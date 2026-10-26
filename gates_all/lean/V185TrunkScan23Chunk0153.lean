import V185TrunkScan23Chunk0152

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_904629 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 6]
def baseStart_904629 : Nat := 118140960795 + 904629 * 2 ^ 59
def prefixEnd_904629 : Nat := 4983230072969 + 3 ^ 40 * 904629 * 2
def baseEnd_904629 : Nat := 51612165666249596508577

theorem tailTrace_904629 : CollatzResearch.WordTrace tailWord_904629 prefixEnd_904629 51612165666249596508577 := by
  unfold tailWord_904629
  simp only [CollatzResearch.WordTrace]
  refine ⟨32994530239691106178068941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21996353493127404118712627 32994530239691106178068941)
  ·
    refine ⟨12372948839884164816775853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32994530239691106178068941 12372948839884164816775853)
    ·
      refine ⟨4639855814956561806290945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12372948839884164816775853 4639855814956561806290945)
      ·
        refine ⟨3479891861217421354718209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4639855814956561806290945 3479891861217421354718209)
        ·
          refine ⟨2609918895913066016038657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3479891861217421354718209 2609918895913066016038657)
          ·
            refine ⟨1957439171934799512028993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2609918895913066016038657 1957439171934799512028993)
            ·
              refine ⟨1468079378951099634021745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957439171934799512028993 1468079378951099634021745)
              ·
                refine ⟨1101059534213324725516309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468079378951099634021745 1101059534213324725516309)
                ·
                  refine ⟨51612165666249596508577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1101059534213324725516309 51612165666249596508577)
                  ·
                    rfl

theorem cell23_904629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_904629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904629 prefixEnd_904629 := by exact prefixLift 904629
  have htrace : WordTrace (prefixWord ++ tailWord_904629) baseStart_904629 baseEnd_904629 := by
    simpa [prefixWord, tailWord_904629, baseEnd_904629] using wordTrace_append hprefix tailTrace_904629
  have hstable : (prefixWord ++ tailWord_904629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904629).length < 2 ^ (prefixWord ++ tailWord_904629).sum := by decide
  have hdescent : baseEnd_904629 < baseStart_904629 := by decide
  rcases family_descends (prefixWord ++ tailWord_904629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904666 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2]
def baseStart_904666 : Nat := 118140960795 + 904666 * 2 ^ 59
def prefixEnd_904666 : Nat := 4983230072969 + 3 ^ 40 * 904666 * 2
def baseEnd_904666 : Nat := 464528489780462723814523

theorem tailTrace_904666 : CollatzResearch.WordTrace tailWord_904666 prefixEnd_904666 464528489780462723814523 := by
  unfold tailWord_904666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8248969935139265374291463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21997253160371374331443901 8248969935139265374291463)
  ·
    refine ⟨12373454902708898061437195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8248969935139265374291463 12373454902708898061437195)
    ·
      refine ⟨18560182354063347092155793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12373454902708898061437195 18560182354063347092155793)
      ·
        refine ⟨13920136765547510319116845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18560182354063347092155793 13920136765547510319116845)
        ·
          refine ⟨5220051287080316369668817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13920136765547510319116845 5220051287080316369668817)
          ·
            refine ⟨3915038465310237277251613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220051287080316369668817 3915038465310237277251613)
            ·
              refine ⟨1468139424491338978969355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915038465310237277251613 1468139424491338978969355)
              ·
                refine ⟨2202209136737008468454033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468139424491338978969355 2202209136737008468454033)
                ·
                  refine ⟨1651656852552756351340525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202209136737008468454033 1651656852552756351340525)
                  ·
                    refine ⟨619371319707283631752697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651656852552756351340525 619371319707283631752697)
                    ·
                      refine ⟨464528489780462723814523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619371319707283631752697 464528489780462723814523)
                      ·
                        rfl

theorem cell23_904666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_904666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904666 prefixEnd_904666 := by exact prefixLift 904666
  have htrace : WordTrace (prefixWord ++ tailWord_904666) baseStart_904666 baseEnd_904666 := by
    simpa [prefixWord, tailWord_904666, baseEnd_904666] using wordTrace_append hprefix tailTrace_904666
  have hstable : (prefixWord ++ tailWord_904666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904666).length < 2 ^ (prefixWord ++ tailWord_904666).sum := by decide
  have hdescent : baseEnd_904666 < baseStart_904666 := by decide
  rcases family_descends (prefixWord ++ tailWord_904666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904673 : List Nat := [1, 2, 3, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_904673 : Nat := 118140960795 + 904673 * 2 ^ 59
def prefixEnd_904673 : Nat := 4983230072969 + 3 ^ 40 * 904673 * 2
def baseEnd_904673 : Nat := 464532084145044196426991

theorem tailTrace_904673 : CollatzResearch.WordTrace tailWord_904673 prefixEnd_904673 464532084145044196426991 := by
  unfold tailWord_904673
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996135051531701692670673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21997423367687801128447115 32996135051531701692670673)
  ·
    refine ⟨24747101288648776269503005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32996135051531701692670673 24747101288648776269503005)
    ·
      refine ⟨9280162983243291101063627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24747101288648776269503005 9280162983243291101063627)
      ·
        refine ⟨13920244474864936651595441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9280162983243291101063627 13920244474864936651595441)
        ·
          refine ⟨10440183356148702488696581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13920244474864936651595441 10440183356148702488696581)
          ·
            refine ⟨1957534379277881716630609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10440183356148702488696581 1957534379277881716630609)
            ·
              refine ⟨1468150784458411287472957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957534379277881716630609 1468150784458411287472957)
              ·
                refine ⟨550556544171904232802359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1468150784458411287472957 550556544171904232802359)
                ·
                  refine ⟨825834816257856349203539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550556544171904232802359 825834816257856349203539)
                  ·
                    refine ⟨1238752224386784523805309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825834816257856349203539 1238752224386784523805309)
                    ·
                      refine ⟨464532084145044196426991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238752224386784523805309 464532084145044196426991)
                      ·
                        rfl

theorem cell23_904673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_904673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904673 prefixEnd_904673 := by exact prefixLift 904673
  have htrace : WordTrace (prefixWord ++ tailWord_904673) baseStart_904673 baseEnd_904673 := by
    simpa [prefixWord, tailWord_904673, baseEnd_904673] using wordTrace_append hprefix tailTrace_904673
  have hstable : (prefixWord ++ tailWord_904673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904673).length < 2 ^ (prefixWord ++ tailWord_904673).sum := by decide
  have hdescent : baseEnd_904673 < baseStart_904673 := by decide
  rcases family_descends (prefixWord ++ tailWord_904673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904689 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 4, 4]
def baseStart_904689 : Nat := 118140960795 + 904689 * 2 ^ 59
def prefixEnd_904689 : Nat := 4983230072969 + 3 ^ 40 * 904689 * 2
def baseEnd_904689 : Nat := 154846766611838711275639

theorem tailTrace_904689 : CollatzResearch.WordTrace tailWord_904689 prefixEnd_904689 154846766611838711275639 := by
  unfold tailWord_904689
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996718619473736425253121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21997812412982490950168747 32996718619473736425253121)
  ·
    refine ⟨24747538964605302318939841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32996718619473736425253121 24747538964605302318939841)
    ·
      refine ⟨18560654223453976739204881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24747538964605302318939841 18560654223453976739204881)
      ·
        refine ⟨13920490667590482554403661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18560654223453976739204881 13920490667590482554403661)
        ·
          refine ⟨5220184000346430957901373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13920490667590482554403661 5220184000346430957901373)
          ·
            refine ⟨1957569000129911609213015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5220184000346430957901373 1957569000129911609213015)
            ·
              refine ⟨2936353500194867413819523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957569000129911609213015 2936353500194867413819523)
              ·
                refine ⟨4404530250292301120729285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936353500194867413819523 4404530250292301120729285)
                ·
                  refine ⟨825849421929806460136741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4404530250292301120729285 825849421929806460136741)
                  ·
                    refine ⟨154846766611838711275639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 825849421929806460136741 154846766611838711275639)
                    ·
                      rfl

theorem cell23_904689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_904689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904689 prefixEnd_904689 := by exact prefixLift 904689
  have htrace : WordTrace (prefixWord ++ tailWord_904689) baseStart_904689 baseEnd_904689 := by
    simpa [prefixWord, tailWord_904689, baseEnd_904689] using wordTrace_append hprefix tailTrace_904689
  have hstable : (prefixWord ++ tailWord_904689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904689).length < 2 ^ (prefixWord ++ tailWord_904689).sum := by decide
  have hdescent : baseEnd_904689 < baseStart_904689 := by decide
  rcases family_descends (prefixWord ++ tailWord_904689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904696 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 3, 2, 2]
def baseStart_904696 : Nat := 118140960795 + 904696 * 2 ^ 59
def prefixEnd_904696 : Nat := 4983230072969 + 3 ^ 40 * 904696 * 2
def baseEnd_904696 : Nat := 464543894200097606439385

theorem tailTrace_904696 : CollatzResearch.WordTrace tailWord_904696 prefixEnd_904696 464543894200097606439385 := by
  unfold tailWord_904696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16498486965224188310378971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21997982620298917747171961 16498486965224188310378971)
  ·
    refine ⟨24747730447836282465568457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16498486965224188310378971 24747730447836282465568457)
    ·
      refine ⟨18560797835877211849176343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24747730447836282465568457 18560797835877211849176343)
      ·
        refine ⟨27841196753815817773764515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18560797835877211849176343 27841196753815817773764515)
        ·
          refine ⟨41761795130723726660646773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27841196753815817773764515 41761795130723726660646773)
          ·
            refine ⟨3915168293505349374435635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41761795130723726660646773 3915168293505349374435635)
            ·
              refine ⟨5872752440258024061653453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915168293505349374435635 5872752440258024061653453)
              ·
                refine ⟨2202282165096759023120045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872752440258024061653453 2202282165096759023120045)
                ·
                  refine ⟨825855811911284633670017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2202282165096759023120045 825855811911284633670017)
                  ·
                    refine ⟨619391858933463475252513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825855811911284633670017 619391858933463475252513)
                    ·
                      refine ⟨464543894200097606439385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619391858933463475252513 464543894200097606439385)
                      ·
                        rfl

theorem cell23_904696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_904696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904696 prefixEnd_904696 := by exact prefixLift 904696
  have htrace : WordTrace (prefixWord ++ tailWord_904696) baseStart_904696 baseEnd_904696 := by
    simpa [prefixWord, tailWord_904696, baseEnd_904696] using wordTrace_append hprefix tailTrace_904696
  have hstable : (prefixWord ++ tailWord_904696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904696).length < 2 ^ (prefixWord ++ tailWord_904696).sum := by decide
  have hdescent : baseEnd_904696 < baseStart_904696 := by decide
  rcases family_descends (prefixWord ++ tailWord_904696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904706 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_904706 : Nat := 118140960795 + 904706 * 2 ^ 59
def prefixEnd_904706 : Nat := 4983230072969 + 3 ^ 40 * 904706 * 2
def baseEnd_904706 : Nat := 154849676335547522438113

theorem tailTrace_904706 : CollatzResearch.WordTrace tailWord_904706 prefixEnd_904706 154849676335547522438113 := by
  unfold tailWord_904706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8249334665103037082155493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21998225773608098885747981 8249334665103037082155493)
  ·
    refine ⟨1546750249706819452904155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8249334665103037082155493 1546750249706819452904155)
    ·
      refine ⟨2320125374560229179356233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546750249706819452904155 2320125374560229179356233)
      ·
        refine ⟨1740094030920171884517175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2320125374560229179356233 1740094030920171884517175)
        ·
          refine ⟨2610141046380257826775763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740094030920171884517175 2610141046380257826775763)
          ·
            refine ⟨3915211569570386740163645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610141046380257826775763 3915211569570386740163645)
            ·
              refine ⟨1468204338588895027561367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915211569570386740163645 1468204338588895027561367)
              ·
                refine ⟨2202306507883342541342051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468204338588895027561367 2202306507883342541342051)
                ·
                  refine ⟨3303459761825013812013077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202306507883342541342051 3303459761825013812013077)
                  ·
                    refine ⟨154849676335547522438113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3303459761825013812013077 154849676335547522438113)
                    ·
                      rfl

theorem cell23_904706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_904706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904706 prefixEnd_904706 := by exact prefixLift 904706
  have htrace : WordTrace (prefixWord ++ tailWord_904706) baseStart_904706 baseEnd_904706 := by
    simpa [prefixWord, tailWord_904706, baseEnd_904706] using wordTrace_append hprefix tailTrace_904706
  have hstable : (prefixWord ++ tailWord_904706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904706).length < 2 ^ (prefixWord ++ tailWord_904706).sum := by decide
  have hdescent : baseEnd_904706 < baseStart_904706 := by decide
  rcases family_descends (prefixWord ++ tailWord_904706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904724 : List Nat := [2, 4, 3, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_904724 : Nat := 118140960795 + 904724 * 2 ^ 59
def prefixEnd_904724 : Nat := 4983230072969 + 3 ^ 40 * 904724 * 2
def baseEnd_904724 : Nat := 464558271658423496889257

theorem tailTrace_904724 : CollatzResearch.WordTrace tailWord_904724 prefixEnd_904724 464558271658423496889257 := by
  unfold tailWord_904724
  simp only [CollatzResearch.WordTrace]
  refine ⟨16498997587173468701388613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21998663449564624935184817 16498997587173468701388613)
  ·
    refine ⟨3093562047595025381510365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16498997587173468701388613 3093562047595025381510365)
    ·
      refine ⟨1160085767848134518066387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3093562047595025381510365 1160085767848134518066387)
      ·
        refine ⟨1740128651772201777099581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160085767848134518066387 1740128651772201777099581)
        ·
          refine ⟨652548244414575666412343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1740128651772201777099581 652548244414575666412343)
          ·
            refine ⟨978822366621863499618515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652548244414575666412343 978822366621863499618515)
            ·
              refine ⟨1468233549932795249427773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978822366621863499618515 1468233549932795249427773)
              ·
                refine ⟨550587581224798218535415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1468233549932795249427773 550587581224798218535415)
                ·
                  refine ⟨825881371837197327803123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550587581224798218535415 825881371837197327803123)
                  ·
                    refine ⟨1238822057755795991704685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825881371837197327803123 1238822057755795991704685)
                    ·
                      refine ⟨464558271658423496889257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238822057755795991704685 464558271658423496889257)
                      ·
                        rfl

theorem cell23_904724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_904724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904724 prefixEnd_904724 := by exact prefixLift 904724
  have htrace : WordTrace (prefixWord ++ tailWord_904724) baseStart_904724 baseEnd_904724 := by
    simpa [prefixWord, tailWord_904724, baseEnd_904724] using wordTrace_append hprefix tailTrace_904724
  have hstable : (prefixWord ++ tailWord_904724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904724).length < 2 ^ (prefixWord ++ tailWord_904724).sum := by decide
  have hdescent : baseEnd_904724 < baseStart_904724 := by decide
  rcases family_descends (prefixWord ++ tailWord_904724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904746 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_904746 : Nat := 118140960795 + 904746 * 2 ^ 59
def prefixEnd_904746 : Nat := 4983230072969 + 3 ^ 40 * 904746 * 2
def baseEnd_904746 : Nat := 464569568232822410814155

theorem tailTrace_904746 : CollatzResearch.WordTrace tailWord_904746 prefixEnd_904746 464569568232822410814155 := by
  unfold tailWord_904746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8249699395066808790019523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21999198386844823440052061 8249699395066808790019523)
  ·
    refine ⟨12374549092600213185029285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8249699395066808790019523 12374549092600213185029285)
    ·
      refine ⟨2320227954862539972192991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12374549092600213185029285 2320227954862539972192991)
      ·
        refine ⟨3480341932293809958289487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320227954862539972192991 3480341932293809958289487)
        ·
          refine ⟨5220512898440714937434231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480341932293809958289487 5220512898440714937434231)
          ·
            refine ⟨7830769347661072406151347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220512898440714937434231 7830769347661072406151347)
            ·
              refine ⟨11746154021491608609227021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830769347661072406151347 11746154021491608609227021)
              ·
                refine ⟨4404807758059353228460133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11746154021491608609227021 4404807758059353228460133)
                ·
                  refine ⟨825901454636128730336275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4404807758059353228460133 825901454636128730336275)
                  ·
                    refine ⟨1238852181954193095504413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825901454636128730336275 1238852181954193095504413)
                    ·
                      refine ⟨464569568232822410814155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238852181954193095504413 464569568232822410814155)
                      ·
                        rfl

theorem cell23_904746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_904746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904746 prefixEnd_904746 := by exact prefixLift 904746
  have htrace : WordTrace (prefixWord ++ tailWord_904746) baseStart_904746 baseEnd_904746 := by
    simpa [prefixWord, tailWord_904746, baseEnd_904746] using wordTrace_append hprefix tailTrace_904746
  have hstable : (prefixWord ++ tailWord_904746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904746).length < 2 ^ (prefixWord ++ tailWord_904746).sum := by decide
  have hdescent : baseEnd_904746 < baseStart_904746 := by decide
  rcases family_descends (prefixWord ++ tailWord_904746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904752 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_904752 : Nat := 118140960795 + 904752 * 2 ^ 59
def prefixEnd_904752 : Nat := 4983230072969 + 3 ^ 40 * 904752 * 2
def baseEnd_904752 : Nat := 464572649116749387339127

theorem tailTrace_904752 : CollatzResearch.WordTrace tailWord_904752 prefixEnd_904752 464572649116749387339127 := by
  unfold tailWord_904752
  simp only [CollatzResearch.WordTrace]
  refine ⟨16499508209122749092398255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21999344278830332123197673 16499508209122749092398255)
  ·
    refine ⟨24749262313684123638597383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16499508209122749092398255 24749262313684123638597383)
    ·
      refine ⟨37123893470526185457896075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24749262313684123638597383 37123893470526185457896075)
      ·
        refine ⟨55685840205789278186844113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37123893470526185457896075 55685840205789278186844113)
        ·
          refine ⟨41764380154341958640133085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55685840205789278186844113 41764380154341958640133085)
          ·
            refine ⟨15661642557878234490049907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41764380154341958640133085 15661642557878234490049907)
            ·
              refine ⟨23492463836817351735074861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15661642557878234490049907 23492463836817351735074861)
              ·
                refine ⟨8809673938806506900653073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23492463836817351735074861 8809673938806506900653073)
                ·
                  refine ⟨6607255454104880175489805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8809673938806506900653073 6607255454104880175489805)
                  ·
                    refine ⟨2477720795289330065808677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6607255454104880175489805 2477720795289330065808677)
                    ·
                      refine ⟨464572649116749387339127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2477720795289330065808677 464572649116749387339127)
                      ·
                        rfl

theorem cell23_904752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_904752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904752 prefixEnd_904752 := by exact prefixLift 904752
  have htrace : WordTrace (prefixWord ++ tailWord_904752) baseStart_904752 baseEnd_904752 := by
    simpa [prefixWord, tailWord_904752, baseEnd_904752] using wordTrace_append hprefix tailTrace_904752
  have hstable : (prefixWord ++ tailWord_904752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904752).length < 2 ^ (prefixWord ++ tailWord_904752).sum := by decide
  have hdescent : baseEnd_904752 < baseStart_904752 := by decide
  rcases family_descends (prefixWord ++ tailWord_904752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904762 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_904762 : Nat := 118140960795 + 904762 * 2 ^ 59
def prefixEnd_904762 : Nat := 4983230072969 + 3 ^ 40 * 904762 * 2
def baseEnd_904762 : Nat := 154859261307764782738027

theorem tailTrace_904762 : CollatzResearch.WordTrace tailWord_904762 prefixEnd_904762 154859261307764782738027 := by
  unfold tailWord_904762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8249845287052317473165135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21999587432139513261773693 8249845287052317473165135)
  ·
    refine ⟨12374767930578476209747703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8249845287052317473165135 12374767930578476209747703)
    ·
      refine ⟨18562151895867714314621555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12374767930578476209747703 18562151895867714314621555)
      ·
        refine ⟨27843227843801571471932333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18562151895867714314621555 27843227843801571471932333)
        ·
          refine ⟨10441210441425589301974625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27843227843801571471932333 10441210441425589301974625)
          ·
            refine ⟨7830907831069191976480969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10441210441425589301974625 7830907831069191976480969)
            ·
              refine ⟨5873180873301893982360727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7830907831069191976480969 5873180873301893982360727)
              ·
                refine ⟨8809771309952840973541091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873180873301893982360727 8809771309952840973541091)
                ·
                  refine ⟨13214656964929261460311637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8809771309952840973541091 13214656964929261460311637)
                  ·
                    refine ⟨154859261307764782738027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13214656964929261460311637 154859261307764782738027)
                    ·
                      rfl

theorem cell23_904762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_904762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904762 prefixEnd_904762 := by exact prefixLift 904762
  have htrace : WordTrace (prefixWord ++ tailWord_904762) baseStart_904762 baseEnd_904762 := by
    simpa [prefixWord, tailWord_904762, baseEnd_904762] using wordTrace_append hprefix tailTrace_904762
  have hstable : (prefixWord ++ tailWord_904762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904762).length < 2 ^ (prefixWord ++ tailWord_904762).sum := by decide
  have hdescent : baseEnd_904762 < baseStart_904762 := by decide
  rcases family_descends (prefixWord ++ tailWord_904762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904786 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_904786 : Nat := 118140960795 + 904786 * 2 ^ 59
def prefixEnd_904786 : Nat := 4983230072969 + 3 ^ 40 * 904786 * 2
def baseEnd_904786 : Nat := 464590107459002254313971

theorem tailTrace_904786 : CollatzResearch.WordTrace tailWord_904786 prefixEnd_904786 464590107459002254313971 := by
  unfold tailWord_904786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250064125030580497883553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22000171000081547994356141 8250064125030580497883553)
  ·
    refine ⟨6187548093772935373412665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8250064125030580497883553 6187548093772935373412665)
    ·
      refine ⟨4640661070329701530059499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6187548093772935373412665 4640661070329701530059499)
      ·
        refine ⟨6960991605494552295089249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4640661070329701530059499 6960991605494552295089249)
        ·
          refine ⟨5220743704120914221316937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6960991605494552295089249 5220743704120914221316937)
          ·
            refine ⟨3915557778090685665987703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220743704120914221316937 3915557778090685665987703)
            ·
              refine ⟨5873336667136028498981555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915557778090685665987703 5873336667136028498981555)
              ·
                refine ⟨8810005000704042748472333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873336667136028498981555 8810005000704042748472333)
                ·
                  refine ⟨3303751875264016030677125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8810005000704042748472333 3303751875264016030677125)
                  ·
                    refine ⟨619453476612003005751961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303751875264016030677125 619453476612003005751961)
                    ·
                      refine ⟨464590107459002254313971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619453476612003005751961 464590107459002254313971)
                      ·
                        rfl

theorem cell23_904786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_904786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904786 prefixEnd_904786 := by exact prefixLift 904786
  have htrace : WordTrace (prefixWord ++ tailWord_904786) baseStart_904786 baseEnd_904786 := by
    simpa [prefixWord, tailWord_904786, baseEnd_904786] using wordTrace_append hprefix tailTrace_904786
  have hstable : (prefixWord ++ tailWord_904786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904786).length < 2 ^ (prefixWord ++ tailWord_904786).sum := by decide
  have hdescent : baseEnd_904786 < baseStart_904786 := by decide
  rcases family_descends (prefixWord ++ tailWord_904786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904797 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_904797 : Nat := 118140960795 + 904797 * 2 ^ 59
def prefixEnd_904797 : Nat := 4983230072969 + 3 ^ 40 * 904797 * 2
def baseEnd_904797 : Nat := 464595755746201711276421

theorem tailTrace_904797 : CollatzResearch.WordTrace tailWord_904797 prefixEnd_904797 464595755746201711276421 := by
  unfold tailWord_904797
  simp only [CollatzResearch.WordTrace]
  refine ⟨33000657703082470870184645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22000438468721647246789763 33000657703082470870184645)
  ·
    refine ⟨6187623319327963288159621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33000657703082470870184645 6187623319327963288159621)
    ·
      refine ⟨1160179372373993116529929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6187623319327963288159621 1160179372373993116529929)
      ·
        refine ⟨870134529280494837397447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1160179372373993116529929 870134529280494837397447)
        ·
          refine ⟨1305201793920742256096171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870134529280494837397447 1305201793920742256096171)
          ·
            refine ⟨1957802690881113384144257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305201793920742256096171 1957802690881113384144257)
            ·
              refine ⟨1468352018160835038108193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957802690881113384144257 1468352018160835038108193)
              ·
                refine ⟨1101264013620626278581145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468352018160835038108193 1101264013620626278581145)
                ·
                  refine ⟨825948010215469708935859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1101264013620626278581145 825948010215469708935859)
                  ·
                    refine ⟨1238922015323204563403789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825948010215469708935859 1238922015323204563403789)
                    ·
                      refine ⟨464595755746201711276421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238922015323204563403789 464595755746201711276421)
                      ·
                        rfl

theorem cell23_904797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_904797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904797 prefixEnd_904797 := by exact prefixLift 904797
  have htrace : WordTrace (prefixWord ++ tailWord_904797) baseStart_904797 baseEnd_904797 := by
    simpa [prefixWord, tailWord_904797, baseEnd_904797] using wordTrace_append hprefix tailTrace_904797
  have hstable : (prefixWord ++ tailWord_904797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904797).length < 2 ^ (prefixWord ++ tailWord_904797).sum := by decide
  have hdescent : baseEnd_904797 < baseStart_904797 := by decide
  rcases family_descends (prefixWord ++ tailWord_904797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904803 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 2, 2, 2]
def baseStart_904803 : Nat := 118140960795 + 904803 * 2 ^ 59
def prefixEnd_904803 : Nat := 4983230072969 + 3 ^ 40 * 904803 * 2
def baseEnd_904803 : Nat := 464598836630128687801393

theorem tailTrace_904803 : CollatzResearch.WordTrace tailWord_904803 prefixEnd_904803 464598836630128687801393 := by
  unfold tailWord_904803
  simp only [CollatzResearch.WordTrace]
  refine ⟨33000876541060733894903063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22000584360707155929935375 33000876541060733894903063)
  ·
    refine ⟨49501314811591100842354595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33000876541060733894903063 49501314811591100842354595)
    ·
      refine ⟨74251972217386651263531893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49501314811591100842354595 74251972217386651263531893)
      ·
        refine ⟨6961122395379998555956115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74251972217386651263531893 6961122395379998555956115)
        ·
          refine ⟨10441683593069997833934173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961122395379998555956115 10441683593069997833934173)
          ·
            refine ⟨3915631347401249187725315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10441683593069997833934173 3915631347401249187725315)
            ·
              refine ⟨5873447021101873781587973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915631347401249187725315 5873447021101873781587973)
              ·
                refine ⟨1101271316456601334047745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5873447021101873781587973 1101271316456601334047745)
                ·
                  refine ⟨825953487342451000535809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1101271316456601334047745 825953487342451000535809)
                  ·
                    refine ⟨619465115506838250401857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825953487342451000535809 619465115506838250401857)
                    ·
                      refine ⟨464598836630128687801393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619465115506838250401857 464598836630128687801393)
                      ·
                        rfl

theorem cell23_904803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_904803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904803 prefixEnd_904803 := by exact prefixLift 904803
  have htrace : WordTrace (prefixWord ++ tailWord_904803) baseStart_904803 baseEnd_904803 := by
    simpa [prefixWord, tailWord_904803, baseEnd_904803] using wordTrace_append hprefix tailTrace_904803
  have hstable : (prefixWord ++ tailWord_904803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904803).length < 2 ^ (prefixWord ++ tailWord_904803).sum := by decide
  have hdescent : baseEnd_904803 < baseStart_904803 := by decide
  rcases family_descends (prefixWord ++ tailWord_904803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904812 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_904812 : Nat := 118140960795 + 904812 * 2 ^ 59
def prefixEnd_904812 : Nat := 4983230072969 + 3 ^ 40 * 904812 * 2
def baseEnd_904812 : Nat := 464603457956019152588851

theorem tailTrace_904812 : CollatzResearch.WordTrace tailWord_904812 prefixEnd_904812 464603457956019152588851 := by
  unfold tailWord_904812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500602399014064215990345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22000803198685418954653793 16500602399014064215990345)
  ·
    refine ⟨12375451799260548161992759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16500602399014064215990345 12375451799260548161992759)
    ·
      refine ⟨18563177698890822242989139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12375451799260548161992759 18563177698890822242989139)
      ·
        refine ⟨27844766548336233364483709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18563177698890822242989139 27844766548336233364483709)
        ·
          refine ⟨10441787455626087511681391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27844766548336233364483709 10441787455626087511681391)
          ·
            refine ⟨15662681183439131267522087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10441787455626087511681391 15662681183439131267522087)
            ·
              refine ⟨23494021775158696901283131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15662681183439131267522087 23494021775158696901283131)
              ·
                refine ⟨35241032662738045351924697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23494021775158696901283131 35241032662738045351924697)
                ·
                  refine ⟨26430774497053534013943523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35241032662738045351924697 26430774497053534013943523)
                  ·
                    refine ⟨39646161745580301020915285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26430774497053534013943523 39646161745580301020915285)
                    ·
                      refine ⟨464603457956019152588851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39646161745580301020915285 464603457956019152588851)
                      ·
                        rfl

theorem cell23_904812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_904812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904812 prefixEnd_904812 := by exact prefixLift 904812
  have htrace : WordTrace (prefixWord ++ tailWord_904812) baseStart_904812 baseEnd_904812 := by
    simpa [prefixWord, tailWord_904812, baseEnd_904812] using wordTrace_append hprefix tailTrace_904812
  have hstable : (prefixWord ++ tailWord_904812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904812).length < 2 ^ (prefixWord ++ tailWord_904812).sum := by decide
  have hdescent : baseEnd_904812 < baseStart_904812 := by decide
  rcases family_descends (prefixWord ++ tailWord_904812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904839 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 1, 7]
def baseStart_904839 : Nat := 118140960795 + 904839 * 2 ^ 59
def prefixEnd_904839 : Nat := 4983230072969 + 3 ^ 40 * 904839 * 2
def baseEnd_904839 : Nat := 154872440644563515650409

theorem tailTrace_904839 : CollatzResearch.WordTrace tailWord_904839 prefixEnd_904839 154872440644563515650409 := by
  unfold tailWord_904839
  simp only [CollatzResearch.WordTrace]
  refine ⟨33002189568930312043213571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22001459712620208028809047 33002189568930312043213571)
  ·
    refine ⟨49503284353395468064820357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33002189568930312043213571 49503284353395468064820357)
    ·
      refine ⟨9281865816261650262153817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49503284353395468064820357 9281865816261650262153817)
      ·
        refine ⟨6961399362196237696615363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9281865816261650262153817 6961399362196237696615363)
        ·
          refine ⟨10442099043294356544923045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961399362196237696615363 10442099043294356544923045)
          ·
            refine ⟨1957893570617691852173071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10442099043294356544923045 1957893570617691852173071)
            ·
              refine ⟨2936840355926537778259607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957893570617691852173071 2936840355926537778259607)
              ·
                refine ⟨4405260533889806667389411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936840355926537778259607 4405260533889806667389411)
                ·
                  refine ⟨6607890800834710001084117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405260533889806667389411 6607890800834710001084117)
                  ·
                    refine ⟨154872440644563515650409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6607890800834710001084117 154872440644563515650409)
                    ·
                      rfl

theorem cell23_904839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_904839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904839 prefixEnd_904839 := by exact prefixLift 904839
  have htrace : WordTrace (prefixWord ++ tailWord_904839) baseStart_904839 baseEnd_904839 := by
    simpa [prefixWord, tailWord_904839, baseEnd_904839] using wordTrace_append hprefix tailTrace_904839
  have hstable : (prefixWord ++ tailWord_904839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904839).length < 2 ^ (prefixWord ++ tailWord_904839).sum := by decide
  have hdescent : baseEnd_904839 < baseStart_904839 := by decide
  rcases family_descends (prefixWord ++ tailWord_904839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904879 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 3]
def baseStart_904879 : Nat := 118140960795 + 904879 * 2 ^ 59
def prefixEnd_904879 : Nat := 4983230072969 + 3 ^ 40 * 904879 * 2
def baseEnd_904879 : Nat := 464637861159870390451043

theorem tailTrace_904879 : CollatzResearch.WordTrace tailWord_904879 prefixEnd_904879 464637861159870390451043 := by
  unfold tailWord_904879
  simp only [CollatzResearch.WordTrace]
  refine ⟨33003648488785398874669691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22002432325856932583113127 33003648488785398874669691)
  ·
    refine ⟨49505472733178098312004537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33003648488785398874669691 49505472733178098312004537)
    ·
      refine ⟨37129104549883573734003403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49505472733178098312004537 37129104549883573734003403)
      ·
        refine ⟨55693656824825360601005105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37129104549883573734003403 55693656824825360601005105)
        ·
          refine ⟨41770242618619020450753829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55693656824825360601005105 41770242618619020450753829)
          ·
            refine ⟨7831920490991066334516343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41770242618619020450753829 7831920490991066334516343)
            ·
              refine ⟨11747880736486599501774515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831920490991066334516343 11747880736486599501774515)
              ·
                refine ⟨17621821104729899252661773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11747880736486599501774515 17621821104729899252661773)
                ·
                  refine ⟨6608182914273712219748165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17621821104729899252661773 6608182914273712219748165)
                  ·
                    refine ⟨1239034296426321041202781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6608182914273712219748165 1239034296426321041202781)
                    ·
                      refine ⟨464637861159870390451043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1239034296426321041202781 464637861159870390451043)
                      ·
                        rfl

theorem cell23_904879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_904879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904879 prefixEnd_904879 := by exact prefixLift 904879
  have htrace : WordTrace (prefixWord ++ tailWord_904879) baseStart_904879 baseEnd_904879 := by
    simpa [prefixWord, tailWord_904879, baseEnd_904879] using wordTrace_append hprefix tailTrace_904879
  have hstable : (prefixWord ++ tailWord_904879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904879).length < 2 ^ (prefixWord ++ tailWord_904879).sum := by decide
  have hdescent : baseEnd_904879 < baseStart_904879 := by decide
  rcases family_descends (prefixWord ++ tailWord_904879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904896 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3]
def baseStart_904896 : Nat := 118140960795 + 904896 * 2 ^ 59
def prefixEnd_904896 : Nat := 4983230072969 + 3 ^ 40 * 904896 * 2
def baseEnd_904896 : Nat := 464646590330996823938465

theorem tailTrace_904896 : CollatzResearch.WordTrace tailWord_904896 prefixEnd_904896 464646590330996823938465 := by
  unfold tailWord_904896
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502134264861905389019271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22002845686482540518692361 16502134264861905389019271)
  ·
    refine ⟨24753201397292858083528907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16502134264861905389019271 24753201397292858083528907)
    ·
      refine ⟨37129802095939287125293361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24753201397292858083528907 37129802095939287125293361)
      ·
        refine ⟨27847351571954465343970021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37129802095939287125293361 27847351571954465343970021)
        ·
          refine ⟨5221378419741462251994379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27847351571954465343970021 5221378419741462251994379)
          ·
            refine ⟨7832067629612193377991569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221378419741462251994379 7832067629612193377991569)
            ·
              refine ⟨5874050722209145033493677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7832067629612193377991569 5874050722209145033493677)
              ·
                refine ⟨2202769020828429387560129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5874050722209145033493677 2202769020828429387560129)
                ·
                  refine ⟨1652076765621322040670097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202769020828429387560129 1652076765621322040670097)
                  ·
                    refine ⟨1239057574215991530502573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1652076765621322040670097 1239057574215991530502573)
                    ·
                      refine ⟨464646590330996823938465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1239057574215991530502573 464646590330996823938465)
                      ·
                        rfl

theorem cell23_904896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_904896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904896 prefixEnd_904896 := by exact prefixLift 904896
  have htrace : WordTrace (prefixWord ++ tailWord_904896) baseStart_904896 baseEnd_904896 := by
    simpa [prefixWord, tailWord_904896, baseEnd_904896] using wordTrace_append hprefix tailTrace_904896
  have hstable : (prefixWord ++ tailWord_904896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904896).length < 2 ^ (prefixWord ++ tailWord_904896).sum := by decide
  have hdescent : baseEnd_904896 < baseStart_904896 := by decide
  rcases family_descends (prefixWord ++ tailWord_904896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904916 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 8]
def baseStart_904916 : Nat := 118140960795 + 904916 * 2 ^ 59
def prefixEnd_904916 : Nat := 4983230072969 + 3 ^ 40 * 904916 * 2
def baseEnd_904916 : Nat := 51628539993787416187597

theorem tailTrace_904916 : CollatzResearch.WordTrace tailWord_904916 prefixEnd_904916 51628539993787416187597 := by
  unfold tailWord_904916
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502498994825677096883301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22003331993100902795844401 16502498994825677096883301)
  ·
    refine ⟨3094218561529814455665619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16502498994825677096883301 3094218561529814455665619)
    ·
      refine ⟨4641327842294721683498429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094218561529814455665619 4641327842294721683498429)
      ·
        refine ⟨1740497940860520631311911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4641327842294721683498429 1740497940860520631311911)
        ·
          refine ⟨2610746911290780946967867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740497940860520631311911 2610746911290780946967867)
          ·
            refine ⟨3916120366936171420451801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610746911290780946967867 3916120366936171420451801)
            ·
              refine ⟨2937090275202128565338851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916120366936171420451801 2937090275202128565338851)
              ·
                refine ⟨4405635412803192848008277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937090275202128565338851 4405635412803192848008277)
                ·
                  refine ⟨51628539993787416187597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4405635412803192848008277 51628539993787416187597)
                  ·
                    rfl

theorem cell23_904916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_904916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904916 prefixEnd_904916 := by exact prefixLift 904916
  have htrace : WordTrace (prefixWord ++ tailWord_904916) baseStart_904916 baseEnd_904916 := by
    simpa [prefixWord, tailWord_904916, baseEnd_904916] using wordTrace_append hprefix tailTrace_904916
  have hstable : (prefixWord ++ tailWord_904916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904916).length < 2 ^ (prefixWord ++ tailWord_904916).sum := by decide
  have hdescent : baseEnd_904916 < baseStart_904916 := by decide
  rcases family_descends (prefixWord ++ tailWord_904916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904920 : List Nat := [2, 1, 2, 2, 3, 1, 5, 2, 1, 4]
def baseStart_904920 : Nat := 118140960795 + 904920 * 2 ^ 59
def prefixEnd_904920 : Nat := 4983230072969 + 3 ^ 40 * 904920 * 2
def baseEnd_904920 : Nat := 154886304622234910012785

theorem tailTrace_904920 : CollatzResearch.WordTrace tailWord_904920 prefixEnd_904920 154886304622234910012785 := by
  unfold tailWord_904920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502571940818431438456107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22003429254424575251274809 16502571940818431438456107)
  ·
    refine ⟨24753857911227647157684161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16502571940818431438456107 24753857911227647157684161)
    ·
      refine ⟨18565393433420735368263121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24753857911227647157684161 18565393433420735368263121)
      ·
        refine ⟨13924045075065551526197341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18565393433420735368263121 13924045075065551526197341)
        ·
          refine ⟨5221516903149581822324003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13924045075065551526197341 5221516903149581822324003)
          ·
            refine ⟨7832275354724372733486005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221516903149581822324003 7832275354724372733486005)
            ·
              refine ⟨734275814505409943764313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7832275354724372733486005 734275814505409943764313)
              ·
                refine ⟨550706860879057457823235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734275814505409943764313 550706860879057457823235)
                ·
                  refine ⟨826060291318586186734853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550706860879057457823235 826060291318586186734853)
                  ·
                    refine ⟨154886304622234910012785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 826060291318586186734853 154886304622234910012785)
                    ·
                      rfl

theorem cell23_904920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_904920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904920 prefixEnd_904920 := by exact prefixLift 904920
  have htrace : WordTrace (prefixWord ++ tailWord_904920) baseStart_904920 baseEnd_904920 := by
    simpa [prefixWord, tailWord_904920, baseEnd_904920] using wordTrace_append hprefix tailTrace_904920
  have hstable : (prefixWord ++ tailWord_904920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904920).length < 2 ^ (prefixWord ++ tailWord_904920).sum := by decide
  have hdescent : baseEnd_904920 < baseStart_904920 := by decide
  rcases family_descends (prefixWord ++ tailWord_904920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904946 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_904946 : Nat := 118140960795 + 904946 * 2 ^ 59
def prefixEnd_904946 : Nat := 4983230072969 + 3 ^ 40 * 904946 * 2
def baseEnd_904946 : Nat := 154890754787907209437745

theorem tailTrace_904946 : CollatzResearch.WordTrace tailWord_904946 prefixEnd_904946 154890754787907209437745 := by
  unfold tailWord_904946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251523044885667329339673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22004061453028446211572461 8251523044885667329339673)
  ·
    refine ⟨6188642283664250497004755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8251523044885667329339673 6188642283664250497004755)
    ·
      refine ⟨9282963425496375745507133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188642283664250497004755 9282963425496375745507133)
      ·
        refine ⟨3481111284561140904565175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9282963425496375745507133 3481111284561140904565175)
        ·
          refine ⟨5221666926841711356847763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481111284561140904565175 5221666926841711356847763)
          ·
            refine ⟨7832500390262567035271645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221666926841711356847763 7832500390262567035271645)
            ·
              refine ⟨2937187646348462638226867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7832500390262567035271645 2937187646348462638226867)
              ·
                refine ⟨4405781469522693957340301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937187646348462638226867 4405781469522693957340301)
                ·
                  refine ⟨1652168051071010234002613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4405781469522693957340301 1652168051071010234002613)
                  ·
                    refine ⟨154890754787907209437745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1652168051071010234002613 154890754787907209437745)
                    ·
                      rfl

theorem cell23_904946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_904946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904946 prefixEnd_904946 := by exact prefixLift 904946
  have htrace : WordTrace (prefixWord ++ tailWord_904946) baseStart_904946 baseEnd_904946 := by
    simpa [prefixWord, tailWord_904946, baseEnd_904946] using wordTrace_append hprefix tailTrace_904946
  have hstable : (prefixWord ++ tailWord_904946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904946).length < 2 ^ (prefixWord ++ tailWord_904946).sum := by decide
  have hdescent : baseEnd_904946 < baseStart_904946 := by decide
  rcases family_descends (prefixWord ++ tailWord_904946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904959 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 3, 6]
def baseStart_904959 : Nat := 118140960795 + 904959 * 2 ^ 59
def prefixEnd_904959 : Nat := 4983230072969 + 3 ^ 40 * 904959 * 2
def baseEnd_904959 : Nat := 154892979870743359150225

theorem tailTrace_904959 : CollatzResearch.WordTrace tailWord_904959 prefixEnd_904959 154892979870743359150225 := by
  unfold tailWord_904959
  simp only [CollatzResearch.WordTrace]
  refine ⟨33006566328495572537581931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22004377552330381691721287 33006566328495572537581931)
  ·
    refine ⟨49509849492743358806372897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33006566328495572537581931 49509849492743358806372897)
    ·
      refine ⟨37132387119557519104779673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49509849492743358806372897 37132387119557519104779673)
      ·
        refine ⟨27849290339668139328584755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37132387119557519104779673 27849290339668139328584755)
        ·
          refine ⟨41773935509502208992877133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27849290339668139328584755 41773935509502208992877133)
          ·
            refine ⟨15665225816063328372328925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41773935509502208992877133 15665225816063328372328925)
            ·
              refine ⟨5874459681023748139623347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15665225816063328372328925 5874459681023748139623347)
              ·
                refine ⟨8811689521535622209435021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874459681023748139623347 8811689521535622209435021)
                ·
                  refine ⟨3304383570575858328538133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8811689521535622209435021 3304383570575858328538133)
                  ·
                    refine ⟨154892979870743359150225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3304383570575858328538133 154892979870743359150225)
                    ·
                      rfl

theorem cell23_904959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_904959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904959 prefixEnd_904959 := by exact prefixLift 904959
  have htrace : WordTrace (prefixWord ++ tailWord_904959) baseStart_904959 baseEnd_904959 := by
    simpa [prefixWord, tailWord_904959, baseEnd_904959] using wordTrace_append hprefix tailTrace_904959
  have hstable : (prefixWord ++ tailWord_904959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904959).length < 2 ^ (prefixWord ++ tailWord_904959).sum := by decide
  have hdescent : baseEnd_904959 < baseStart_904959 := by decide
  rcases family_descends (prefixWord ++ tailWord_904959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904979 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6]
def baseStart_904979 : Nat := 118140960795 + 904979 * 2 ^ 59
def prefixEnd_904979 : Nat := 4983230072969 + 3 ^ 40 * 904979 * 2
def baseEnd_904979 : Nat := 464689209225319999200583

theorem tailTrace_904979 : CollatzResearch.WordTrace tailWord_904979 prefixEnd_904979 464689209225319999200583 := by
  unfold tailWord_904979
  simp only [CollatzResearch.WordTrace]
  refine ⟨33007295788423115953309991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22004863858948743968873327 33007295788423115953309991)
  ·
    refine ⟨49510943682634673929964987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33007295788423115953309991 49510943682634673929964987)
    ·
      refine ⟨74266415523952010894947481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49510943682634673929964987 74266415523952010894947481)
      ·
        refine ⟨55699811642964008171210611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74266415523952010894947481 55699811642964008171210611)
        ·
          refine ⟨83549717464446012256815917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55699811642964008171210611 83549717464446012256815917)
          ·
            refine ⟨31331144049167254596305969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83549717464446012256815917 31331144049167254596305969)
            ·
              refine ⟨23498358036875440947229477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31331144049167254596305969 23498358036875440947229477)
              ·
                refine ⟨4405942131914145177605527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23498358036875440947229477 4405942131914145177605527)
                ·
                  refine ⟨6608913197871217766408291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405942131914145177605527 6608913197871217766408291)
                  ·
                    refine ⟨9913369796806826649612437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608913197871217766408291 9913369796806826649612437)
                    ·
                      refine ⟨464689209225319999200583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9913369796806826649612437 464689209225319999200583)
                      ·
                        rfl

theorem cell23_904979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_904979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904979 prefixEnd_904979 := by exact prefixLift 904979
  have htrace : WordTrace (prefixWord ++ tailWord_904979) baseStart_904979 baseEnd_904979 := by
    simpa [prefixWord, tailWord_904979, baseEnd_904979] using wordTrace_append hprefix tailTrace_904979
  have hstable : (prefixWord ++ tailWord_904979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904979).length < 2 ^ (prefixWord ++ tailWord_904979).sum := by decide
  have hdescent : baseEnd_904979 < baseStart_904979 := by decide
  rcases family_descends (prefixWord ++ tailWord_904979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904993 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 2, 4]
def baseStart_904993 : Nat := 118140960795 + 904993 * 2 ^ 59
def prefixEnd_904993 : Nat := 4983230072969 + 3 ^ 40 * 904993 * 2
def baseEnd_904993 : Nat := 154898799318160981475173

theorem tailTrace_904993 : CollatzResearch.WordTrace tailWord_904993 prefixEnd_904993 154898799318160981475173 := by
  unfold tailWord_904993
  simp only [CollatzResearch.WordTrace]
  refine ⟨33007806410372396344319633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22005204273581597562879755 33007806410372396344319633)
  ·
    refine ⟨24755854807779297258239725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33007806410372396344319633 24755854807779297258239725)
    ·
      refine ⟨9283445552917236471839897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24755854807779297258239725 9283445552917236471839897)
      ·
        refine ⟨6962584164687927353879923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9283445552917236471839897 6962584164687927353879923)
        ·
          refine ⟨10443876247031891030819885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962584164687927353879923 10443876247031891030819885)
          ·
            refine ⟨3916453592636959136557457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10443876247031891030819885 3916453592636959136557457)
            ·
              refine ⟨2937340194477719352418093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916453592636959136557457 2937340194477719352418093)
              ·
                refine ⟨1101502572929144757156785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2937340194477719352418093 1101502572929144757156785)
                ·
                  refine ⟨826126929696858567867589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1101502572929144757156785 826126929696858567867589)
                  ·
                    refine ⟨154898799318160981475173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 826126929696858567867589 154898799318160981475173)
                    ·
                      rfl

theorem cell23_904993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_904993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904993 prefixEnd_904993 := by exact prefixLift 904993
  have htrace : WordTrace (prefixWord ++ tailWord_904993) baseStart_904993 baseEnd_904993 := by
    simpa [prefixWord, tailWord_904993, baseEnd_904993] using wordTrace_append hprefix tailTrace_904993
  have hstable : (prefixWord ++ tailWord_904993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904993).length < 2 ^ (prefixWord ++ tailWord_904993).sum := by decide
  have hdescent : baseEnd_904993 < baseStart_904993 := by decide
  rcases family_descends (prefixWord ++ tailWord_904993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905000 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_905000 : Nat := 118140960795 + 905000 * 2 ^ 59
def prefixEnd_905000 : Nat := 4983230072969 + 3 ^ 40 * 905000 * 2
def baseEnd_905000 : Nat := 464699992319064417037987

theorem tailTrace_905000 : CollatzResearch.WordTrace tailWord_905000 prefixEnd_905000 464699992319064417037987 := by
  unfold tailWord_905000
  simp only [CollatzResearch.WordTrace]
  refine ⟨16504030860673518269912227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22005374480898024359882969 16504030860673518269912227)
  ·
    refine ⟨24756046291010277404868341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16504030860673518269912227 24756046291010277404868341)
    ·
      refine ⟨2320879339782213506706407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24756046291010277404868341 2320879339782213506706407)
      ·
        refine ⟨3481319009673320260059611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320879339782213506706407 3481319009673320260059611)
        ·
          refine ⟨5221978514509980390089417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481319009673320260059611 5221978514509980390089417)
          ·
            refine ⟨3916483885882485292567063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5221978514509980390089417 3916483885882485292567063)
            ·
              refine ⟨5874725828823727938850595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916483885882485292567063 5874725828823727938850595)
              ·
                refine ⟨8812088743235591908275893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874725828823727938850595 8812088743235591908275893)
                ·
                  refine ⟨826133319678336741400865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8812088743235591908275893 826133319678336741400865)
                  ·
                    refine ⟨619599989758752556050649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 826133319678336741400865 619599989758752556050649)
                    ·
                      refine ⟨464699992319064417037987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619599989758752556050649 464699992319064417037987)
                      ·
                        rfl

theorem cell23_905000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_905000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905000 prefixEnd_905000 := by exact prefixLift 905000
  have htrace : WordTrace (prefixWord ++ tailWord_905000) baseStart_905000 baseEnd_905000 := by
    simpa [prefixWord, tailWord_905000, baseEnd_905000] using wordTrace_append hprefix tailTrace_905000
  have hstable : (prefixWord ++ tailWord_905000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905000).length < 2 ^ (prefixWord ++ tailWord_905000).sum := by decide
  have hdescent : baseEnd_905000 < baseStart_905000 := by decide
  rcases family_descends (prefixWord ++ tailWord_905000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905020 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_905020 : Nat := 118140960795 + 905020 * 2 ^ 59
def prefixEnd_905020 : Nat := 4983230072969 + 3 ^ 40 * 905020 * 2
def baseEnd_905020 : Nat := 464710261932154338787895

theorem tailTrace_905020 : CollatzResearch.WordTrace tailWord_905020 prefixEnd_905020 464710261932154338787895 := by
  unfold tailWord_905020
  simp only [CollatzResearch.WordTrace]
  refine ⟨16504395590637289977776257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22005860787516386637035009 16504395590637289977776257)
  ·
    refine ⟨12378296692977967483332193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16504395590637289977776257 12378296692977967483332193)
    ·
      refine ⟨9283722519733475612499145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12378296692977967483332193 9283722519733475612499145)
      ·
        refine ⟨6962791889800106709374359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9283722519733475612499145 6962791889800106709374359)
        ·
          refine ⟨10444187834700160064061539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962791889800106709374359 10444187834700160064061539)
          ·
            refine ⟨15666281752050240096092309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444187834700160064061539 15666281752050240096092309)
            ·
              refine ⟨734356957127355004504327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15666281752050240096092309 734356957127355004504327)
              ·
                refine ⟨1101535435691032506756491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734356957127355004504327 1101535435691032506756491)
                ·
                  refine ⟨1652303153536548760134737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101535435691032506756491 1652303153536548760134737)
                  ·
                    refine ⟨1239227365152411570101053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1652303153536548760134737 1239227365152411570101053)
                    ·
                      refine ⟨464710261932154338787895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1239227365152411570101053 464710261932154338787895)
                      ·
                        rfl

theorem cell23_905020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_905020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905020 prefixEnd_905020 := by exact prefixLift 905020
  have htrace : WordTrace (prefixWord ++ tailWord_905020) baseStart_905020 baseEnd_905020 := by
    simpa [prefixWord, tailWord_905020, baseEnd_905020] using wordTrace_append hprefix tailTrace_905020
  have hstable : (prefixWord ++ tailWord_905020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905020).length < 2 ^ (prefixWord ++ tailWord_905020).sum := by decide
  have hdescent : baseEnd_905020 < baseStart_905020 := by decide
  rcases family_descends (prefixWord ++ tailWord_905020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905033 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 3]
def baseStart_905033 : Nat := 118140960795 + 905033 * 2 ^ 59
def prefixEnd_905033 : Nat := 4983230072969 + 3 ^ 40 * 905033 * 2
def baseEnd_905033 : Nat := 464716937180662787925335

theorem tailTrace_905033 : CollatzResearch.WordTrace tailWord_905033 prefixEnd_905033 464716937180662787925335 := by
  unfold tailWord_905033
  simp only [CollatzResearch.WordTrace]
  refine ⟨33009265330227483175775753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22006176886818322117183835 33009265330227483175775753)
  ·
    refine ⟨24756948997670612381831815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33009265330227483175775753 24756948997670612381831815)
    ·
      refine ⟨37135423496505918572747723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24756948997670612381831815 37135423496505918572747723)
      ·
        refine ⟨55703135244758877859121585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37135423496505918572747723 55703135244758877859121585)
        ·
          refine ⟨41777351433569158394341189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55703135244758877859121585 41777351433569158394341189)
          ·
            refine ⟨7833253393794217198938973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41777351433569158394341189 7833253393794217198938973)
            ·
              refine ⟨2937470022672831449602115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7833253393794217198938973 2937470022672831449602115)
              ·
                refine ⟨4406205034009247174403173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937470022672831449602115 4406205034009247174403173)
                ·
                  refine ⟨826163443876733845200595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4406205034009247174403173 826163443876733845200595)
                  ·
                    refine ⟨1239245165815100767800893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 826163443876733845200595 1239245165815100767800893)
                    ·
                      refine ⟨464716937180662787925335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1239245165815100767800893 464716937180662787925335)
                      ·
                        rfl

theorem cell23_905033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 3].length) (baseStart_905033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905033 prefixEnd_905033 := by exact prefixLift 905033
  have htrace : WordTrace (prefixWord ++ tailWord_905033) baseStart_905033 baseEnd_905033 := by
    simpa [prefixWord, tailWord_905033, baseEnd_905033] using wordTrace_append hprefix tailTrace_905033
  have hstable : (prefixWord ++ tailWord_905033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905033).length < 2 ^ (prefixWord ++ tailWord_905033).sum := by decide
  have hdescent : baseEnd_905033 < baseStart_905033 := by decide
  rcases family_descends (prefixWord ++ tailWord_905033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905073 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 3, 4, 2]
def baseStart_905073 : Nat := 118140960795 + 905073 * 2 ^ 59
def prefixEnd_905073 : Nat := 4983230072969 + 3 ^ 40 * 905073 * 2
def baseEnd_905073 : Nat := 464737476406842631425151

theorem tailTrace_905073 : CollatzResearch.WordTrace tailWord_905073 prefixEnd_905073 464737476406842631425151 := by
  unfold tailWord_905073
  simp only [CollatzResearch.WordTrace]
  refine ⟨33010724250082570007231873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22007149500055046671487915 33010724250082570007231873)
  ·
    refine ⟨24758043187561927505423905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33010724250082570007231873 24758043187561927505423905)
    ·
      refine ⟨18568532390671445629067929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24758043187561927505423905 18568532390671445629067929)
      ·
        refine ⟨13926399293003584221800947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18568532390671445629067929 13926399293003584221800947)
        ·
          refine ⟨20889598939505376332701421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13926399293003584221800947 20889598939505376332701421)
          ·
            refine ⟨7833599602314516124763033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20889598939505376332701421 7833599602314516124763033)
            ·
              refine ⟨5875199701735887093572275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7833599602314516124763033 5875199701735887093572275)
              ·
                refine ⟨8812799552603830640358413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875199701735887093572275 8812799552603830640358413)
                ·
                  refine ⟨3304799832226436490134405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8812799552603830640358413 3304799832226436490134405)
                  ·
                    refine ⟨619649968542456841900201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304799832226436490134405 619649968542456841900201)
                    ·
                      refine ⟨464737476406842631425151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619649968542456841900201 464737476406842631425151)
                      ·
                        rfl

theorem cell23_905073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_905073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905073 prefixEnd_905073 := by exact prefixLift 905073
  have htrace : WordTrace (prefixWord ++ tailWord_905073) baseStart_905073 baseEnd_905073 := by
    simpa [prefixWord, tailWord_905073, baseEnd_905073] using wordTrace_append hprefix tailTrace_905073
  have hstable : (prefixWord ++ tailWord_905073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905073).length < 2 ^ (prefixWord ++ tailWord_905073).sum := by decide
  have hdescent : baseEnd_905073 < baseStart_905073 := by decide
  rcases family_descends (prefixWord ++ tailWord_905073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905150 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_905150 : Nat := 118140960795 + 905150 * 2 ^ 59
def prefixEnd_905150 : Nat := 4983230072969 + 3 ^ 40 * 905150 * 2
def baseEnd_905150 : Nat := 464777014417238830162297

theorem tailTrace_905150 : CollatzResearch.WordTrace tailWord_905150 prefixEnd_905150 464777014417238830162297 := by
  unfold tailWord_905150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126691583850451519723113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22009021780535741438523269 4126691583850451519723113)
  ·
    refine ⟨3095018687887838639792335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4126691583850451519723113 3095018687887838639792335)
    ·
      refine ⟨4642528031831757959688503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095018687887838639792335 4642528031831757959688503)
      ·
        refine ⟨6963792047747636939532755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642528031831757959688503 6963792047747636939532755)
        ·
          refine ⟨10445688071621455409299133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963792047747636939532755 10445688071621455409299133)
          ·
            refine ⟨3917133026858045778487175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10445688071621455409299133 3917133026858045778487175)
            ·
              refine ⟨5875699540287068667730763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917133026858045778487175 5875699540287068667730763)
              ·
                refine ⟨8813549310430603001596145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875699540287068667730763 8813549310430603001596145)
                ·
                  refine ⟨6610161982822952251197109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8813549310430603001596145 6610161982822952251197109)
                  ·
                    refine ⟨619702685889651773549729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6610161982822952251197109 619702685889651773549729)
                    ·
                      refine ⟨464777014417238830162297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619702685889651773549729 464777014417238830162297)
                      ·
                        rfl

theorem cell23_905150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_905150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905150 prefixEnd_905150 := by exact prefixLift 905150
  have htrace : WordTrace (prefixWord ++ tailWord_905150) baseStart_905150 baseEnd_905150 := by
    simpa [prefixWord, tailWord_905150, baseEnd_905150] using wordTrace_append hprefix tailTrace_905150
  have hstable : (prefixWord ++ tailWord_905150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905150).length < 2 ^ (prefixWord ++ tailWord_905150).sum := by decide
  have hdescent : baseEnd_905150 < baseStart_905150 := by decide
  rcases family_descends (prefixWord ++ tailWord_905150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905177 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 2, 5]
def baseStart_905177 : Nat := 118140960795 + 905177 * 2 ^ 59
def prefixEnd_905177 : Nat := 4983230072969 + 3 ^ 40 * 905177 * 2
def baseEnd_905177 : Nat := 154930292798303408174891

theorem tailTrace_905177 : CollatzResearch.WordTrace tailWord_905177 prefixEnd_905177 154930292798303408174891 := by
  unfold tailWord_905177
  simp only [CollatzResearch.WordTrace]
  refine ⟨33014517441705795769017785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22009678294470530512678523 33014517441705795769017785)
  ·
    refine ⟨24760888081279346826763339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33014517441705795769017785 24760888081279346826763339)
    ·
      refine ⟨37141332121919020240145009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24760888081279346826763339 37141332121919020240145009)
      ·
        refine ⟨27855999091439265180108757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37141332121919020240145009 27855999091439265180108757)
        ·
          refine ⟨652874978705607777658799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27855999091439265180108757 652874978705607777658799)
          ·
            refine ⟨979312468058411666488199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652874978705607777658799 979312468058411666488199)
            ·
              refine ⟨1468968702087617499732299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979312468058411666488199 1468968702087617499732299)
              ·
                refine ⟨2203453053131426249598449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468968702087617499732299 2203453053131426249598449)
                ·
                  refine ⟨1652589789848569687198837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2203453053131426249598449 1652589789848569687198837)
                  ·
                    refine ⟨154930292798303408174891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1652589789848569687198837 154930292798303408174891)
                    ·
                      rfl

theorem cell23_905177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 5].length) (baseStart_905177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905177 prefixEnd_905177 := by exact prefixLift 905177
  have htrace : WordTrace (prefixWord ++ tailWord_905177) baseStart_905177 baseEnd_905177 := by
    simpa [prefixWord, tailWord_905177, baseEnd_905177] using wordTrace_append hprefix tailTrace_905177
  have hstable : (prefixWord ++ tailWord_905177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905177).length < 2 ^ (prefixWord ++ tailWord_905177).sum := by decide
  have hdescent : baseEnd_905177 < baseStart_905177 := by decide
  rcases family_descends (prefixWord ++ tailWord_905177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905216 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 9]
def baseStart_905216 : Nat := 118140960795 + 905216 * 2 ^ 59
def prefixEnd_905216 : Nat := 4983230072969 + 3 ^ 40 * 905216 * 2
def baseEnd_905216 : Nat := 154936968046811857312331

theorem tailTrace_905216 : CollatzResearch.WordTrace tailWord_905216 prefixEnd_905216 154936968046811857312331 := by
  unfold tailWord_905216
  simp only [CollatzResearch.WordTrace]
  refine ⟨16507969944282252714843751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22010626592376336953125001 16507969944282252714843751)
  ·
    refine ⟨24761954916423379072265627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16507969944282252714843751 24761954916423379072265627)
    ·
      refine ⟨37142932374635068608398441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24761954916423379072265627 37142932374635068608398441)
      ·
        refine ⟨27857199280976301456298831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37142932374635068608398441 27857199280976301456298831)
        ·
          refine ⟨41785798921464452184448247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27857199280976301456298831 41785798921464452184448247)
          ·
            refine ⟨62678698382196678276672371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41785798921464452184448247 62678698382196678276672371)
            ·
              refine ⟨94018047573295017415008557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62678698382196678276672371 94018047573295017415008557)
              ·
                refine ⟨35256767839985631530628209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94018047573295017415008557 35256767839985631530628209)
                ·
                  refine ⟨26442575879989223647971157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35256767839985631530628209 26442575879989223647971157)
                  ·
                    refine ⟨154936968046811857312331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 26442575879989223647971157 154936968046811857312331)
                    ·
                      rfl

theorem cell23_905216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_905216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905216 prefixEnd_905216 := by exact prefixLift 905216
  have htrace : WordTrace (prefixWord ++ tailWord_905216) baseStart_905216 baseEnd_905216 := by
    simpa [prefixWord, tailWord_905216, baseEnd_905216] using wordTrace_append hprefix tailTrace_905216
  have hstable : (prefixWord ++ tailWord_905216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905216).length < 2 ^ (prefixWord ++ tailWord_905216).sum := by decide
  have hdescent : baseEnd_905216 < baseStart_905216 := by decide
  rcases family_descends (prefixWord ++ tailWord_905216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905240 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 1, 5, 2]
def baseStart_905240 : Nat := 118140960795 + 905240 * 2 ^ 59
def prefixEnd_905240 : Nat := 4983230072969 + 3 ^ 40 * 905240 * 2
def baseEnd_905240 : Nat := 464823227676143478036883

theorem tailTrace_905240 : CollatzResearch.WordTrace tailWord_905240 prefixEnd_905240 464823227676143478036883 := by
  unfold tailWord_905240
  simp only [CollatzResearch.WordTrace]
  refine ⟨16508407620238778764280587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22011210160318371685707449 16508407620238778764280587)
  ·
    refine ⟨24762611430358168146420881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16508407620238778764280587 24762611430358168146420881)
    ·
      refine ⟨18571958572768626109815661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24762611430358168146420881 18571958572768626109815661)
      ·
        refine ⟨6964484464788234791180873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18571958572768626109815661 6964484464788234791180873)
        ·
          refine ⟨5223363348591176093385655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6964484464788234791180873 5223363348591176093385655)
          ·
            refine ⟨7835045022886764140078483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223363348591176093385655 7835045022886764140078483)
            ·
              refine ⟨11752567534330146210117725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835045022886764140078483 11752567534330146210117725)
              ·
                refine ⟨4407212825373804828794147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11752567534330146210117725 4407212825373804828794147)
                ·
                  refine ⟨6610819238060707243191221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407212825373804828794147 6610819238060707243191221)
                  ·
                    refine ⟨619764303568191304049177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6610819238060707243191221 619764303568191304049177)
                    ·
                      refine ⟨464823227676143478036883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619764303568191304049177 464823227676143478036883)
                      ·
                        rfl

theorem cell23_905240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_905240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905240 prefixEnd_905240 := by exact prefixLift 905240
  have htrace : WordTrace (prefixWord ++ tailWord_905240) baseStart_905240 baseEnd_905240 := by
    simpa [prefixWord, tailWord_905240, baseEnd_905240] using wordTrace_append hprefix tailTrace_905240
  have hstable : (prefixWord ++ tailWord_905240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905240).length < 2 ^ (prefixWord ++ tailWord_905240).sum := by decide
  have hdescent : baseEnd_905240 < baseStart_905240 := by decide
  rcases family_descends (prefixWord ++ tailWord_905240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905250 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_905250 : Nat := 118140960795 + 905250 * 2 ^ 59
def prefixEnd_905250 : Nat := 4983230072969 + 3 ^ 40 * 905250 * 2
def baseEnd_905250 : Nat := 154942787494229479637279

theorem tailTrace_905250 : CollatzResearch.WordTrace tailWord_905250 prefixEnd_905250 154942787494229479637279 := by
  unfold tailWord_905250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254294992610332309106301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22011453313627552824283469 8254294992610332309106301)
  ·
    refine ⟨3095360622228874615914863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8254294992610332309106301 3095360622228874615914863)
    ·
      refine ⟨4643040933343311923872295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095360622228874615914863 4643040933343311923872295)
      ·
        refine ⟨6964561400014967885808443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643040933343311923872295 6964561400014967885808443)
        ·
          refine ⟨10446842100022451828712665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964561400014967885808443 10446842100022451828712665)
          ·
            refine ⟨7835131575016838871534499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10446842100022451828712665 7835131575016838871534499)
            ·
              refine ⟨11752697362525258307301749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835131575016838871534499 11752697362525258307301749)
              ·
                refine ⟨1101815377736742966309539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11752697362525258307301749 1101815377736742966309539)
                ·
                  refine ⟨1652723066605114449464309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101815377736742966309539 1652723066605114449464309)
                  ·
                    refine ⟨154942787494229479637279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1652723066605114449464309 154942787494229479637279)
                    ·
                      rfl

theorem cell23_905250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_905250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905250 prefixEnd_905250 := by exact prefixLift 905250
  have htrace : WordTrace (prefixWord ++ tailWord_905250) baseStart_905250 baseEnd_905250 := by
    simpa [prefixWord, tailWord_905250, baseEnd_905250] using wordTrace_append hprefix tailTrace_905250
  have hstable : (prefixWord ++ tailWord_905250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905250).length < 2 ^ (prefixWord ++ tailWord_905250).sum := by decide
  have hdescent : baseEnd_905250 < baseStart_905250 := by decide
  rcases family_descends (prefixWord ++ tailWord_905250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905287 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_905287 : Nat := 118140960795 + 905287 * 2 ^ 59
def prefixEnd_905287 : Nat := 4983230072969 + 3 ^ 40 * 905287 * 2
def baseEnd_905287 : Nat := 464847361266904794149167

theorem tailTrace_905287 : CollatzResearch.WordTrace tailWord_905287 prefixEnd_905287 464847361266904794149167 := by
  unfold tailWord_905287
  simp only [CollatzResearch.WordTrace]
  refine ⟨33018529471307284555522115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22012352980871523037014743 33018529471307284555522115)
  ·
    refine ⟨49527794206960926833283173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33018529471307284555522115 49527794206960926833283173)
    ·
      refine ⟨9286461413805173781240595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49527794206960926833283173 9286461413805173781240595)
      ·
        refine ⟨13929692120707760671860893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9286461413805173781240595 13929692120707760671860893)
        ·
          refine ⟨5223634545265410251947835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13929692120707760671860893 5223634545265410251947835)
          ·
            refine ⟨7835451817898115377921753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223634545265410251947835 7835451817898115377921753)
            ·
              refine ⟨5876588863423586533441315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7835451817898115377921753 5876588863423586533441315)
              ·
                refine ⟨8814883295135379800161973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876588863423586533441315 8814883295135379800161973)
                ·
                  refine ⟨826395308918941856265185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8814883295135379800161973 826395308918941856265185)
                  ·
                    refine ⟨619796481689206392198889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 826395308918941856265185 619796481689206392198889)
                    ·
                      refine ⟨464847361266904794149167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619796481689206392198889 464847361266904794149167)
                      ·
                        rfl

theorem cell23_905287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_905287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905287 prefixEnd_905287 := by exact prefixLift 905287
  have htrace : WordTrace (prefixWord ++ tailWord_905287) baseStart_905287 baseEnd_905287 := by
    simpa [prefixWord, tailWord_905287, baseEnd_905287] using wordTrace_append hprefix tailTrace_905287
  have hstable : (prefixWord ++ tailWord_905287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905287).length < 2 ^ (prefixWord ++ tailWord_905287).sum := by decide
  have hdescent : baseEnd_905287 < baseStart_905287 := by decide
  rcases family_descends (prefixWord ++ tailWord_905287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905337 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 3]
def baseStart_905337 : Nat := 118140960795 + 905337 * 2 ^ 59
def prefixEnd_905337 : Nat := 4983230072969 + 3 ^ 40 * 905337 * 2
def baseEnd_905337 : Nat := 464873035299629598523937

theorem tailTrace_905337 : CollatzResearch.WordTrace tailWord_905337 prefixEnd_905337 464873035299629598523937 := by
  unfold tailWord_905337
  simp only [CollatzResearch.WordTrace]
  refine ⟨33020353121126143094842265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22013568747417428729894843 33020353121126143094842265)
  ·
    refine ⟨24765264840844607321131699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33020353121126143094842265 24765264840844607321131699)
    ·
      refine ⟨37147897261266910981697549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24765264840844607321131699 37147897261266910981697549)
      ·
        refine ⟨13930461472975091618136581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37147897261266910981697549 13930461472975091618136581)
        ·
          refine ⟨2611961526182829678400609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13930461472975091618136581 2611961526182829678400609)
          ·
            refine ⟨1958971144637122258800457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611961526182829678400609 1958971144637122258800457)
            ·
              refine ⟨1469228358477841694100343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958971144637122258800457 1469228358477841694100343)
              ·
                refine ⟨2203842537716762541150515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469228358477841694100343 2203842537716762541150515)
                ·
                  refine ⟨3305763806575143811725773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203842537716762541150515 3305763806575143811725773)
                  ·
                    refine ⟨1239661427465678929397165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3305763806575143811725773 1239661427465678929397165)
                    ·
                      refine ⟨464873035299629598523937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1239661427465678929397165 464873035299629598523937)
                      ·
                        rfl

theorem cell23_905337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_905337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905337 prefixEnd_905337 := by exact prefixLift 905337
  have htrace : WordTrace (prefixWord ++ tailWord_905337) baseStart_905337 baseEnd_905337 := by
    simpa [prefixWord, tailWord_905337, baseEnd_905337] using wordTrace_append hprefix tailTrace_905337
  have hstable : (prefixWord ++ tailWord_905337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905337).length < 2 ^ (prefixWord ++ tailWord_905337).sum := by decide
  have hdescent : baseEnd_905337 < baseStart_905337 := by decide
  rcases family_descends (prefixWord ++ tailWord_905337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905347 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 3, 3, 2]
def baseStart_905347 : Nat := 118140960795 + 905347 * 2 ^ 59
def prefixEnd_905347 : Nat := 4983230072969 + 3 ^ 40 * 905347 * 2
def baseEnd_905347 : Nat := 464878170106174559398891

theorem tailTrace_905347 : CollatzResearch.WordTrace tailWord_905347 prefixEnd_905347 464878170106174559398891 := by
  unfold tailWord_905347
  simp only [CollatzResearch.WordTrace]
  refine ⟨33020717851089914802706295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22013811900726609868470863 33020717851089914802706295)
  ·
    refine ⟨49531076776634872204059443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33020717851089914802706295 49531076776634872204059443)
    ·
      refine ⟨74296615164952308306089165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49531076776634872204059443 74296615164952308306089165)
      ·
        refine ⟨27861230686857115614783437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74296615164952308306089165 27861230686857115614783437)
        ·
          refine ⟨10447961507571418355543789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27861230686857115614783437 10447961507571418355543789)
          ·
            refine ⟨3917985565339281883328921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10447961507571418355543789 3917985565339281883328921)
            ·
              refine ⟨2938489174004461412496691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917985565339281883328921 2938489174004461412496691)
              ·
                refine ⟨4407733761006692118745037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938489174004461412496691 4407733761006692118745037)
                ·
                  refine ⟨1652900160377509544529389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4407733761006692118745037 1652900160377509544529389)
                  ·
                    refine ⟨619837560141566079198521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652900160377509544529389 619837560141566079198521)
                    ·
                      refine ⟨464878170106174559398891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619837560141566079198521 464878170106174559398891)
                      ·
                        rfl

theorem cell23_905347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_905347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905347 prefixEnd_905347 := by exact prefixLift 905347
  have htrace : WordTrace (prefixWord ++ tailWord_905347) baseStart_905347 baseEnd_905347 := by
    simpa [prefixWord, tailWord_905347, baseEnd_905347] using wordTrace_append hprefix tailTrace_905347
  have hstable : (prefixWord ++ tailWord_905347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905347).length < 2 ^ (prefixWord ++ tailWord_905347).sum := by decide
  have hdescent : baseEnd_905347 < baseStart_905347 := by decide
  rcases family_descends (prefixWord ++ tailWord_905347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905353 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 1, 8]
def baseStart_905353 : Nat := 118140960795 + 905353 * 2 ^ 59
def prefixEnd_905353 : Nat := 4983230072969 + 3 ^ 40 * 905353 * 2
def baseEnd_905353 : Nat := 154960416996700511974621

theorem tailTrace_905353 : CollatzResearch.WordTrace tailWord_905353 prefixEnd_905353 154960416996700511974621 := by
  unfold tailWord_905353
  simp only [CollatzResearch.WordTrace]
  refine ⟨33020936689068177827424713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22013957792712118551616475 33020936689068177827424713)
  ·
    refine ⟨24765702516801133370568535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33020936689068177827424713 24765702516801133370568535)
    ·
      refine ⟨37148553775201700055852803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24765702516801133370568535 37148553775201700055852803)
      ·
        refine ⟨55722830662802550083779205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37148553775201700055852803 55722830662802550083779205)
        ·
          refine ⟨10448030749275478140708601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55722830662802550083779205 10448030749275478140708601)
          ·
            refine ⟨7836023061956608605531451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10448030749275478140708601 7836023061956608605531451)
            ·
              refine ⟨11754034592934912908297177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836023061956608605531451 11754034592934912908297177)
              ·
                refine ⟨8815525944701184681222883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11754034592934912908297177 8815525944701184681222883)
                ·
                  refine ⟨13223288917051777021834325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815525944701184681222883 13223288917051777021834325)
                  ·
                    refine ⟨154960416996700511974621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13223288917051777021834325 154960416996700511974621)
                    ·
                      rfl

theorem cell23_905353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_905353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905353 prefixEnd_905353 := by exact prefixLift 905353
  have htrace : WordTrace (prefixWord ++ tailWord_905353) baseStart_905353 baseEnd_905353 := by
    simpa [prefixWord, tailWord_905353, baseEnd_905353] using wordTrace_append hprefix tailTrace_905353
  have hstable : (prefixWord ++ tailWord_905353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905353).length < 2 ^ (prefixWord ++ tailWord_905353).sum := by decide
  have hdescent : baseEnd_905353 < baseStart_905353 := by decide
  rcases family_descends (prefixWord ++ tailWord_905353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905358 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_905358 : Nat := 118140960795 + 905358 * 2 ^ 59
def prefixEnd_905358 : Nat := 4983230072969 + 3 ^ 40 * 905358 * 2
def baseEnd_905358 : Nat := 464883818393374016361341

theorem tailTrace_905358 : CollatzResearch.WordTrace tailWord_905358 prefixEnd_905358 464883818393374016361341 := by
  unfold tailWord_905358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127639881756257960169591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22014079369366709120904485 4127639881756257960169591)
  ·
    refine ⟨6191459822634386940254387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4127639881756257960169591 6191459822634386940254387)
    ·
      refine ⟨9287189733951580410381581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6191459822634386940254387 9287189733951580410381581)
      ·
        refine ⟨3482696150231842653893093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9287189733951580410381581 3482696150231842653893093)
        ·
          refine ⟨653005528168470497604955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3482696150231842653893093 653005528168470497604955)
          ·
            refine ⟨979508292252705746407433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653005528168470497604955 979508292252705746407433)
            ·
              refine ⟨734631219189529309805575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979508292252705746407433 734631219189529309805575)
              ·
                refine ⟨1101946828784293964708363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734631219189529309805575 1101946828784293964708363)
                ·
                  refine ⟨1652920243176440947062545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101946828784293964708363 1652920243176440947062545)
                  ·
                    refine ⟨1239690182382330710296909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1652920243176440947062545 1239690182382330710296909)
                    ·
                      refine ⟨464883818393374016361341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1239690182382330710296909 464883818393374016361341)
                      ·
                        rfl

theorem cell23_905358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_905358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905358 prefixEnd_905358 := by exact prefixLift 905358
  have htrace : WordTrace (prefixWord ++ tailWord_905358) baseStart_905358 baseEnd_905358 := by
    simpa [prefixWord, tailWord_905358, baseEnd_905358] using wordTrace_append hprefix tailTrace_905358
  have hstable : (prefixWord ++ tailWord_905358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905358).length < 2 ^ (prefixWord ++ tailWord_905358).sum := by decide
  have hdescent : baseEnd_905358 < baseStart_905358 := by decide
  rcases family_descends (prefixWord ++ tailWord_905358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905363 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5]
def baseStart_905363 : Nat := 118140960795 + 905363 * 2 ^ 59
def prefixEnd_905363 : Nat := 4983230072969 + 3 ^ 40 * 905363 * 2
def baseEnd_905363 : Nat := 464886385796646496798817

theorem tailTrace_905363 : CollatzResearch.WordTrace tailWord_905363 prefixEnd_905363 464886385796646496798817 := by
  unfold tailWord_905363
  simp only [CollatzResearch.WordTrace]
  refine ⟨33021301419031949535288743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22014200946021299690192495 33021301419031949535288743)
  ·
    refine ⟨49531952128547924302933115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33021301419031949535288743 49531952128547924302933115)
    ·
      refine ⟨74297928192821886454399673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49531952128547924302933115 74297928192821886454399673)
      ·
        refine ⟨55723446144616414840799755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74297928192821886454399673 55723446144616414840799755)
        ·
          refine ⟨83585169216924622261199633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55723446144616414840799755 83585169216924622261199633)
          ·
            refine ⟨62688876912693466695899725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83585169216924622261199633 62688876912693466695899725)
            ·
              refine ⟨23508328842260050010962397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62688876912693466695899725 23508328842260050010962397)
              ·
                refine ⟨8815623315847518754110899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23508328842260050010962397 8815623315847518754110899)
                ·
                  refine ⟨13223434973771278131166349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815623315847518754110899 13223434973771278131166349)
                  ·
                    refine ⟨4958788115164229299187381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13223434973771278131166349 4958788115164229299187381)
                    ·
                      refine ⟨464886385796646496798817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4958788115164229299187381 464886385796646496798817)
                      ·
                        rfl

theorem cell23_905363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_905363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905363 prefixEnd_905363 := by exact prefixLift 905363
  have htrace : WordTrace (prefixWord ++ tailWord_905363) baseStart_905363 baseEnd_905363 := by
    simpa [prefixWord, tailWord_905363, baseEnd_905363] using wordTrace_append hprefix tailTrace_905363
  have hstable : (prefixWord ++ tailWord_905363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905363).length < 2 ^ (prefixWord ++ tailWord_905363).sum := by decide
  have hdescent : baseEnd_905363 < baseStart_905363 := by decide
  rcases family_descends (prefixWord ++ tailWord_905363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905440 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_905440 : Nat := 118140960795 + 905440 * 2 ^ 59
def prefixEnd_905440 : Nat := 4983230072969 + 3 ^ 40 * 905440 * 2
def baseEnd_905440 : Nat := 464925923807042695535963

theorem tailTrace_905440 : CollatzResearch.WordTrace tailWord_905440 prefixEnd_905440 464925923807042695535963 := by
  unfold tailWord_905440
  simp only [CollatzResearch.WordTrace]
  refine ⟨16512054919876495842920887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22016073226501994457227849 16512054919876495842920887)
  ·
    refine ⟨24768082379814743764381331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16512054919876495842920887 24768082379814743764381331)
    ·
      refine ⟨37152123569722115646571997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24768082379814743764381331 37152123569722115646571997)
      ·
        refine ⟨13932046338645793367464499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37152123569722115646571997 13932046338645793367464499)
        ·
          refine ⟨20898069507968690051196749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13932046338645793367464499 20898069507968690051196749)
          ·
            refine ⟨7836776065488258769198781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20898069507968690051196749 7836776065488258769198781)
            ·
              refine ⟨2938791024558097038449543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7836776065488258769198781 2938791024558097038449543)
              ·
                refine ⟨4408186536837145557674315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938791024558097038449543 4408186536837145557674315)
                ·
                  refine ⟨6612279805255718336511473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408186536837145557674315 6612279805255718336511473)
                  ·
                    refine ⟨4959209853941788752383605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6612279805255718336511473 4959209853941788752383605)
                    ·
                      refine ⟨464925923807042695535963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4959209853941788752383605 464925923807042695535963)
                      ·
                        rfl

theorem cell23_905440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_905440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905440 prefixEnd_905440 := by exact prefixLift 905440
  have htrace : WordTrace (prefixWord ++ tailWord_905440) baseStart_905440 baseEnd_905440 := by
    simpa [prefixWord, tailWord_905440, baseEnd_905440] using wordTrace_append hprefix tailTrace_905440
  have hstable : (prefixWord ++ tailWord_905440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905440).length < 2 ^ (prefixWord ++ tailWord_905440).sum := by decide
  have hdescent : baseEnd_905440 < baseStart_905440 := by decide
  rcases family_descends (prefixWord ++ tailWord_905440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905501 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_905501 : Nat := 118140960795 + 905501 * 2 ^ 59
def prefixEnd_905501 : Nat := 4983230072969 + 3 ^ 40 * 905501 * 2
def baseEnd_905501 : Nat := 464957246126966956873183

theorem tailTrace_905501 : CollatzResearch.WordTrace tailWord_905501 prefixEnd_905501 464957246126966956873183 := by
  unfold tailWord_905501
  simp only [CollatzResearch.WordTrace]
  refine ⟨33026334692531999103812357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22017556461687999402541571 33026334692531999103812357)
  ·
    refine ⟨6192437754849749831964817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33026334692531999103812357 6192437754849749831964817)
    ·
      refine ⟨4644328316137312373973613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6192437754849749831964817 4644328316137312373973613)
      ·
        refine ⟨1741623118551492140240105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4644328316137312373973613 1741623118551492140240105)
        ·
          refine ⟨1306217338913619105180079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741623118551492140240105 1306217338913619105180079)
          ·
            refine ⟨1959326008370428657770119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306217338913619105180079 1959326008370428657770119)
            ·
              refine ⟨2938989012555642986655179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1959326008370428657770119 2938989012555642986655179)
              ·
                refine ⟨4408483518833464479982769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938989012555642986655179 4408483518833464479982769)
                ·
                  refine ⟨3306362639125098359987077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408483518833464479982769 3306362639125098359987077)
                  ·
                    refine ⟨619942994835955942497577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3306362639125098359987077 619942994835955942497577)
                    ·
                      refine ⟨464957246126966956873183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619942994835955942497577 464957246126966956873183)
                      ·
                        rfl

theorem cell23_905501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_905501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905501 prefixEnd_905501 := by exact prefixLift 905501
  have htrace : WordTrace (prefixWord ++ tailWord_905501) baseStart_905501 baseEnd_905501 := by
    simpa [prefixWord, tailWord_905501, baseEnd_905501] using wordTrace_append hprefix tailTrace_905501
  have hstable : (prefixWord ++ tailWord_905501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905501).length < 2 ^ (prefixWord ++ tailWord_905501).sum := by decide
  have hdescent : baseEnd_905501 < baseStart_905501 := by decide
  rcases family_descends (prefixWord ++ tailWord_905501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905518 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_905518 : Nat := 118140960795 + 905518 * 2 ^ 59
def prefixEnd_905518 : Nat := 4983230072969 + 3 ^ 40 * 905518 * 2
def baseEnd_905518 : Nat := 464965975298093390360605

theorem tailTrace_905518 : CollatzResearch.WordTrace tailWord_905518 prefixEnd_905518 464965975298093390360605 := by
  unfold tailWord_905518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128369341683801375897651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22017969822313607338120805 4128369341683801375897651)
  ·
    refine ⟨6192554012525702063846477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128369341683801375897651 6192554012525702063846477)
    ·
      refine ⟨2322207754697138273942429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6192554012525702063846477 2322207754697138273942429)
      ·
        refine ⟨870827908011426852728411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2322207754697138273942429 870827908011426852728411)
        ·
          refine ⟨1306241862017140279092617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870827908011426852728411 1306241862017140279092617)
          ·
            refine ⟨979681396512855209319463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306241862017140279092617 979681396512855209319463)
            ·
              refine ⟨1469522094769282813979195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979681396512855209319463 1469522094769282813979195)
              ·
                refine ⟨2204283142153924220968793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469522094769282813979195 2204283142153924220968793)
                ·
                  refine ⟨1653212356615443165726595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204283142153924220968793 1653212356615443165726595)
                  ·
                    refine ⟨2479818534923164748589893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653212356615443165726595 2479818534923164748589893)
                    ·
                      refine ⟨464965975298093390360605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2479818534923164748589893 464965975298093390360605)
                      ·
                        rfl

theorem cell23_905518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_905518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905518 prefixEnd_905518 := by exact prefixLift 905518
  have htrace : WordTrace (prefixWord ++ tailWord_905518) baseStart_905518 baseEnd_905518 := by
    simpa [prefixWord, tailWord_905518, baseEnd_905518] using wordTrace_append hprefix tailTrace_905518
  have hstable : (prefixWord ++ tailWord_905518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905518).length < 2 ^ (prefixWord ++ tailWord_905518).sum := by decide
  have hdescent : baseEnd_905518 < baseStart_905518 := by decide
  rcases family_descends (prefixWord ++ tailWord_905518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905521 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_905521 : Nat := 118140960795 + 905521 * 2 ^ 59
def prefixEnd_905521 : Nat := 4983230072969 + 3 ^ 40 * 905521 * 2
def baseEnd_905521 : Nat := 464967515740056878623091

theorem tailTrace_905521 : CollatzResearch.WordTrace tailWord_905521 prefixEnd_905521 464967515740056878623091 := by
  unfold tailWord_905521
  simp only [CollatzResearch.WordTrace]
  refine ⟨33027064152459542519540417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22018042768306361679693611 33027064152459542519540417)
  ·
    refine ⟨24770298114344656889655313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33027064152459542519540417 24770298114344656889655313)
    ·
      refine ⟨18577723585758492667241485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24770298114344656889655313 18577723585758492667241485)
      ·
        refine ⟨6966646344659434750215557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18577723585758492667241485 6966646344659434750215557)
        ·
          refine ⟨1306246189623644015665417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6966646344659434750215557 1306246189623644015665417)
          ·
            refine ⟨979684642217733011749063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306246189623644015665417 979684642217733011749063)
            ·
              refine ⟨1469526963326599517623595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979684642217733011749063 1469526963326599517623595)
              ·
                refine ⟨2204290444989899276435393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469526963326599517623595 2204290444989899276435393)
                ·
                  refine ⟨1653217833742424457326545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204290444989899276435393 1653217833742424457326545)
                  ·
                    refine ⟨1239913375306818342994909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1653217833742424457326545 1239913375306818342994909)
                    ·
                      refine ⟨464967515740056878623091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1239913375306818342994909 464967515740056878623091)
                      ·
                        rfl

theorem cell23_905521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_905521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905521 prefixEnd_905521 := by exact prefixLift 905521
  have htrace : WordTrace (prefixWord ++ tailWord_905521) baseStart_905521 baseEnd_905521 := by
    simpa [prefixWord, tailWord_905521, baseEnd_905521] using wordTrace_append hprefix tailTrace_905521
  have hstable : (prefixWord ++ tailWord_905521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905521).length < 2 ^ (prefixWord ++ tailWord_905521).sum := by decide
  have hdescent : baseEnd_905521 < baseStart_905521 := by decide
  rcases family_descends (prefixWord ++ tailWord_905521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905544 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_905544 : Nat := 118140960795 + 905544 * 2 ^ 59
def prefixEnd_905544 : Nat := 4983230072969 + 3 ^ 40 * 905544 * 2
def baseEnd_905544 : Nat := 464979325795110288635485

theorem tailTrace_905544 : CollatzResearch.WordTrace tailWord_905544 prefixEnd_905544 464979325795110288635485 := by
  unfold tailWord_905544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16513951515688108723813843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22018602020917478298418457 16513951515688108723813843)
  ·
    refine ⟨24770927273532163085720765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16513951515688108723813843 24770927273532163085720765)
    ·
      refine ⟨9289097727574561157145287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24770927273532163085720765 9289097727574561157145287)
      ·
        refine ⟨13933646591361841735717931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289097727574561157145287 13933646591361841735717931)
        ·
          refine ⟨20900469887042762603576897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13933646591361841735717931 20900469887042762603576897)
          ·
            refine ⟨15675352415282071952682673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20900469887042762603576897 15675352415282071952682673)
            ·
              refine ⟨11756514311461553964512005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15675352415282071952682673 11756514311461553964512005)
              ·
                refine ⟨2204346433399041368346001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11756514311461553964512005 2204346433399041368346001)
                ·
                  refine ⟨1653259825049281026259501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204346433399041368346001 1653259825049281026259501)
                  ·
                    refine ⟨619972434393480384847313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653259825049281026259501 619972434393480384847313)
                    ·
                      refine ⟨464979325795110288635485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619972434393480384847313 464979325795110288635485)
                      ·
                        rfl

theorem cell23_905544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_905544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905544 prefixEnd_905544 := by exact prefixLift 905544
  have htrace : WordTrace (prefixWord ++ tailWord_905544) baseStart_905544 baseEnd_905544 := by
    simpa [prefixWord, tailWord_905544, baseEnd_905544] using wordTrace_append hprefix tailTrace_905544
  have hstable : (prefixWord ++ tailWord_905544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905544).length < 2 ^ (prefixWord ++ tailWord_905544).sum := by decide
  have hdescent : baseEnd_905544 < baseStart_905544 := by decide
  rcases family_descends (prefixWord ++ tailWord_905544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905567 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 1, 6]
def baseStart_905567 : Nat := 118140960795 + 905567 * 2 ^ 59
def prefixEnd_905567 : Nat := 4983230072969 + 3 ^ 40 * 905567 * 2
def baseEnd_905567 : Nat := 154997045283387899549293

theorem tailTrace_905567 : CollatzResearch.WordTrace tailWord_905567 prefixEnd_905567 154997045283387899549293 := by
  unfold tailWord_905567
  simp only [CollatzResearch.WordTrace]
  refine ⟨33028741910292892375714955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22019161273528594917143303 33028741910292892375714955)
  ·
    refine ⟨49543112865439338563572433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33028741910292892375714955 49543112865439338563572433)
    ·
      refine ⟨37157334649079503922679325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49543112865439338563572433 37157334649079503922679325)
      ·
        refine ⟨13934000493404813971004747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37157334649079503922679325 13934000493404813971004747)
        ·
          refine ⟨20901000740107220956507121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934000493404813971004747 20901000740107220956507121)
          ·
            refine ⟨15675750555080415717380341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20901000740107220956507121 15675750555080415717380341)
            ·
              refine ⟨1469601614538788973504407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15675750555080415717380341 1469601614538788973504407)
              ·
                refine ⟨2204402421808183460256611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469601614538788973504407 2204402421808183460256611)
                ·
                  refine ⟨3306603632712275190384917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204402421808183460256611 3306603632712275190384917)
                  ·
                    refine ⟨154997045283387899549293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3306603632712275190384917 154997045283387899549293)
                    ·
                      rfl

theorem cell23_905567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_905567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905567 prefixEnd_905567 := by exact prefixLift 905567
  have htrace : WordTrace (prefixWord ++ tailWord_905567) baseStart_905567 baseEnd_905567 := by
    simpa [prefixWord, tailWord_905567, baseEnd_905567] using wordTrace_append hprefix tailTrace_905567
  have hstable : (prefixWord ++ tailWord_905567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905567).length < 2 ^ (prefixWord ++ tailWord_905567).sum := by decide
  have hdescent : baseEnd_905567 < baseStart_905567 := by decide
  rcases family_descends (prefixWord ++ tailWord_905567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905597 : List Nat := [1, 4, 1, 1, 2, 5, 9]
def baseStart_905597 : Nat := 118140960795 + 905597 * 2 ^ 59
def prefixEnd_905597 : Nat := 4983230072969 + 3 ^ 40 * 905597 * 2
def baseEnd_905597 : Nat := 5740821484812328163861

theorem tailTrace_905597 : CollatzResearch.WordTrace tailWord_905597 prefixEnd_905597 5740821484812328163861 := by
  unfold tailWord_905597
  simp only [CollatzResearch.WordTrace]
  refine ⟨33029836100184207499307045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22019890733456138332871363 33029836100184207499307045)
  ·
    refine ⟨6193094268784538906120071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33029836100184207499307045 6193094268784538906120071)
    ·
      refine ⟨9289641403176808359180107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193094268784538906120071 9289641403176808359180107)
      ·
        refine ⟨13934462104765212538770161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289641403176808359180107 13934462104765212538770161)
        ·
          refine ⟨10450846578573909404077621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13934462104765212538770161 10450846578573909404077621)
          ·
            refine ⟨979766866741304006632277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10450846578573909404077621 979766866741304006632277)
            ·
              refine ⟨5740821484812328163861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 979766866741304006632277 5740821484812328163861)
              ·
                rfl

theorem cell23_905597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 9].length) (baseStart_905597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905597 prefixEnd_905597 := by exact prefixLift 905597
  have htrace : WordTrace (prefixWord ++ tailWord_905597) baseStart_905597 baseEnd_905597 := by
    simpa [prefixWord, tailWord_905597, baseEnd_905597] using wordTrace_append hprefix tailTrace_905597
  have hstable : (prefixWord ++ tailWord_905597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905597).length < 2 ^ (prefixWord ++ tailWord_905597).sum := by decide
  have hdescent : baseEnd_905597 < baseStart_905597 := by decide
  rcases family_descends (prefixWord ++ tailWord_905597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905602 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_905602 : Nat := 118140960795 + 905602 * 2 ^ 59
def prefixEnd_905602 : Nat := 4983230072969 + 3 ^ 40 * 905602 * 2
def baseEnd_905602 : Nat := 465009107673071061710219

theorem tailTrace_905602 : CollatzResearch.WordTrace tailWord_905602 prefixEnd_905602 465009107673071061710219 := by
  unfold tailWord_905602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257504616291523338309765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22020012310110728902159373 8257504616291523338309765)
  ·
    refine ⟨1548282115554660625933081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8257504616291523338309765 1548282115554660625933081)
    ·
      refine ⟨1161211586665995469449811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1548282115554660625933081 1161211586665995469449811)
      ·
        refine ⟨1741817379998993204174717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161211586665995469449811 1741817379998993204174717)
        ·
          refine ⟨653181517499622451565519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1741817379998993204174717 653181517499622451565519)
          ·
            refine ⟨979772276249433677348279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653181517499622451565519 979772276249433677348279)
            ·
              refine ⟨1469658414374150516022419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979772276249433677348279 1469658414374150516022419)
              ·
                refine ⟨2204487621561225774033629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469658414374150516022419 2204487621561225774033629)
                ·
                  refine ⟨826682858085459665262611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2204487621561225774033629 826682858085459665262611)
                  ·
                    refine ⟨1240024287128189497893917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 826682858085459665262611 1240024287128189497893917)
                    ·
                      refine ⟨465009107673071061710219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1240024287128189497893917 465009107673071061710219)
                      ·
                        rfl

theorem cell23_905602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_905602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905602 prefixEnd_905602 := by exact prefixLift 905602
  have htrace : WordTrace (prefixWord ++ tailWord_905602) baseStart_905602 baseEnd_905602 := by
    simpa [prefixWord, tailWord_905602, baseEnd_905602] using wordTrace_append hprefix tailTrace_905602
  have hstable : (prefixWord ++ tailWord_905602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905602).length < 2 ^ (prefixWord ++ tailWord_905602).sum := by decide
  have hdescent : baseEnd_905602 < baseStart_905602 := by decide
  rcases family_descends (prefixWord ++ tailWord_905602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905614 : List Nat := [4, 1, 1, 4, 1, 2, 2, 8]
def baseStart_905614 : Nat := 118140960795 + 905614 * 2 ^ 59
def prefixEnd_905614 : Nat := 4983230072969 + 3 ^ 40 * 905614 * 2
def baseEnd_905614 : Nat := 17222787757071296842969

theorem tailTrace_905614 : CollatzResearch.WordTrace tailWord_905614 prefixEnd_905614 17222787757071296842969 := by
  unfold tailWord_905614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128807017640327425334487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22020304094081746268450597 4128807017640327425334487)
  ·
    refine ⟨6193210526460491138001731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128807017640327425334487 6193210526460491138001731)
    ·
      refine ⟨9289815789690736707002597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193210526460491138001731 9289815789690736707002597)
      ·
        refine ⟨1741840460567013132562987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9289815789690736707002597 1741840460567013132562987)
        ·
          refine ⟨2612760690850519698844481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741840460567013132562987 2612760690850519698844481)
          ·
            refine ⟨1959570518137889774133361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2612760690850519698844481 1959570518137889774133361)
            ·
              refine ⟨1469677888603417330600021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959570518137889774133361 1469677888603417330600021)
              ·
                refine ⟨17222787757071296842969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1469677888603417330600021 17222787757071296842969)
                ·
                  rfl

theorem cell23_905614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_905614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905614 prefixEnd_905614 := by exact prefixLift 905614
  have htrace : WordTrace (prefixWord ++ tailWord_905614) baseStart_905614 baseEnd_905614 := by
    simpa [prefixWord, tailWord_905614, baseEnd_905614] using wordTrace_append hprefix tailTrace_905614
  have hstable : (prefixWord ++ tailWord_905614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905614).length < 2 ^ (prefixWord ++ tailWord_905614).sum := by decide
  have hdescent : baseEnd_905614 < baseStart_905614 := by decide
  rcases family_descends (prefixWord ++ tailWord_905614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905622 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_905622 : Nat := 118140960795 + 905622 * 2 ^ 59
def prefixEnd_905622 : Nat := 4983230072969 + 3 ^ 40 * 905622 * 2
def baseEnd_905622 : Nat := 155006459095386994486709

theorem tailTrace_905622 : CollatzResearch.WordTrace tailWord_905622 prefixEnd_905622 155006459095386994486709 := by
  unfold tailWord_905622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064421745318352298060445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22020498616729091179311413 2064421745318352298060445)
  ·
    refine ⟨774158154494382111772667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2064421745318352298060445 774158154494382111772667)
    ·
      refine ⟨1161237231741573167659001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774158154494382111772667 1161237231741573167659001)
      ·
        refine ⟨870927923806179875744251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1161237231741573167659001 870927923806179875744251)
        ·
          refine ⟨1306391885709269813616377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870927923806179875744251 1306391885709269813616377)
          ·
            refine ⟨979793914281952360212283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306391885709269813616377 979793914281952360212283)
            ·
              refine ⟨1469690871422928540318425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979793914281952360212283 1469690871422928540318425)
              ·
                refine ⟨1102268153567196405238819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469690871422928540318425 1102268153567196405238819)
                ·
                  refine ⟨1653402230350794607858229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102268153567196405238819 1653402230350794607858229)
                  ·
                    refine ⟨155006459095386994486709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1653402230350794607858229 155006459095386994486709)
                    ·
                      rfl

theorem cell23_905622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_905622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905622 prefixEnd_905622 := by exact prefixLift 905622
  have htrace : WordTrace (prefixWord ++ tailWord_905622) baseStart_905622 baseEnd_905622 := by
    simpa [prefixWord, tailWord_905622, baseEnd_905622] using wordTrace_append hprefix tailTrace_905622
  have hstable : (prefixWord ++ tailWord_905622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905622).length < 2 ^ (prefixWord ++ tailWord_905622).sum := by decide
  have hdescent : baseEnd_905622 < baseStart_905622 := by decide
  rcases family_descends (prefixWord ++ tailWord_905622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905642 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_905642 : Nat := 118140960795 + 905642 * 2 ^ 59
def prefixEnd_905642 : Nat := 4983230072969 + 3 ^ 40 * 905642 * 2
def baseEnd_905642 : Nat := 465029646899250905210035

theorem tailTrace_905642 : CollatzResearch.WordTrace tailWord_905642 prefixEnd_905642 465029646899250905210035 := by
  unfold tailWord_905642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257869346255295046173795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22020984923347453456463453 8257869346255295046173795)
  ·
    refine ⟨12386804019382942569260693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8257869346255295046173795 12386804019382942569260693)
    ·
      refine ⟨580631438408575432934095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12386804019382942569260693 580631438408575432934095)
      ·
        refine ⟨870947157612863149401143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580631438408575432934095 870947157612863149401143)
        ·
          refine ⟨1306420736419294724101715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870947157612863149401143 1306420736419294724101715)
          ·
            refine ⟨1959631104628942086152573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306420736419294724101715 1959631104628942086152573)
            ·
              refine ⟨734861664235853282307215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1959631104628942086152573 734861664235853282307215)
              ·
                refine ⟨1102292496353779923460823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734861664235853282307215 1102292496353779923460823)
                ·
                  refine ⟨1653438744530669885191235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102292496353779923460823 1653438744530669885191235)
                  ·
                    refine ⟨2480158116796004827786853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653438744530669885191235 2480158116796004827786853)
                    ·
                      refine ⟨465029646899250905210035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2480158116796004827786853 465029646899250905210035)
                      ·
                        rfl

theorem cell23_905642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_905642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905642 prefixEnd_905642 := by exact prefixLift 905642
  have htrace : WordTrace (prefixWord ++ tailWord_905642) baseStart_905642 baseEnd_905642 := by
    simpa [prefixWord, tailWord_905642, baseEnd_905642] using wordTrace_append hprefix tailTrace_905642
  have hstable : (prefixWord ++ tailWord_905642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905642).length < 2 ^ (prefixWord ++ tailWord_905642).sum := by decide
  have hdescent : baseEnd_905642 < baseStart_905642 := by decide
  rcases family_descends (prefixWord ++ tailWord_905642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905645 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_905645 : Nat := 118140960795 + 905645 * 2 ^ 59
def prefixEnd_905645 : Nat := 4983230072969 + 3 ^ 40 * 905645 * 2
def baseEnd_905645 : Nat := 465031187341214393472521

theorem tailTrace_905645 : CollatzResearch.WordTrace tailWord_905645 prefixEnd_905645 465031187341214393472521 := by
  unfold tailWord_905645
  simp only [CollatzResearch.WordTrace]
  refine ⟨33031586804010311697054389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22021057869340207798036259 33031586804010311697054389)
  ·
    refine ⟨3096711262875966721598849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33031586804010311697054389 3096711262875966721598849)
    ·
      refine ⟨2322533447156975041199137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3096711262875966721598849 2322533447156975041199137)
      ·
        refine ⟨1741900085367731280899353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2322533447156975041199137 1741900085367731280899353)
        ·
          refine ⟨1306425064025798460674515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741900085367731280899353 1306425064025798460674515)
          ·
            refine ⟨1959637596038697691011773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306425064025798460674515 1959637596038697691011773)
            ·
              refine ⟨734864098514511634129415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1959637596038697691011773 734864098514511634129415)
              ·
                refine ⟨1102296147771767451194123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734864098514511634129415 1102296147771767451194123)
                ·
                  refine ⟨1653444221657651176791185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102296147771767451194123 1653444221657651176791185)
                  ·
                    refine ⟨1240083166243238382593389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1653444221657651176791185 1240083166243238382593389)
                    ·
                      refine ⟨465031187341214393472521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1240083166243238382593389 465031187341214393472521)
                      ·
                        rfl

theorem cell23_905645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_905645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905645 prefixEnd_905645 := by exact prefixLift 905645
  have htrace : WordTrace (prefixWord ++ tailWord_905645) baseStart_905645 baseEnd_905645 := by
    simpa [prefixWord, tailWord_905645, baseEnd_905645] using wordTrace_append hprefix tailTrace_905645
  have hstable : (prefixWord ++ tailWord_905645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905645).length < 2 ^ (prefixWord ++ tailWord_905645).sum := by decide
  have hdescent : baseEnd_905645 < baseStart_905645 := by decide
  rcases family_descends (prefixWord ++ tailWord_905645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905664 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 5, 4, 2]
def baseStart_905664 : Nat := 118140960795 + 905664 * 2 ^ 59
def prefixEnd_905664 : Nat := 4983230072969 + 3 ^ 40 * 905664 * 2
def baseEnd_905664 : Nat := 465040943473649819134933

theorem tailTrace_905664 : CollatzResearch.WordTrace tailWord_905664 prefixEnd_905664 465040943473649819134933 := by
  unfold tailWord_905664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16516139895470738970998023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22021519860627651961330697 16516139895470738970998023)
  ·
    refine ⟨24774209843206108456497035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16516139895470738970998023 24774209843206108456497035)
    ·
      refine ⟨37161314764809162684745553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24774209843206108456497035 37161314764809162684745553)
      ·
        refine ⟨27870986073606872013559165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37161314764809162684745553 27870986073606872013559165)
        ·
          refine ⟨10451619777602577005084687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27870986073606872013559165 10451619777602577005084687)
          ·
            refine ⟨15677429666403865507627031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451619777602577005084687 15677429666403865507627031)
            ·
              refine ⟨23516144499605798261440547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15677429666403865507627031 23516144499605798261440547)
              ·
                refine ⟨35274216749408697392160821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23516144499605798261440547 35274216749408697392160821)
                ·
                  refine ⟨3306957820257065380515077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35274216749408697392160821 3306957820257065380515077)
                  ·
                    refine ⟨620054591298199758846577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3306957820257065380515077 620054591298199758846577)
                    ·
                      refine ⟨465040943473649819134933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620054591298199758846577 465040943473649819134933)
                      ·
                        rfl

theorem cell23_905664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_905664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905664 prefixEnd_905664 := by exact prefixLift 905664
  have htrace : WordTrace (prefixWord ++ tailWord_905664) baseStart_905664 baseEnd_905664 := by
    simpa [prefixWord, tailWord_905664, baseEnd_905664] using wordTrace_append hprefix tailTrace_905664
  have hstable : (prefixWord ++ tailWord_905664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905664).length < 2 ^ (prefixWord ++ tailWord_905664).sum := by decide
  have hdescent : baseEnd_905664 < baseStart_905664 := by decide
  rcases family_descends (prefixWord ++ tailWord_905664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905665 : List Nat := [1, 2, 7, 1, 2, 1, 1, 8]
def baseStart_905665 : Nat := 118140960795 + 905665 * 2 ^ 59
def prefixEnd_905665 : Nat := 4983230072969 + 3 ^ 40 * 905665 * 2
def baseEnd_905665 : Nat := 17223757664974233897127

theorem tailTrace_905665 : CollatzResearch.WordTrace tailWord_905665 prefixEnd_905665 17223757664974233897127 := by
  unfold tailWord_905665
  simp only [CollatzResearch.WordTrace]
  refine ⟨33032316263937855112782449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22021544175958570075188299 33032316263937855112782449)
  ·
    refine ⟨24774237197953391334586837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33032316263937855112782449 24774237197953391334586837)
    ·
      refine ⟨580646184327032609404379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24774237197953391334586837 580646184327032609404379)
      ·
        refine ⟨870969276490548914106569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580646184327032609404379 870969276490548914106569)
        ·
          refine ⟨653226957367911685579927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870969276490548914106569 653226957367911685579927)
          ·
            refine ⟨979840436051867528369891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653226957367911685579927 979840436051867528369891)
            ·
              refine ⟨1469760654077801292554837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979840436051867528369891 1469760654077801292554837)
              ·
                refine ⟨17223757664974233897127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1469760654077801292554837 17223757664974233897127)
                ·
                  rfl

theorem cell23_905665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 8].length) (baseStart_905665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905665 prefixEnd_905665 := by exact prefixLift 905665
  have htrace : WordTrace (prefixWord ++ tailWord_905665) baseStart_905665 baseEnd_905665 := by
    simpa [prefixWord, tailWord_905665, baseEnd_905665] using wordTrace_append hprefix tailTrace_905665
  have hstable : (prefixWord ++ tailWord_905665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905665).length < 2 ^ (prefixWord ++ tailWord_905665).sum := by decide
  have hdescent : baseEnd_905665 < baseStart_905665 := by decide
  rcases family_descends (prefixWord ++ tailWord_905665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905727 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_905727 : Nat := 118140960795 + 905727 * 2 ^ 59
def prefixEnd_905727 : Nat := 4983230072969 + 3 ^ 40 * 905727 * 2
def baseEnd_905727 : Nat := 465073292754883072647143

theorem tailTrace_905727 : CollatzResearch.WordTrace tailWord_905727 prefixEnd_905727 465073292754883072647143 := by
  unfold tailWord_905727
  simp only [CollatzResearch.WordTrace]
  refine ⟨33034577589713239701539435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22023051726475493134359623 33034577589713239701539435)
  ·
    refine ⟨49551866384569859552309153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33034577589713239701539435 49551866384569859552309153)
    ·
      refine ⟨37163899788427394664231865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49551866384569859552309153 37163899788427394664231865)
      ·
        refine ⟨27872924841320545998173899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37163899788427394664231865 27872924841320545998173899)
        ·
          refine ⟨41809387261980818997260849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27872924841320545998173899 41809387261980818997260849)
          ·
            refine ⟨31357040446485614247945637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41809387261980818997260849 31357040446485614247945637)
            ·
              refine ⟨5879445083716052671489807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31357040446485614247945637 5879445083716052671489807)
              ·
                refine ⟨8819167625574079007234711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879445083716052671489807 8819167625574079007234711)
                ·
                  refine ⟨13228751438361118510852067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819167625574079007234711 13228751438361118510852067)
                  ·
                    refine ⟨19843127157541677766278101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13228751438361118510852067 19843127157541677766278101)
                    ·
                      refine ⟨465073292754883072647143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19843127157541677766278101 465073292754883072647143)
                      ·
                        rfl

theorem cell23_905727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_905727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905727 prefixEnd_905727 := by exact prefixLift 905727
  have htrace : WordTrace (prefixWord ++ tailWord_905727) baseStart_905727 baseEnd_905727 := by
    simpa [prefixWord, tailWord_905727, baseEnd_905727] using wordTrace_append hprefix tailTrace_905727
  have hstable : (prefixWord ++ tailWord_905727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905727).length < 2 ^ (prefixWord ++ tailWord_905727).sum := by decide
  have hdescent : baseEnd_905727 < baseStart_905727 := by decide
  rcases family_descends (prefixWord ++ tailWord_905727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905732 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_905732 : Nat := 118140960795 + 905732 * 2 ^ 59
def prefixEnd_905732 : Nat := 4983230072969 + 3 ^ 40 * 905732 * 2
def baseEnd_905732 : Nat := 465075860158155553084621

theorem tailTrace_905732 : CollatzResearch.WordTrace tailWord_905732 prefixEnd_905732 465075860158155553084621 := by
  unfold tailWord_905732
  simp only [CollatzResearch.WordTrace]
  refine ⟨16517379977347562777735725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22023173303130083703647633 16517379977347562777735725)
  ·
    refine ⟨6194017491505336041650897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16517379977347562777735725 6194017491505336041650897)
    ·
      refine ⟨4645513118629002031238173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6194017491505336041650897 4645513118629002031238173)
      ·
        refine ⟨1742067419485875761714315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4645513118629002031238173 1742067419485875761714315)
        ·
          refine ⟨2613101129228813642571473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742067419485875761714315 2613101129228813642571473)
          ·
            refine ⟨1959825846921610231928605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2613101129228813642571473 1959825846921610231928605)
            ·
              refine ⟨734934692595603836973227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1959825846921610231928605 734934692595603836973227)
              ·
                refine ⟨1102402038893405755459841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734934692595603836973227 1102402038893405755459841)
                ·
                  refine ⟨826801529170054316594881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1102402038893405755459841 826801529170054316594881)
                  ·
                    refine ⟨620101146877540737446161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 826801529170054316594881 620101146877540737446161)
                    ·
                      refine ⟨465075860158155553084621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620101146877540737446161 465075860158155553084621)
                      ·
                        rfl

theorem cell23_905732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_905732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905732 prefixEnd_905732 := by exact prefixLift 905732
  have htrace : WordTrace (prefixWord ++ tailWord_905732) baseStart_905732 baseEnd_905732 := by
    simpa [prefixWord, tailWord_905732, baseEnd_905732] using wordTrace_append hprefix tailTrace_905732
  have hstable : (prefixWord ++ tailWord_905732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905732).length < 2 ^ (prefixWord ++ tailWord_905732).sum := by decide
  have hdescent : baseEnd_905732 < baseStart_905732 := by decide
  rcases family_descends (prefixWord ++ tailWord_905732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905747 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 2, 8]
def baseStart_905747 : Nat := 118140960795 + 905747 * 2 ^ 59
def prefixEnd_905747 : Nat := 4983230072969 + 3 ^ 40 * 905747 * 2
def baseEnd_905747 : Nat := 155027854122657664799017

theorem tailTrace_905747 : CollatzResearch.WordTrace tailWord_905747 prefixEnd_905747 155027854122657664799017 := by
  unfold tailWord_905747
  simp only [CollatzResearch.WordTrace]
  refine ⟨33035307049640783117267495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22023538033093855411511663 33035307049640783117267495)
  ·
    refine ⟨49552960574461174675901243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33035307049640783117267495 49552960574461174675901243)
    ·
      refine ⟨74329440861691762013851865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49552960574461174675901243 74329440861691762013851865)
      ·
        refine ⟨55747080646268821510388899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74329440861691762013851865 55747080646268821510388899)
        ·
          refine ⟨83620620969403232265583349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55747080646268821510388899 83620620969403232265583349)
          ·
            refine ⟨7839433215881553024898439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83620620969403232265583349 7839433215881553024898439)
            ·
              refine ⟨11759149823822329537347659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7839433215881553024898439 11759149823822329537347659)
              ·
                refine ⟨17638724735733494306021489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759149823822329537347659 17638724735733494306021489)
                ·
                  refine ⟨13229043551800120729516117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17638724735733494306021489 13229043551800120729516117)
                  ·
                    refine ⟨155027854122657664799017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13229043551800120729516117 155027854122657664799017)
                    ·
                      rfl

theorem cell23_905747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 8].length) (baseStart_905747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905747 prefixEnd_905747 := by exact prefixLift 905747
  have htrace : WordTrace (prefixWord ++ tailWord_905747) baseStart_905747 baseEnd_905747 := by
    simpa [prefixWord, tailWord_905747, baseEnd_905747] using wordTrace_append hprefix tailTrace_905747
  have hstable : (prefixWord ++ tailWord_905747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905747).length < 2 ^ (prefixWord ++ tailWord_905747).sum := by decide
  have hdescent : baseEnd_905747 < baseStart_905747 := by decide
  rcases family_descends (prefixWord ++ tailWord_905747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905754 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_905754 : Nat := 118140960795 + 905754 * 2 ^ 59
def prefixEnd_905754 : Nat := 4983230072969 + 3 ^ 40 * 905754 * 2
def baseEnd_905754 : Nat := 465087156732554467009519

theorem tailTrace_905754 : CollatzResearch.WordTrace tailWord_905754 prefixEnd_905754 465087156732554467009519 := by
  unfold tailWord_905754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258890590153855828193079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22023708240410282208514877 8258890590153855828193079)
  ·
    refine ⟨12388335885230783742289619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8258890590153855828193079 12388335885230783742289619)
    ·
      refine ⟨18582503827846175613434429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12388335885230783742289619 18582503827846175613434429)
      ·
        refine ⟨6968438935442315855037911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18582503827846175613434429 6968438935442315855037911)
        ·
          refine ⟨10452658403163473782556867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6968438935442315855037911 10452658403163473782556867)
          ·
            refine ⟨15678987604745210673835301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10452658403163473782556867 15678987604745210673835301)
            ·
              refine ⟨2939810175889727001344119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15678987604745210673835301 2939810175889727001344119)
              ·
                refine ⟨4409715263834590502016179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939810175889727001344119 4409715263834590502016179)
                ·
                  refine ⟨6614572895751885753024269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4409715263834590502016179 6614572895751885753024269)
                  ·
                    refine ⟨2480464835906957157384101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6614572895751885753024269 2480464835906957157384101)
                    ·
                      refine ⟨465087156732554467009519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2480464835906957157384101 465087156732554467009519)
                      ·
                        rfl

theorem cell23_905754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_905754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905754 prefixEnd_905754 := by exact prefixLift 905754
  have htrace : WordTrace (prefixWord ++ tailWord_905754) baseStart_905754 baseEnd_905754 := by
    simpa [prefixWord, tailWord_905754, baseEnd_905754] using wordTrace_append hprefix tailTrace_905754
  have hstable : (prefixWord ++ tailWord_905754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905754).length < 2 ^ (prefixWord ++ tailWord_905754).sum := by decide
  have hdescent : baseEnd_905754 < baseStart_905754 := by decide
  rcases family_descends (prefixWord ++ tailWord_905754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905787 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7]
def baseStart_905787 : Nat := 118140960795 + 905787 * 2 ^ 59
def prefixEnd_905787 : Nat := 4983230072969 + 3 ^ 40 * 905787 * 2
def baseEnd_905787 : Nat := 465104101594152837896867

theorem tailTrace_905787 : CollatzResearch.WordTrace tailWord_905787 prefixEnd_905787 465104101594152837896867 := by
  unfold tailWord_905787
  simp only [CollatzResearch.WordTrace]
  refine ⟨33036765969495869948723615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22024510646330579965815743 33036765969495869948723615)
  ·
    refine ⟨49555148954243804923085423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33036765969495869948723615 49555148954243804923085423)
    ·
      refine ⟨74332723431365707384628135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49555148954243804923085423 74332723431365707384628135)
      ·
        refine ⟨111499085147048561076942203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74332723431365707384628135 111499085147048561076942203)
        ·
          refine ⟨167248627720572841615413305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111499085147048561076942203 167248627720572841615413305)
          ·
            refine ⟨125436470790429631211559979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167248627720572841615413305 125436470790429631211559979)
            ·
              refine ⟨188154706185644446817339969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125436470790429631211559979 188154706185644446817339969)
              ·
                refine ⟨141116029639233335113004977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188154706185644446817339969 141116029639233335113004977)
                ·
                  refine ⟨105837022229425001334753733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141116029639233335113004977 105837022229425001334753733)
                  ·
                    refine ⟨19844441668017187750266325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105837022229425001334753733 19844441668017187750266325)
                    ·
                      refine ⟨465104101594152837896867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19844441668017187750266325 465104101594152837896867)
                      ·
                        rfl

theorem cell23_905787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_905787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905787 prefixEnd_905787 := by exact prefixLift 905787
  have htrace : WordTrace (prefixWord ++ tailWord_905787) baseStart_905787 baseEnd_905787 := by
    simpa [prefixWord, tailWord_905787, baseEnd_905787] using wordTrace_append hprefix tailTrace_905787
  have hstable : (prefixWord ++ tailWord_905787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905787).length < 2 ^ (prefixWord ++ tailWord_905787).sum := by decide
  have hdescent : baseEnd_905787 < baseStart_905787 := by decide
  rcases family_descends (prefixWord ++ tailWord_905787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905831 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_905831 : Nat := 118140960795 + 905831 * 2 ^ 59
def prefixEnd_905831 : Nat := 4983230072969 + 3 ^ 40 * 905831 * 2
def baseEnd_905831 : Nat := 465126694742950665746665

theorem tailTrace_905831 : CollatzResearch.WordTrace tailWord_905831 prefixEnd_905831 465126694742950665746665 := by
  unfold tailWord_905831
  simp only [CollatzResearch.WordTrace]
  refine ⟨33038370781336465463325347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22025580520890976975550231 33038370781336465463325347)
  ·
    refine ⟨49557556172004698194988021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33038370781336465463325347 49557556172004698194988021)
    ·
      refine ⟨4646020891125440455780127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49557556172004698194988021 4646020891125440455780127)
      ·
        refine ⟨6969031336688160683670191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646020891125440455780127 6969031336688160683670191)
        ·
          refine ⟨10453547005032241025505287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969031336688160683670191 10453547005032241025505287)
          ·
            refine ⟨15680320507548361538257931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10453547005032241025505287 15680320507548361538257931)
            ·
              refine ⟨23520480761322542307386897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680320507548361538257931 23520480761322542307386897)
              ·
                refine ⟨17640360570991906730540173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23520480761322542307386897 17640360570991906730540173)
                ·
                  refine ⟨6615135214121965023952565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17640360570991906730540173 6615135214121965023952565)
                  ·
                    refine ⟨620168926323934220995553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6615135214121965023952565 620168926323934220995553)
                    ·
                      refine ⟨465126694742950665746665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620168926323934220995553 465126694742950665746665)
                      ·
                        rfl

theorem cell23_905831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_905831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905831 prefixEnd_905831 := by exact prefixLift 905831
  have htrace : WordTrace (prefixWord ++ tailWord_905831) baseStart_905831 baseEnd_905831 := by
    simpa [prefixWord, tailWord_905831, baseEnd_905831] using wordTrace_append hprefix tailTrace_905831
  have hstable : (prefixWord ++ tailWord_905831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905831).length < 2 ^ (prefixWord ++ tailWord_905831).sum := by decide
  have hdescent : baseEnd_905831 < baseStart_905831 := by decide
  rcases family_descends (prefixWord ++ tailWord_905831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905861 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_905861 : Nat := 118140960795 + 905861 * 2 ^ 59
def prefixEnd_905861 : Nat := 4983230072969 + 3 ^ 40 * 905861 * 2
def baseEnd_905861 : Nat := 465142099162585548371527

theorem tailTrace_905861 : CollatzResearch.WordTrace tailWord_905861 prefixEnd_905861 465142099162585548371527 := by
  unfold tailWord_905861
  simp only [CollatzResearch.WordTrace]
  refine ⟨33039464971227780586917437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22026309980818520391278291 33039464971227780586917437)
  ·
    refine ⟨12389799364210417720094039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33039464971227780586917437 12389799364210417720094039)
    ·
      refine ⟨18584699046315626580141059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12389799364210417720094039 18584699046315626580141059)
      ·
        refine ⟨27877048569473439870211589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18584699046315626580141059 27877048569473439870211589)
        ·
          refine ⟨5226946606776269975664673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27877048569473439870211589 5226946606776269975664673)
          ·
            refine ⟨3920209955082202481748505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5226946606776269975664673 3920209955082202481748505)
            ·
              refine ⟨2940157466311651861311379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3920209955082202481748505 2940157466311651861311379)
              ·
                refine ⟨4410236199467477791967069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940157466311651861311379 4410236199467477791967069)
                ·
                  refine ⟨1653838574800304171987651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4410236199467477791967069 1653838574800304171987651)
                  ·
                    refine ⟨2480757862200456257981477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653838574800304171987651 2480757862200456257981477)
                    ·
                      refine ⟨465142099162585548371527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2480757862200456257981477 465142099162585548371527)
                      ·
                        rfl

theorem cell23_905861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_905861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905861 prefixEnd_905861 := by exact prefixLift 905861
  have htrace : WordTrace (prefixWord ++ tailWord_905861) baseStart_905861 baseEnd_905861 := by
    simpa [prefixWord, tailWord_905861, baseEnd_905861] using wordTrace_append hprefix tailTrace_905861
  have hstable : (prefixWord ++ tailWord_905861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905861).length < 2 ^ (prefixWord ++ tailWord_905861).sum := by decide
  have hdescent : baseEnd_905861 < baseStart_905861 := by decide
  rcases family_descends (prefixWord ++ tailWord_905861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905888 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 4, 4]
def baseStart_905888 : Nat := 118140960795 + 905888 * 2 ^ 59
def prefixEnd_905888 : Nat := 4983230072969 + 3 ^ 40 * 905888 * 2
def baseEnd_905888 : Nat := 155051987713418980911301

theorem tailTrace_905888 : CollatzResearch.WordTrace tailWord_905888 prefixEnd_905888 155051987713418980911301 := by
  unfold tailWord_905888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16520224871064982099075159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22026966494753309465433545 16520224871064982099075159)
  ·
    refine ⟨24780337306597473148612739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16520224871064982099075159 24780337306597473148612739)
    ·
      refine ⟨37170505959896209722919109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24780337306597473148612739 37170505959896209722919109)
      ·
        refine ⟨6969469867480539323047333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37170505959896209722919109 6969469867480539323047333)
        ·
          refine ⟨1306775600152601123071375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6969469867480539323047333 1306775600152601123071375)
          ·
            refine ⟨1960163400228901684607063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306775600152601123071375 1960163400228901684607063)
            ·
              refine ⟨2940245100343352526910595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960163400228901684607063 2940245100343352526910595)
              ·
                refine ⟨4410367650515028790365893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940245100343352526910595 4410367650515028790365893)
                ·
                  refine ⟨826943934471567898193605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4410367650515028790365893 826943934471567898193605)
                  ·
                    refine ⟨155051987713418980911301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 826943934471567898193605 155051987713418980911301)
                    ·
                      rfl

theorem cell23_905888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_905888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905888 prefixEnd_905888 := by exact prefixLift 905888
  have htrace : WordTrace (prefixWord ++ tailWord_905888) baseStart_905888 baseEnd_905888 := by
    simpa [prefixWord, tailWord_905888, baseEnd_905888] using wordTrace_append hprefix tailTrace_905888
  have hstable : (prefixWord ++ tailWord_905888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905888).length < 2 ^ (prefixWord ++ tailWord_905888).sum := by decide
  have hdescent : baseEnd_905888 < baseStart_905888 := by decide
  rcases family_descends (prefixWord ++ tailWord_905888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905905 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 1, 6]
def baseStart_905905 : Nat := 118140960795 + 905905 * 2 ^ 59
def prefixEnd_905905 : Nat := 4983230072969 + 3 ^ 40 * 905905 * 2
def baseEnd_905905 : Nat := 155054897437127792073775

theorem tailTrace_905905 : CollatzResearch.WordTrace tailWord_905905 prefixEnd_905905 155054897437127792073775 := by
  unfold tailWord_905905
  simp only [CollatzResearch.WordTrace]
  refine ⟨33041069783068376101519169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22027379855378917401012779 33041069783068376101519169)
  ·
    refine ⟨24780802337301282076139377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33041069783068376101519169 24780802337301282076139377)
    ·
      refine ⟨18585601752975961557104533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24780802337301282076139377 18585601752975961557104533)
      ·
        refine ⟨871200082170748197989275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18585601752975961557104533 871200082170748197989275)
        ·
          refine ⟨1306800123256122296983913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871200082170748197989275 1306800123256122296983913)
          ·
            refine ⟨980100092442091722737935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306800123256122296983913 980100092442091722737935)
            ·
              refine ⟨1470150138663137584106903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980100092442091722737935 1470150138663137584106903)
              ·
                refine ⟨2205225207994706376160355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470150138663137584106903 2205225207994706376160355)
                ·
                  refine ⟨3307837811992059564240533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205225207994706376160355 3307837811992059564240533)
                  ·
                    refine ⟨155054897437127792073775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3307837811992059564240533 155054897437127792073775)
                    ·
                      rfl

theorem cell23_905905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_905905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905905 prefixEnd_905905 := by exact prefixLift 905905
  have htrace : WordTrace (prefixWord ++ tailWord_905905) baseStart_905905 baseEnd_905905 := by
    simpa [prefixWord, tailWord_905905, baseEnd_905905] using wordTrace_append hprefix tailTrace_905905
  have hstable : (prefixWord ++ tailWord_905905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905905).length < 2 ^ (prefixWord ++ tailWord_905905).sum := by decide
  have hdescent : baseEnd_905905 < baseStart_905905 := by decide
  rcases family_descends (prefixWord ++ tailWord_905905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905928 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_905928 : Nat := 118140960795 + 905928 * 2 ^ 59
def prefixEnd_905928 : Nat := 4983230072969 + 3 ^ 40 * 905928 * 2
def baseEnd_905928 : Nat := 465176502366436786233719

theorem tailTrace_905928 : CollatzResearch.WordTrace tailWord_905928 prefixEnd_905928 465176502366436786233719 := by
  unfold tailWord_905928
  simp only [CollatzResearch.WordTrace]
  refine ⟨16520954330992525514803219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22027939107990034019737625 16520954330992525514803219)
  ·
    refine ⟨24781431496488788272204829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16520954330992525514803219 24781431496488788272204829)
    ·
      refine ⟨9293036811183295602076811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24781431496488788272204829 9293036811183295602076811)
      ·
        refine ⟨13939555216774943403115217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9293036811183295602076811 13939555216774943403115217)
        ·
          refine ⟨10454666412581207552336413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13939555216774943403115217 10454666412581207552336413)
          ·
            refine ⟨3920499904717952832126155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10454666412581207552336413 3920499904717952832126155)
            ·
              refine ⟨5880749857076929248189233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920499904717952832126155 5880749857076929248189233)
              ·
                refine ⟨4410562392807696936141925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880749857076929248189233 4410562392807696936141925)
                ·
                  refine ⟨826980448651443175526611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4410562392807696936141925 826980448651443175526611)
                  ·
                    refine ⟨1240470672977164763289917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 826980448651443175526611 1240470672977164763289917)
                    ·
                      refine ⟨465176502366436786233719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1240470672977164763289917 465176502366436786233719)
                      ·
                        rfl

theorem cell23_905928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_905928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905928 prefixEnd_905928 := by exact prefixLift 905928
  have htrace : WordTrace (prefixWord ++ tailWord_905928) baseStart_905928 baseEnd_905928 := by
    simpa [prefixWord, tailWord_905928, baseEnd_905928] using wordTrace_append hprefix tailTrace_905928
  have hstable : (prefixWord ++ tailWord_905928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905928).length < 2 ^ (prefixWord ++ tailWord_905928).sum := by decide
  have hdescent : baseEnd_905928 < baseStart_905928 := by decide
  rcases family_descends (prefixWord ++ tailWord_905928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905968 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 1, 4, 2]
def baseStart_905968 : Nat := 118140960795 + 905968 * 2 ^ 59
def prefixEnd_905968 : Nat := 4983230072969 + 3 ^ 40 * 905968 * 2
def baseEnd_905968 : Nat := 465197041592616629733535

theorem tailTrace_905968 : CollatzResearch.WordTrace tailWord_905968 prefixEnd_905968 465197041592616629733535 := by
  unfold tailWord_905968
  simp only [CollatzResearch.WordTrace]
  refine ⟨16521683790920068930531279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22028911721226758574041705 16521683790920068930531279)
  ·
    refine ⟨24782525686380103395796919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16521683790920068930531279 24782525686380103395796919)
    ·
      refine ⟨37173788529570155093695379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24782525686380103395796919 37173788529570155093695379)
      ·
        refine ⟨55760682794355232640543069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37173788529570155093695379 55760682794355232640543069)
        ·
          refine ⟨20910256047883212240203651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55760682794355232640543069 20910256047883212240203651)
          ·
            refine ⟨31365384071824818360305477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20910256047883212240203651 31365384071824818360305477)
            ·
              refine ⟨5881009513467153442557277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31365384071824818360305477 5881009513467153442557277)
              ·
                refine ⟨2205378567550182540958979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5881009513467153442557277 2205378567550182540958979)
                ·
                  refine ⟨3308067851325273811438469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205378567550182540958979 3308067851325273811438469)
                  ·
                    refine ⟨620262722123488839644713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3308067851325273811438469 620262722123488839644713)
                    ·
                      refine ⟨465197041592616629733535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620262722123488839644713 465197041592616629733535)
                      ·
                        rfl

theorem cell23_905968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 4, 2].length) (baseStart_905968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_905968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_905968 prefixEnd_905968 := by exact prefixLift 905968
  have htrace : WordTrace (prefixWord ++ tailWord_905968) baseStart_905968 baseEnd_905968 := by
    simpa [prefixWord, tailWord_905968, baseEnd_905968] using wordTrace_append hprefix tailTrace_905968
  have hstable : (prefixWord ++ tailWord_905968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905968).length < 2 ^ (prefixWord ++ tailWord_905968).sum := by decide
  have hdescent : baseEnd_905968 < baseStart_905968 := by decide
  rcases family_descends (prefixWord ++ tailWord_905968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906018 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_906018 : Nat := 118140960795 + 906018 * 2 ^ 59
def prefixEnd_906018 : Nat := 4983230072969 + 3 ^ 40 * 906018 * 2
def baseEnd_906018 : Nat := 465222715625341434108305

theorem tailTrace_906018 : CollatzResearch.WordTrace tailWord_906018 prefixEnd_906018 465222715625341434108305 := by
  unfold tailWord_906018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8261297807914749100095677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22030127487772664266921805 8261297807914749100095677)
  ·
    refine ⟨3097986677968030912535879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8261297807914749100095677 3097986677968030912535879)
    ·
      refine ⟨4646980016952046368803819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3097986677968030912535879 4646980016952046368803819)
      ·
        refine ⟨6970470025428069553205729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646980016952046368803819 6970470025428069553205729)
        ·
          refine ⟨5227852519071052164904297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6970470025428069553205729 5227852519071052164904297)
          ·
            refine ⟨3920889389303289123678223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227852519071052164904297 3920889389303289123678223)
            ·
              refine ⟨5881334083954933685517335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920889389303289123678223 5881334083954933685517335)
              ·
                refine ⟨8822001125932400528276003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881334083954933685517335 8822001125932400528276003)
                ·
                  refine ⟨13233001688898600792414005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822001125932400528276003 13233001688898600792414005)
                  ·
                    refine ⟨1240593908334243824288813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13233001688898600792414005 1240593908334243824288813)
                    ·
                      refine ⟨465222715625341434108305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1240593908334243824288813 465222715625341434108305)
                      ·
                        rfl

theorem cell23_906018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_906018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906018 prefixEnd_906018 := by exact prefixLift 906018
  have htrace : WordTrace (prefixWord ++ tailWord_906018) baseStart_906018 baseEnd_906018 := by
    simpa [prefixWord, tailWord_906018, baseEnd_906018] using wordTrace_append hprefix tailTrace_906018
  have hstable : (prefixWord ++ tailWord_906018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906018).length < 2 ^ (prefixWord ++ tailWord_906018).sum := by decide
  have hdescent : baseEnd_906018 < baseStart_906018 := by decide
  rcases family_descends (prefixWord ++ tailWord_906018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906021 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_906021 : Nat := 118140960795 + 906021 * 2 ^ 59
def prefixEnd_906021 : Nat := 4983230072969 + 3 ^ 40 * 906021 * 2
def baseEnd_906021 : Nat := 155074752022434974123597

theorem tailTrace_906021 : CollatzResearch.WordTrace tailWord_906021 prefixEnd_906021 155074752022434974123597 := by
  unfold tailWord_906021
  simp only [CollatzResearch.WordTrace]
  refine ⟨33045300650648127912741917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22030200433765418608494611 33045300650648127912741917)
  ·
    refine ⟨12391987743993047967278219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33045300650648127912741917 12391987743993047967278219)
    ·
      refine ⟨18587981615989571950917329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12391987743993047967278219 18587981615989571950917329)
      ·
        refine ⟨13940986211992178963187997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18587981615989571950917329 13940986211992178963187997)
        ·
          refine ⟨5227869829497067111195499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13940986211992178963187997 5227869829497067111195499)
          ·
            refine ⟨7841804744245600666793249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227869829497067111195499 7841804744245600666793249)
            ·
              refine ⟨5881353558184200500094937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7841804744245600666793249 5881353558184200500094937)
              ·
                refine ⟨4411015168638150375071203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5881353558184200500094937 4411015168638150375071203)
                ·
                  refine ⟨6616522752957225562606805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411015168638150375071203 6616522752957225562606805)
                  ·
                    refine ⟨155074752022434974123597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6616522752957225562606805 155074752022434974123597)
                    ·
                      rfl

theorem cell23_906021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_906021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906021 prefixEnd_906021 := by exact prefixLift 906021
  have htrace : WordTrace (prefixWord ++ tailWord_906021) baseStart_906021 baseEnd_906021 := by
    simpa [prefixWord, tailWord_906021, baseEnd_906021] using wordTrace_append hprefix tailTrace_906021
  have hstable : (prefixWord ++ tailWord_906021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906021).length < 2 ^ (prefixWord ++ tailWord_906021).sum := by decide
  have hdescent : baseEnd_906021 < baseStart_906021 := by decide
  rcases family_descends (prefixWord ++ tailWord_906021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906028 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 2, 5, 2]
def baseStart_906028 : Nat := 118140960795 + 906028 * 2 ^ 59
def prefixEnd_906028 : Nat := 4983230072969 + 3 ^ 40 * 906028 * 2
def baseEnd_906028 : Nat := 465227850431886394983259

theorem tailTrace_906028 : CollatzResearch.WordTrace tailWord_906028 prefixEnd_906028 465227850431886394983259 := by
  unfold tailWord_906028
  simp only [CollatzResearch.WordTrace]
  refine ⟨16522777980811384054123369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22030370641081845405497825 16522777980811384054123369)
  ·
    refine ⟨12392083485608538040592527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16522777980811384054123369 12392083485608538040592527)
    ·
      refine ⟨18588125228412807060888791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12392083485608538040592527 18588125228412807060888791)
      ·
        refine ⟨27882187842619210591333187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18588125228412807060888791 27882187842619210591333187)
        ·
          refine ⟨41823281763928815886999781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27882187842619210591333187 41823281763928815886999781)
          ·
            refine ⟨7841865330736652978812459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41823281763928815886999781 7841865330736652978812459)
            ·
              refine ⟨11762797996104979468218689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841865330736652978812459 11762797996104979468218689)
              ·
                refine ⟨8822098497078734601164017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11762797996104979468218689 8822098497078734601164017)
                ·
                  refine ⟨6616573872809050950873013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8822098497078734601164017 6616573872809050950873013)
                  ·
                    refine ⟨620303800575848526644345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6616573872809050950873013 620303800575848526644345)
                    ·
                      refine ⟨465227850431886394983259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620303800575848526644345 465227850431886394983259)
                      ·
                        rfl

theorem cell23_906028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_906028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906028 prefixEnd_906028 := by exact prefixLift 906028
  have htrace : WordTrace (prefixWord ++ tailWord_906028) baseStart_906028 baseEnd_906028 := by
    simpa [prefixWord, tailWord_906028, baseEnd_906028] using wordTrace_append hprefix tailTrace_906028
  have hstable : (prefixWord ++ tailWord_906028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906028).length < 2 ^ (prefixWord ++ tailWord_906028).sum := by decide
  have hdescent : baseEnd_906028 < baseStart_906028 := by decide
  rcases family_descends (prefixWord ++ tailWord_906028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906119 : List Nat := [1, 1, 4, 2, 3, 2, 3, 2, 1, 4]
def baseStart_906119 : Nat := 118140960795 + 906119 * 2 ^ 59
def prefixEnd_906119 : Nat := 4983230072969 + 3 ^ 40 * 906119 * 2
def baseEnd_906119 : Nat := 155091525723815179648447

theorem tailTrace_906119 : CollatzResearch.WordTrace tailWord_906119 prefixEnd_906119 155091525723815179648447 := by
  unfold tailWord_906119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33048875004293090649809411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22032583336195393766539607 33048875004293090649809411)
  ·
    refine ⟨49573312506439635974714117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33048875004293090649809411 49573312506439635974714117)
    ·
      refine ⟨9294996094957431745258897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49573312506439635974714117 9294996094957431745258897)
      ·
        refine ⟨6971247071218073808944173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9294996094957431745258897 6971247071218073808944173)
        ·
          refine ⟨2614217651706777678354065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6971247071218073808944173 2614217651706777678354065)
          ·
            refine ⟨1960663238780083258765549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614217651706777678354065 1960663238780083258765549)
            ·
              refine ⟨735248714542531222037081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1960663238780083258765549 735248714542531222037081)
              ·
                refine ⟨551436535906898416527811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735248714542531222037081 551436535906898416527811)
                ·
                  refine ⟨827154803860347624791717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551436535906898416527811 827154803860347624791717)
                  ·
                    refine ⟨155091525723815179648447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827154803860347624791717 155091525723815179648447)
                    ·
                      rfl

theorem cell23_906119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_906119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906119 prefixEnd_906119 := by exact prefixLift 906119
  have htrace : WordTrace (prefixWord ++ tailWord_906119) baseStart_906119 baseEnd_906119 := by
    simpa [prefixWord, tailWord_906119, baseEnd_906119] using wordTrace_append hprefix tailTrace_906119
  have hstable : (prefixWord ++ tailWord_906119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906119).length < 2 ^ (prefixWord ++ tailWord_906119).sum := by decide
  have hdescent : baseEnd_906119 < baseStart_906119 := by decide
  rcases family_descends (prefixWord ++ tailWord_906119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906135 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 4, 3, 2]
def baseStart_906135 : Nat := 118140960795 + 906135 * 2 ^ 59
def prefixEnd_906135 : Nat := 4983230072969 + 3 ^ 40 * 906135 * 2
def baseEnd_906135 : Nat := 465282792861917476345267

theorem tailTrace_906135 : CollatzResearch.WordTrace tailWord_906135 prefixEnd_906135 465282792861917476345267 := by
  unfold tailWord_906135
  simp only [CollatzResearch.WordTrace]
  refine ⟨33049458572235125382391859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22032972381490083588261239 33049458572235125382391859)
  ·
    refine ⟨49574187858352688073587789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33049458572235125382391859 49574187858352688073587789)
    ·
      refine ⟨18590320446882258027595421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49574187858352688073587789 18590320446882258027595421)
      ·
        refine ⟨6971370167580846760348283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18590320446882258027595421 6971370167580846760348283)
        ·
          refine ⟨10457055251371270140522425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6971370167580846760348283 10457055251371270140522425)
          ·
            refine ⟨7842791438528452605391819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10457055251371270140522425 7842791438528452605391819)
            ·
              refine ⟨11764187157792678908087729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842791438528452605391819 11764187157792678908087729)
              ·
                refine ⟨8823140368344509181065797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11764187157792678908087729 8823140368344509181065797)
                ·
                  refine ⟨1654338819064595471449837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8823140368344509181065797 1654338819064595471449837)
                  ·
                    refine ⟨620377057149223301793689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1654338819064595471449837 620377057149223301793689)
                    ·
                      refine ⟨465282792861917476345267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620377057149223301793689 465282792861917476345267)
                      ·
                        rfl

theorem cell23_906135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_906135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906135 prefixEnd_906135 := by exact prefixLift 906135
  have htrace : WordTrace (prefixWord ++ tailWord_906135) baseStart_906135 baseEnd_906135 := by
    simpa [prefixWord, tailWord_906135, baseEnd_906135] using wordTrace_append hprefix tailTrace_906135
  have hstable : (prefixWord ++ tailWord_906135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906135).length < 2 ^ (prefixWord ++ tailWord_906135).sum := by decide
  have hdescent : baseEnd_906135 < baseStart_906135 := by decide
  rcases family_descends (prefixWord ++ tailWord_906135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906145 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 3, 5]
def baseStart_906145 : Nat := 118140960795 + 906145 * 2 ^ 59
def prefixEnd_906145 : Nat := 4983230072969 + 3 ^ 40 * 906145 * 2
def baseEnd_906145 : Nat := 155095975889487479073407

theorem tailTrace_906145 : CollatzResearch.WordTrace tailWord_906145 prefixEnd_906145 155095975889487479073407 := by
  unfold tailWord_906145
  simp only [CollatzResearch.WordTrace]
  refine ⟨33049823302198897090255889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22033215534799264726837259 33049823302198897090255889)
  ·
    refine ⟨24787367476649172817691917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33049823302198897090255889 24787367476649172817691917)
    ·
      refine ⟨9295262803743439806634469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24787367476649172817691917 9295262803743439806634469)
      ·
        refine ⟨1742861775701894963743963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9295262803743439806634469 1742861775701894963743963)
        ·
          refine ⟨2614292663552842445615945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742861775701894963743963 2614292663552842445615945)
          ·
            refine ⟨1960719497664631834211959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614292663552842445615945 1960719497664631834211959)
            ·
              refine ⟨2941079246496947751317939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960719497664631834211959 2941079246496947751317939)
              ·
                refine ⟨4411618869745421626976909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941079246496947751317939 4411618869745421626976909)
                ·
                  refine ⟨1654357076154533110116341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4411618869745421626976909 1654357076154533110116341)
                  ·
                    refine ⟨155095975889487479073407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1654357076154533110116341 155095975889487479073407)
                    ·
                      rfl

theorem cell23_906145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_906145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906145 prefixEnd_906145 := by exact prefixLift 906145
  have htrace : WordTrace (prefixWord ++ tailWord_906145) baseStart_906145 baseEnd_906145 := by
    simpa [prefixWord, tailWord_906145, baseEnd_906145] using wordTrace_append hprefix tailTrace_906145
  have hstable : (prefixWord ++ tailWord_906145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906145).length < 2 ^ (prefixWord ++ tailWord_906145).sum := by decide
  have hdescent : baseEnd_906145 < baseStart_906145 := by decide
  rcases family_descends (prefixWord ++ tailWord_906145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906166 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_906166 : Nat := 118140960795 + 906166 * 2 ^ 59
def prefixEnd_906166 : Nat := 4983230072969 + 3 ^ 40 * 906166 * 2
def baseEnd_906166 : Nat := 51699856751356317228625

theorem tailTrace_906166 : CollatzResearch.WordTrace tailWord_906166 prefixEnd_906166 51699856751356317228625 := by
  unfold tailWord_906166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065661827195176104798147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22033726156748545117846901 2065661827195176104798147)
  ·
    refine ⟨3098492740792764157197221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2065661827195176104798147 3098492740792764157197221)
    ·
      refine ⟨580967388898643279474479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3098492740792764157197221 580967388898643279474479)
      ·
        refine ⟨871451083347964919211719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580967388898643279474479 871451083347964919211719)
        ·
          refine ⟨1307176625021947378817579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871451083347964919211719 1307176625021947378817579)
          ·
            refine ⟨1960764937532921068226369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307176625021947378817579 1960764937532921068226369)
            ·
              refine ⟨1470573703149690801169777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960764937532921068226369 1470573703149690801169777)
              ·
                refine ⟨1102930277362268100877333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470573703149690801169777 1102930277362268100877333)
                ·
                  refine ⟨51699856751356317228625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1102930277362268100877333 51699856751356317228625)
                  ·
                    rfl

theorem cell23_906166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_906166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906166 prefixEnd_906166 := by exact prefixLift 906166
  have htrace : WordTrace (prefixWord ++ tailWord_906166) baseStart_906166 baseEnd_906166 := by
    simpa [prefixWord, tailWord_906166, baseEnd_906166] using wordTrace_append hprefix tailTrace_906166
  have hstable : (prefixWord ++ tailWord_906166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906166).length < 2 ^ (prefixWord ++ tailWord_906166).sum := by decide
  have hdescent : baseEnd_906166 < baseStart_906166 := by decide
  rcases family_descends (prefixWord ++ tailWord_906166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906176 : List Nat := [2, 1, 1, 2, 3, 5, 2, 2, 1, 1, 3]
def baseStart_906176 : Nat := 118140960795 + 906176 * 2 ^ 59
def prefixEnd_906176 : Nat := 4983230072969 + 3 ^ 40 * 906176 * 2
def baseEnd_906176 : Nat := 465303845568751815932579

theorem tailTrace_906176 : CollatzResearch.WordTrace tailWord_906176 prefixEnd_906176 465303845568751815932579 := by
  unfold tailWord_906176
  simp only [CollatzResearch.WordTrace]
  refine ⟨16525476982543294692317191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22033969310057726256422921 16525476982543294692317191)
  ·
    refine ⟨24788215473814942038475787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16525476982543294692317191 24788215473814942038475787)
    ·
      refine ⟨37182323210722413057713681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24788215473814942038475787 37182323210722413057713681)
      ·
        refine ⟨27886742408041809793285261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37182323210722413057713681 27886742408041809793285261)
        ·
          refine ⟨10457528403015678672481973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27886742408041809793285261 10457528403015678672481973)
          ·
            refine ⟨980393287782719875545185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10457528403015678672481973 980393287782719875545185)
            ·
              refine ⟨735294965837039906658889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980393287782719875545185 735294965837039906658889)
              ·
                refine ⟨551471224377779929994167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735294965837039906658889 551471224377779929994167)
                ·
                  refine ⟨827206836566669894991251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551471224377779929994167 827206836566669894991251)
                  ·
                    refine ⟨1240810254850004842486877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 827206836566669894991251 1240810254850004842486877)
                    ·
                      refine ⟨465303845568751815932579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1240810254850004842486877 465303845568751815932579)
                      ·
                        rfl

theorem cell23_906176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_906176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906176 prefixEnd_906176 := by exact prefixLift 906176
  have htrace : WordTrace (prefixWord ++ tailWord_906176) baseStart_906176 baseEnd_906176 := by
    simpa [prefixWord, tailWord_906176, baseEnd_906176] using wordTrace_append hprefix tailTrace_906176
  have hstable : (prefixWord ++ tailWord_906176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906176).length < 2 ^ (prefixWord ++ tailWord_906176).sum := by decide
  have hdescent : baseEnd_906176 < baseStart_906176 := by decide
  rcases family_descends (prefixWord ++ tailWord_906176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906226 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_906226 : Nat := 118140960795 + 906226 * 2 ^ 59
def prefixEnd_906226 : Nat := 4983230072969 + 3 ^ 40 * 906226 * 2
def baseEnd_906226 : Nat := 155109839867158873435783

theorem tailTrace_906226 : CollatzResearch.WordTrace tailWord_906226 prefixEnd_906226 155109839867158873435783 := by
  unfold tailWord_906226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263194403726361980988633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22035185076603631949303021 8263194403726361980988633)
  ·
    refine ⟨6197395802794771485741475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8263194403726361980988633 6197395802794771485741475)
    ·
      refine ⟨9296093704192157228612213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197395802794771485741475 9296093704192157228612213)
      ·
        refine ⟨871508784768014740182395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9296093704192157228612213 871508784768014740182395)
        ·
          refine ⟨1307263177152022110273593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871508784768014740182395 1307263177152022110273593)
          ·
            refine ⟨980447382864016582705195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307263177152022110273593 980447382864016582705195)
            ·
              refine ⟨1470671074296024874057793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980447382864016582705195 1470671074296024874057793)
              ·
                refine ⟨1103003305722018655543345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470671074296024874057793 1103003305722018655543345)
                ·
                  refine ⟨827252479291513991657509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1103003305722018655543345 827252479291513991657509)
                  ·
                    refine ⟨155109839867158873435783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827252479291513991657509 155109839867158873435783)
                    ·
                      rfl

theorem cell23_906226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_906226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906226 prefixEnd_906226 := by exact prefixLift 906226
  have htrace : WordTrace (prefixWord ++ tailWord_906226) baseStart_906226 baseEnd_906226 := by
    simpa [prefixWord, tailWord_906226, baseEnd_906226] using wordTrace_append hprefix tailTrace_906226
  have hstable : (prefixWord ++ tailWord_906226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906226).length < 2 ^ (prefixWord ++ tailWord_906226).sum := by decide
  have hdescent : baseEnd_906226 < baseStart_906226 := by decide
  rcases family_descends (prefixWord ++ tailWord_906226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906255 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 7, 4, 2]
def baseStart_906255 : Nat := 118140960795 + 906255 * 2 ^ 59
def prefixEnd_906255 : Nat := 4983230072969 + 3 ^ 40 * 906255 * 2
def baseEnd_906255 : Nat := 465344410540457006844715

theorem tailTrace_906255 : CollatzResearch.WordTrace tailWord_906255 prefixEnd_906255 465344410540457006844715 := by
  unfold tailWord_906255
  simp only [CollatzResearch.WordTrace]
  refine ⟨33053835331800385876760219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22035890221200257251173479 33053835331800385876760219)
  ·
    refine ⟨49580752997700578815140329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33053835331800385876760219 49580752997700578815140329)
    ·
      refine ⟨37185564748275434111355247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49580752997700578815140329 37185564748275434111355247)
      ·
        refine ⟨55778347122413151167032871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37185564748275434111355247 55778347122413151167032871)
        ·
          refine ⟨83667520683619726750549307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55778347122413151167032871 83667520683619726750549307)
          ·
            refine ⟨125501281025429590125823961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83667520683619726750549307 125501281025429590125823961)
            ·
              refine ⟨94125960769072192594367971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125501281025429590125823961 94125960769072192594367971)
              ·
                refine ⟨141188941153608288891551957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94125960769072192594367971 141188941153608288891551957)
                ·
                  refine ⟨3309115808287694270895749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141188941153608288891551957 3309115808287694270895749)
                  ·
                    refine ⟨620459214053942675792953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309115808287694270895749 620459214053942675792953)
                    ·
                      refine ⟨465344410540457006844715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620459214053942675792953 465344410540457006844715)
                      ·
                        rfl

theorem cell23_906255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4, 2].length) (baseStart_906255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906255 prefixEnd_906255 := by exact prefixLift 906255
  have htrace : WordTrace (prefixWord ++ tailWord_906255) baseStart_906255 baseEnd_906255 := by
    simpa [prefixWord, tailWord_906255, baseEnd_906255] using wordTrace_append hprefix tailTrace_906255
  have hstable : (prefixWord ++ tailWord_906255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906255).length < 2 ^ (prefixWord ++ tailWord_906255).sum := by decide
  have hdescent : baseEnd_906255 < baseStart_906255 := by decide
  rcases family_descends (prefixWord ++ tailWord_906255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906275 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5]
def baseStart_906275 : Nat := 118140960795 + 906275 * 2 ^ 59
def prefixEnd_906275 : Nat := 4983230072969 + 3 ^ 40 * 906275 * 2
def baseEnd_906275 : Nat := 465354680153546928594623

theorem tailTrace_906275 : CollatzResearch.WordTrace tailWord_906275 prefixEnd_906275 465354680153546928594623 := by
  unfold tailWord_906275
  simp only [CollatzResearch.WordTrace]
  refine ⟨33054564791727929292488279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22036376527818619528325519 33054564791727929292488279)
  ·
    refine ⟨49581847187591893938732419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33054564791727929292488279 49581847187591893938732419)
    ·
      refine ⟨74372770781387840908098629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49581847187591893938732419 74372770781387840908098629)
      ·
        refine ⟨13944894521510220170268493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74372770781387840908098629 13944894521510220170268493)
        ·
          refine ⟨5229335445566332563850685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13944894521510220170268493 5229335445566332563850685)
          ·
            refine ⟨1961000792087374711444007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5229335445566332563850685 1961000792087374711444007)
            ·
              refine ⟨2941501188131062067166011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961000792087374711444007 2941501188131062067166011)
              ·
                refine ⟨4412251782196593100749017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941501188131062067166011 4412251782196593100749017)
                ·
                  refine ⟨3309188836647444825561763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412251782196593100749017 3309188836647444825561763)
                  ·
                    refine ⟨4963783254971167238342645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3309188836647444825561763 4963783254971167238342645)
                    ·
                      refine ⟨465354680153546928594623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4963783254971167238342645 465354680153546928594623)
                      ·
                        rfl

theorem cell23_906275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_906275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906275 prefixEnd_906275 := by exact prefixLift 906275
  have htrace : WordTrace (prefixWord ++ tailWord_906275) baseStart_906275 baseEnd_906275 := by
    simpa [prefixWord, tailWord_906275, baseEnd_906275] using wordTrace_append hprefix tailTrace_906275
  have hstable : (prefixWord ++ tailWord_906275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906275).length < 2 ^ (prefixWord ++ tailWord_906275).sum := by decide
  have hdescent : baseEnd_906275 < baseStart_906275 := by decide
  rcases family_descends (prefixWord ++ tailWord_906275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906288 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_906288 : Nat := 118140960795 + 906288 * 2 ^ 59
def prefixEnd_906288 : Nat := 4983230072969 + 3 ^ 40 * 906288 * 2
def baseEnd_906288 : Nat := 465361355402055377732063

theorem tailTrace_906288 : CollatzResearch.WordTrace tailWord_906288 prefixEnd_906288 465361355402055377732063 := by
  unfold tailWord_906288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16527519470340416256355759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22036692627120555008474345 16527519470340416256355759)
  ·
    refine ⟨24791279205510624384533639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16527519470340416256355759 24791279205510624384533639)
    ·
      refine ⟨37186918808265936576800459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24791279205510624384533639 37186918808265936576800459)
      ·
        refine ⟨55780378212398904865200689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37186918808265936576800459 55780378212398904865200689)
        ·
          refine ⟨41835283659299178648900517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55780378212398904865200689 41835283659299178648900517)
          ·
            refine ⟨7844115686118595996668847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41835283659299178648900517 7844115686118595996668847)
            ·
              refine ⟨11766173529177893995003271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7844115686118595996668847 11766173529177893995003271)
              ·
                refine ⟨17649260293766840992504907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11766173529177893995003271 17649260293766840992504907)
                ·
                  refine ⟨26473890440650261488757361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17649260293766840992504907 26473890440650261488757361)
                  ·
                    refine ⟨19855417830487696116568021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26473890440650261488757361 19855417830487696116568021)
                    ·
                      refine ⟨465361355402055377732063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19855417830487696116568021 465361355402055377732063)
                      ·
                        rfl

theorem cell23_906288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_906288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906288 prefixEnd_906288 := by exact prefixLift 906288
  have htrace : WordTrace (prefixWord ++ tailWord_906288) baseStart_906288 baseEnd_906288 := by
    simpa [prefixWord, tailWord_906288, baseEnd_906288] using wordTrace_append hprefix tailTrace_906288
  have hstable : (prefixWord ++ tailWord_906288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906288).length < 2 ^ (prefixWord ++ tailWord_906288).sum := by decide
  have hdescent : baseEnd_906288 < baseStart_906288 := by decide
  rcases family_descends (prefixWord ++ tailWord_906288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906289 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 2, 2, 2]
def baseStart_906289 : Nat := 118140960795 + 906289 * 2 ^ 59
def prefixEnd_906289 : Nat := 4983230072969 + 3 ^ 40 * 906289 * 2
def baseEnd_906289 : Nat := 465361868882709873819559

theorem tailTrace_906289 : CollatzResearch.WordTrace tailWord_906289 prefixEnd_906289 465361868882709873819559 := by
  unfold tailWord_906289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055075413677209683497921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22036716942451473122331947 33055075413677209683497921)
  ·
    refine ⟨24791306560257907262623441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33055075413677209683497921 24791306560257907262623441)
    ·
      refine ⟨18593479920193430446967581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24791306560257907262623441 18593479920193430446967581)
      ·
        refine ⟨6972554970072536417612843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18593479920193430446967581 6972554970072536417612843)
        ·
          refine ⟨10458832455108804626419265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972554970072536417612843 10458832455108804626419265)
          ·
            refine ⟨7844124341331603469814449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10458832455108804626419265 7844124341331603469814449)
            ·
              refine ⟨5883093255998702602360837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7844124341331603469814449 5883093255998702602360837)
              ·
                refine ⟨1103079985499756737942657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5883093255998702602360837 1103079985499756737942657)
                ·
                  refine ⟨827309989124817553456993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1103079985499756737942657 827309989124817553456993)
                  ·
                    refine ⟨620482491843613165092745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 827309989124817553456993 620482491843613165092745)
                    ·
                      refine ⟨465361868882709873819559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620482491843613165092745 465361868882709873819559)
                      ·
                        rfl

theorem cell23_906289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_906289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906289 prefixEnd_906289 := by exact prefixLift 906289
  have htrace : WordTrace (prefixWord ++ tailWord_906289) baseStart_906289 baseEnd_906289 := by
    simpa [prefixWord, tailWord_906289, baseEnd_906289] using wordTrace_append hprefix tailTrace_906289
  have hstable : (prefixWord ++ tailWord_906289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906289).length < 2 ^ (prefixWord ++ tailWord_906289).sum := by decide
  have hdescent : baseEnd_906289 < baseStart_906289 := by decide
  rcases family_descends (prefixWord ++ tailWord_906289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906346 : List Nat := [3, 1, 3, 2, 2, 3, 2, 2, 5]
def baseStart_906346 : Nat := 118140960795 + 906346 * 2 ^ 59
def prefixEnd_906346 : Nat := 4983230072969 + 3 ^ 40 * 906346 * 2
def baseEnd_906346 : Nat := 51710126364446238978533

theorem tailTrace_906346 : CollatzResearch.WordTrace tailWord_906346 prefixEnd_906346 51710126364446238978533 := by
  unfold tailWord_906346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8264288593617677104580723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22038102916313805612215261 8264288593617677104580723)
  ·
    refine ⟨12396432890426515656871085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8264288593617677104580723 12396432890426515656871085)
    ·
      refine ⟨4648662333909943371326657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12396432890426515656871085 4648662333909943371326657)
      ·
        refine ⟨3486496750432457528494993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4648662333909943371326657 3486496750432457528494993)
        ·
          refine ⟨2614872562824343146371245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3486496750432457528494993 2614872562824343146371245)
          ·
            refine ⟨980577211059128679889217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2614872562824343146371245 980577211059128679889217)
            ·
              refine ⟨735432908294346509916913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980577211059128679889217 735432908294346509916913)
              ·
                refine ⟨551574681220759882437685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735432908294346509916913 551574681220759882437685)
                ·
                  refine ⟨51710126364446238978533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 551574681220759882437685 51710126364446238978533)
                  ·
                    rfl

theorem cell23_906346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_906346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906346 prefixEnd_906346 := by exact prefixLift 906346
  have htrace : WordTrace (prefixWord ++ tailWord_906346) baseStart_906346 baseEnd_906346 := by
    simpa [prefixWord, tailWord_906346, baseEnd_906346] using wordTrace_append hprefix tailTrace_906346
  have hstable : (prefixWord ++ tailWord_906346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906346).length < 2 ^ (prefixWord ++ tailWord_906346).sum := by decide
  have hdescent : baseEnd_906346 < baseStart_906346 := by decide
  rcases family_descends (prefixWord ++ tailWord_906346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906355 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 9, 4]
def baseStart_906355 : Nat := 118140960795 + 906355 * 2 ^ 59
def prefixEnd_906355 : Nat := 4983230072969 + 3 ^ 40 * 906355 * 2
def baseEnd_906355 : Nat := 155131919535302205198085

theorem tailTrace_906355 : CollatzResearch.WordTrace tailWord_906355 prefixEnd_906355 155131919535302205198085 := by
  unfold tailWord_906355
  simp only [CollatzResearch.WordTrace]
  refine ⟨33057482631438102955400519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22038321754292068636933679 33057482631438102955400519)
  ·
    refine ⟨49586223947157154433100779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33057482631438102955400519 49586223947157154433100779)
    ·
      refine ⟨74379335920735731649651169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49586223947157154433100779 74379335920735731649651169)
      ·
        refine ⟨55784501940551798737238377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74379335920735731649651169 55784501940551798737238377)
        ·
          refine ⟨41838376455413849052928783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55784501940551798737238377 41838376455413849052928783)
          ·
            refine ⟨62757564683120773579393175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41838376455413849052928783 62757564683120773579393175)
            ·
              refine ⟨94136347024681160369089763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62757564683120773579393175 94136347024681160369089763)
              ·
                refine ⟨141204520537021740553634645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94136347024681160369089763 141204520537021740553634645)
                ·
                  refine ⟨827370237521611761056453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 141204520537021740553634645 827370237521611761056453)
                  ·
                    refine ⟨155131919535302205198085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827370237521611761056453 155131919535302205198085)
                    ·
                      rfl

theorem cell23_906355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 4].length) (baseStart_906355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906355 prefixEnd_906355 := by exact prefixLift 906355
  have htrace : WordTrace (prefixWord ++ tailWord_906355) baseStart_906355 baseEnd_906355 := by
    simpa [prefixWord, tailWord_906355, baseEnd_906355] using wordTrace_append hprefix tailTrace_906355
  have hstable : (prefixWord ++ tailWord_906355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906355).length < 2 ^ (prefixWord ++ tailWord_906355).sum := by decide
  have hdescent : baseEnd_906355 < baseStart_906355 := by decide
  rcases family_descends (prefixWord ++ tailWord_906355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906372 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_906372 : Nat := 118140960795 + 906372 * 2 ^ 59
def prefixEnd_906372 : Nat := 4983230072969 + 3 ^ 40 * 906372 * 2
def baseEnd_906372 : Nat := 155134829259011016360559

theorem tailTrace_906372 : CollatzResearch.WordTrace tailWord_906372 prefixEnd_906372 155134829259011016360559 := by
  unfold tailWord_906372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16529051336188257429384685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22038735114917676572512913 16529051336188257429384685)
  ·
    refine ⟨6198394251070596536019257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16529051336188257429384685 6198394251070596536019257)
    ·
      refine ⟨4648795688302947402014443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6198394251070596536019257 4648795688302947402014443)
      ·
        refine ⟨6973193532454421103021665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648795688302947402014443 6973193532454421103021665)
        ·
          refine ⟨5229895149340815827266249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6973193532454421103021665 5229895149340815827266249)
          ·
            refine ⟨3922421362005611870449687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5229895149340815827266249 3922421362005611870449687)
            ·
              refine ⟨5883632043008417805674531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922421362005611870449687 5883632043008417805674531)
              ·
                refine ⟨8825448064512626708511797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883632043008417805674531 8825448064512626708511797)
                ·
                  refine ⟨827385756048058753922981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8825448064512626708511797 827385756048058753922981)
                  ·
                    refine ⟨155134829259011016360559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827385756048058753922981 155134829259011016360559)
                    ·
                      rfl

theorem cell23_906372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_906372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906372 prefixEnd_906372 := by exact prefixLift 906372
  have htrace : WordTrace (prefixWord ++ tailWord_906372) baseStart_906372 baseEnd_906372 := by
    simpa [prefixWord, tailWord_906372, baseEnd_906372] using wordTrace_append hprefix tailTrace_906372
  have hstable : (prefixWord ++ tailWord_906372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906372).length < 2 ^ (prefixWord ++ tailWord_906372).sum := by decide
  have hdescent : baseEnd_906372 < baseStart_906372 := by decide
  rcases family_descends (prefixWord ++ tailWord_906372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906376 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 2, 5]
def baseStart_906376 : Nat := 118140960795 + 906376 * 2 ^ 59
def prefixEnd_906376 : Nat := 4983230072969 + 3 ^ 40 * 906376 * 2
def baseEnd_906376 : Nat := 155135513899883677810553

theorem tailTrace_906376 : CollatzResearch.WordTrace tailWord_906376 prefixEnd_906376 155135513899883677810553 := by
  unfold tailWord_906376
  simp only [CollatzResearch.WordTrace]
  refine ⟨16529124282181011770957491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22038832376241349027943321 16529124282181011770957491)
  ·
    refine ⟨24793686423271517656436237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16529124282181011770957491 24793686423271517656436237)
    ·
      refine ⟨9297632408726819121163589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24793686423271517656436237 9297632408726819121163589)
      ·
        refine ⟨1743306076636278585218173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9297632408726819121163589 1743306076636278585218173)
        ·
          refine ⟨653739778738604469456815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1743306076636278585218173 653739778738604469456815)
          ·
            refine ⟨980609668107906704185223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653739778738604469456815 980609668107906704185223)
            ·
              refine ⟨1470914502161860056277835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980609668107906704185223 1470914502161860056277835)
              ·
                refine ⟨2206371753242790084416753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470914502161860056277835 2206371753242790084416753)
                ·
                  refine ⟨1654778814932092563312565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2206371753242790084416753 1654778814932092563312565)
                  ·
                    refine ⟨155135513899883677810553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1654778814932092563312565 155135513899883677810553)
                    ·
                      rfl

theorem cell23_906376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_906376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906376 prefixEnd_906376 := by exact prefixLift 906376
  have htrace : WordTrace (prefixWord ++ tailWord_906376) baseStart_906376 baseEnd_906376 := by
    simpa [prefixWord, tailWord_906376, baseEnd_906376] using wordTrace_append hprefix tailTrace_906376
  have hstable : (prefixWord ++ tailWord_906376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906376).length < 2 ^ (prefixWord ++ tailWord_906376).sum := by decide
  have hdescent : baseEnd_906376 < baseStart_906376 := by decide
  rcases family_descends (prefixWord ++ tailWord_906376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906405 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_906405 : Nat := 118140960795 + 906405 * 2 ^ 59
def prefixEnd_906405 : Nat := 4983230072969 + 3 ^ 40 * 906405 * 2
def baseEnd_906405 : Nat := 465421432638631419969025

theorem tailTrace_906405 : CollatzResearch.WordTrace tailWord_906405 prefixEnd_906405 465421432638631419969025 := by
  unfold tailWord_906405
  simp only [CollatzResearch.WordTrace]
  refine ⟨33059306281256961494720669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22039537520837974329813779 33059306281256961494720669)
  ·
    refine ⟨12397239855471360560520251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33059306281256961494720669 12397239855471360560520251)
    ·
      refine ⟨18595859783207040840780377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12397239855471360560520251 18595859783207040840780377)
      ·
        refine ⟨13946894837405280630585283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18595859783207040840780377 13946894837405280630585283)
        ·
          refine ⟨20920342256107920945877925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13946894837405280630585283 20920342256107920945877925)
          ·
            refine ⟨3922564173020235177352111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20920342256107920945877925 3922564173020235177352111)
            ·
              refine ⟨5883846259530352766028167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922564173020235177352111 5883846259530352766028167)
              ·
                refine ⟨8825769389295529149042251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883846259530352766028167 8825769389295529149042251)
                ·
                  refine ⟨13238654083943293723563377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8825769389295529149042251 13238654083943293723563377)
                  ·
                    refine ⟨9928990562957470292672533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13238654083943293723563377 9928990562957470292672533)
                    ·
                      refine ⟨465421432638631419969025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9928990562957470292672533 465421432638631419969025)
                      ·
                        rfl

theorem cell23_906405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_906405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906405 prefixEnd_906405 := by exact prefixLift 906405
  have htrace : WordTrace (prefixWord ++ tailWord_906405) baseStart_906405 baseEnd_906405 := by
    simpa [prefixWord, tailWord_906405, baseEnd_906405] using wordTrace_append hprefix tailTrace_906405
  have hstable : (prefixWord ++ tailWord_906405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906405).length < 2 ^ (prefixWord ++ tailWord_906405).sum := by decide
  have hdescent : baseEnd_906405 < baseStart_906405 := by decide
  rcases family_descends (prefixWord ++ tailWord_906405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906415 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 5, 5]
def baseStart_906415 : Nat := 118140960795 + 906415 * 2 ^ 59
def prefixEnd_906415 : Nat := 4983230072969 + 3 ^ 40 * 906415 * 2
def baseEnd_906415 : Nat := 155142189148392126947993

theorem tailTrace_906415 : CollatzResearch.WordTrace tailWord_906415 prefixEnd_906415 155142189148392126947993 := by
  unfold tailWord_906415
  simp only [CollatzResearch.WordTrace]
  refine ⟨33059671011220733202584699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22039780674147155468389799 33059671011220733202584699)
  ·
    refine ⟨49589506516831099803877049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33059671011220733202584699 49589506516831099803877049)
    ·
      refine ⟨37192129887623324852907787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49589506516831099803877049 37192129887623324852907787)
      ·
        refine ⟨55788194831434987279361681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37192129887623324852907787 55788194831434987279361681)
        ·
          refine ⟨41841146123576240459521261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55788194831434987279361681 41841146123576240459521261)
          ·
            refine ⟨15690429796341090172320473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41841146123576240459521261 15690429796341090172320473)
            ·
              refine ⟨11767822347255817629240355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15690429796341090172320473 11767822347255817629240355)
              ·
                refine ⟨17651733520883726443860533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11767822347255817629240355 17651733520883726443860533)
                ·
                  refine ⟨1654850017582849354111925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17651733520883726443860533 1654850017582849354111925)
                  ·
                    refine ⟨155142189148392126947993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1654850017582849354111925 155142189148392126947993)
                    ·
                      rfl

theorem cell23_906415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_906415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906415 prefixEnd_906415 := by exact prefixLift 906415
  have htrace : WordTrace (prefixWord ++ tailWord_906415) baseStart_906415 baseEnd_906415 := by
    simpa [prefixWord, tailWord_906415, baseEnd_906415] using wordTrace_append hprefix tailTrace_906415
  have hstable : (prefixWord ++ tailWord_906415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906415).length < 2 ^ (prefixWord ++ tailWord_906415).sum := by decide
  have hdescent : baseEnd_906415 < baseStart_906415 := by decide
  rcases family_descends (prefixWord ++ tailWord_906415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906429 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_906429 : Nat := 118140960795 + 906429 * 2 ^ 59
def prefixEnd_906429 : Nat := 4983230072969 + 3 ^ 40 * 906429 * 2
def baseEnd_906429 : Nat := 465433756174339326068915

theorem tailTrace_906429 : CollatzResearch.WordTrace tailWord_906429 prefixEnd_906429 465433756174339326068915 := by
  unfold tailWord_906429
  simp only [CollatzResearch.WordTrace]
  refine ⟨33060181633170013593594341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22040121088780009062396227 33060181633170013593594341)
  ·
    refine ⟨6198784056219377548798939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33060181633170013593594341 6198784056219377548798939)
    ·
      refine ⟨9298176084329066323198409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6198784056219377548798939 9298176084329066323198409)
      ·
        refine ⟨6973632063246799742398807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9298176084329066323198409 6973632063246799742398807)
        ·
          refine ⟨10460448094870199613598211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6973632063246799742398807 10460448094870199613598211)
          ·
            refine ⟨15690672142305299420397317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10460448094870199613598211 15690672142305299420397317)
            ·
              refine ⟨2942001026682243641324497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15690672142305299420397317 2942001026682243641324497)
              ·
                refine ⟨2206500770011682730993373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2942001026682243641324497 2206500770011682730993373)
                ·
                  refine ⟨827437788754381024122515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2206500770011682730993373 827437788754381024122515)
                  ·
                    refine ⟨1241156683131571536183773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 827437788754381024122515 1241156683131571536183773)
                    ·
                      refine ⟨465433756174339326068915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1241156683131571536183773 465433756174339326068915)
                      ·
                        rfl

theorem cell23_906429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_906429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906429 prefixEnd_906429 := by exact prefixLift 906429
  have htrace : WordTrace (prefixWord ++ tailWord_906429) baseStart_906429 baseEnd_906429 := by
    simpa [prefixWord, tailWord_906429, baseEnd_906429] using wordTrace_append hprefix tailTrace_906429
  have hstable : (prefixWord ++ tailWord_906429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906429).length < 2 ^ (prefixWord ++ tailWord_906429).sum := by decide
  have hdescent : baseEnd_906429 < baseStart_906429 := by decide
  rcases family_descends (prefixWord ++ tailWord_906429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906456 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 2, 3, 2]
def baseStart_906456 : Nat := 118140960795 + 906456 * 2 ^ 59
def prefixEnd_906456 : Nat := 4983230072969 + 3 ^ 40 * 906456 * 2
def baseEnd_906456 : Nat := 465447620152010720431291

theorem tailTrace_906456 : CollatzResearch.WordTrace tailWord_906456 prefixEnd_906456 465447620152010720431291 := by
  unfold tailWord_906456
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530583202036098602413611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22040777602714798136551481 16530583202036098602413611)
  ·
    refine ⟨24795874803054147903620417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16530583202036098602413611 24795874803054147903620417)
    ·
      refine ⟨18596906102290610927715313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24795874803054147903620417 18596906102290610927715313)
      ·
        refine ⟨13947679576717958195786485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18596906102290610927715313 13947679576717958195786485)
        ·
          refine ⟨1307594960317308580854983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13947679576717958195786485 1307594960317308580854983)
          ·
            refine ⟨1961392440475962871282475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307594960317308580854983 1961392440475962871282475)
            ·
              refine ⟨2942088660713944306923713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961392440475962871282475 2942088660713944306923713)
              ·
                refine ⟨2206566495535458230192785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2942088660713944306923713 2206566495535458230192785)
                ·
                  refine ⟨1654924871651593672644589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2206566495535458230192785 1654924871651593672644589)
                  ·
                    refine ⟨620596826869347627241721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1654924871651593672644589 620596826869347627241721)
                    ·
                      refine ⟨465447620152010720431291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620596826869347627241721 465447620152010720431291)
                      ·
                        rfl

theorem cell23_906456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_906456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906456 prefixEnd_906456 := by exact prefixLift 906456
  have htrace : WordTrace (prefixWord ++ tailWord_906456) baseStart_906456 baseEnd_906456 := by
    simpa [prefixWord, tailWord_906456, baseEnd_906456] using wordTrace_append hprefix tailTrace_906456
  have hstable : (prefixWord ++ tailWord_906456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906456).length < 2 ^ (prefixWord ++ tailWord_906456).sum := by decide
  have hdescent : baseEnd_906456 < baseStart_906456 := by decide
  rcases family_descends (prefixWord ++ tailWord_906456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906472 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_906472 : Nat := 118140960795 + 906472 * 2 ^ 59
def prefixEnd_906472 : Nat := 4983230072969 + 3 ^ 40 * 906472 * 2
def baseEnd_906472 : Nat := 465455835842482657831217

theorem tailTrace_906472 : CollatzResearch.WordTrace tailWord_906472 prefixEnd_906472 465455835842482657831217 := by
  unfold tailWord_906472
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530874986007115968704835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22041166648009487958273113 16530874986007115968704835)
  ·
    refine ⟨24796312479010673953057253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16530874986007115968704835 24796312479010673953057253)
    ·
      refine ⟨4649308589814501366198235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24796312479010673953057253 4649308589814501366198235)
      ·
        refine ⟨6973962884721752049297353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649308589814501366198235 6973962884721752049297353)
        ·
          refine ⟨5230472163541314036973015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6973962884721752049297353 5230472163541314036973015)
          ·
            refine ⟨7845708245311971055459523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230472163541314036973015 7845708245311971055459523)
            ·
              refine ⟨11768562367967956583189285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845708245311971055459523 11768562367967956583189285)
              ·
                refine ⟨2206605443993991859347991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11768562367967956583189285 2206605443993991859347991)
                ·
                  refine ⟨3309908165990987789021987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206605443993991859347991 3309908165990987789021987)
                  ·
                    refine ⟨4964862248986481683532981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3309908165990987789021987 4964862248986481683532981)
                    ·
                      refine ⟨465455835842482657831217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4964862248986481683532981 465455835842482657831217)
                      ·
                        rfl

theorem cell23_906472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_906472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906472 prefixEnd_906472 := by exact prefixLift 906472
  have htrace : WordTrace (prefixWord ++ tailWord_906472) baseStart_906472 baseEnd_906472 := by
    simpa [prefixWord, tailWord_906472, baseEnd_906472] using wordTrace_append hprefix tailTrace_906472
  have hstable : (prefixWord ++ tailWord_906472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906472).length < 2 ^ (prefixWord ++ tailWord_906472).sum := by decide
  have hdescent : baseEnd_906472 < baseStart_906472 := by decide
  rcases family_descends (prefixWord ++ tailWord_906472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906475 : List Nat := [1, 1, 1, 1, 2, 6, 1, 10]
def baseStart_906475 : Nat := 118140960795 + 906475 * 2 ^ 59
def prefixEnd_906475 : Nat := 4983230072969 + 3 ^ 40 * 906475 * 2
def baseEnd_906475 : Nat := 17239162084609116521989

theorem tailTrace_906475 : CollatzResearch.WordTrace tailWord_906475 prefixEnd_906475 17239162084609116521989 := by
  unfold tailWord_906475
  simp only [CollatzResearch.WordTrace]
  refine ⟨33061859391003363449768879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22041239594002242299845919 33061859391003363449768879)
  ·
    refine ⟨49592789086505045174653319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33061859391003363449768879 49592789086505045174653319)
    ·
      refine ⟨74389183629757567761979979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49592789086505045174653319 74389183629757567761979979)
      ·
        refine ⟨111583775444636351642969969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74389183629757567761979979 111583775444636351642969969)
        ·
          refine ⟨83687831583477263732227477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111583775444636351642969969 83687831583477263732227477)
          ·
            refine ⟨3922867105475496737448163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83687831583477263732227477 3922867105475496737448163)
            ·
              refine ⟨5884300658213245106172245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922867105475496737448163 5884300658213245106172245)
              ·
                refine ⟨17239162084609116521989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5884300658213245106172245 17239162084609116521989)
                ·
                  rfl

theorem cell23_906475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 10].length) (baseStart_906475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906475 prefixEnd_906475 := by exact prefixLift 906475
  have htrace : WordTrace (prefixWord ++ tailWord_906475) baseStart_906475 baseEnd_906475 := by
    simpa [prefixWord, tailWord_906475, baseEnd_906475] using wordTrace_append hprefix tailTrace_906475
  have hstable : (prefixWord ++ tailWord_906475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906475).length < 2 ^ (prefixWord ++ tailWord_906475).sum := by decide
  have hdescent : baseEnd_906475 < baseStart_906475 := by decide
  rcases family_descends (prefixWord ++ tailWord_906475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906486 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_906486 : Nat := 118140960795 + 906486 * 2 ^ 59
def prefixEnd_906486 : Nat := 4983230072969 + 3 ^ 40 * 906486 * 2
def baseEnd_906486 : Nat := 465463024571645603056153

theorem tailTrace_906486 : CollatzResearch.WordTrace tailWord_906486 prefixEnd_906486 465463024571645603056153 := by
  unfold tailWord_906486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066391287122719520526207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22041507062642341552279541 2066391287122719520526207)
  ·
    refine ⟨3099586930684079280789311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2066391287122719520526207 3099586930684079280789311)
    ·
      refine ⟨4649380396026118921183967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099586930684079280789311 4649380396026118921183967)
      ·
        refine ⟨6974070594039178381775951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649380396026118921183967 6974070594039178381775951)
        ·
          refine ⟨10461105891058767572663927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974070594039178381775951 10461105891058767572663927)
          ·
            refine ⟨15691658836588151358995891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461105891058767572663927 15691658836588151358995891)
            ·
              refine ⟨23537488254882227038493837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15691658836588151358995891 23537488254882227038493837)
              ·
                refine ⟨8826558095580835139435189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23537488254882227038493837 8826558095580835139435189)
                ·
                  refine ⟨827489821460703294322049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8826558095580835139435189 827489821460703294322049)
                  ·
                    refine ⟨620617366095527470741537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 827489821460703294322049 620617366095527470741537)
                    ·
                      refine ⟨465463024571645603056153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620617366095527470741537 465463024571645603056153)
                      ·
                        rfl

theorem cell23_906486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_906486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906486 prefixEnd_906486 := by exact prefixLift 906486
  have htrace : WordTrace (prefixWord ++ tailWord_906486) baseStart_906486 baseEnd_906486 := by
    simpa [prefixWord, tailWord_906486, baseEnd_906486] using wordTrace_append hprefix tailTrace_906486
  have hstable : (prefixWord ++ tailWord_906486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906486).length < 2 ^ (prefixWord ++ tailWord_906486).sum := by decide
  have hdescent : baseEnd_906486 < baseStart_906486 := by decide
  rcases family_descends (prefixWord ++ tailWord_906486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906514 : List Nat := [3, 2, 4, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_906514 : Nat := 118140960795 + 906514 * 2 ^ 59
def prefixEnd_906514 : Nat := 4983230072969 + 3 ^ 40 * 906514 * 2
def baseEnd_906514 : Nat := 465477402029971493506025

theorem tailTrace_906514 : CollatzResearch.WordTrace tailWord_906514 prefixEnd_906514 465477402029971493506025 := by
  unfold tailWord_906514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265820459465518277609649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22042187891908048740292397 8265820459465518277609649)
  ·
    refine ⟨6199365344599138708207237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8265820459465518277609649 6199365344599138708207237)
    ·
      refine ⟨1162381002112338507788857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6199365344599138708207237 1162381002112338507788857)
      ·
        refine ⟨871785751584253880841643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162381002112338507788857 871785751584253880841643)
        ·
          refine ⟨1307678627376380821262465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871785751584253880841643 1307678627376380821262465)
          ·
            refine ⟨980758970532285615946849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307678627376380821262465 980758970532285615946849)
            ·
              refine ⟨735569227899214211960137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980758970532285615946849 735569227899214211960137)
              ·
                refine ⟨551676920924410658970103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735569227899214211960137 551676920924410658970103)
                ·
                  refine ⟨827515381386615988455155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551676920924410658970103 827515381386615988455155)
                  ·
                    refine ⟨1241273072079923982682733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 827515381386615988455155 1241273072079923982682733)
                    ·
                      refine ⟨465477402029971493506025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1241273072079923982682733 465477402029971493506025)
                      ·
                        rfl

theorem cell23_906514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_906514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906514 prefixEnd_906514 := by exact prefixLift 906514
  have htrace : WordTrace (prefixWord ++ tailWord_906514) baseStart_906514 baseEnd_906514 := by
    simpa [prefixWord, tailWord_906514, baseEnd_906514] using wordTrace_append hprefix tailTrace_906514
  have hstable : (prefixWord ++ tailWord_906514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906514).length < 2 ^ (prefixWord ++ tailWord_906514).sum := by decide
  have hdescent : baseEnd_906514 < baseStart_906514 := by decide
  rcases family_descends (prefixWord ++ tailWord_906514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906515 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7]
def baseStart_906515 : Nat := 118140960795 + 906515 * 2 ^ 59
def prefixEnd_906515 : Nat := 4983230072969 + 3 ^ 40 * 906515 * 2
def baseEnd_906515 : Nat := 465477915510625989593519

theorem tailTrace_906515 : CollatzResearch.WordTrace tailWord_906515 prefixEnd_906515 465477915510625989593519 := by
  unfold tailWord_906515
  simp only [CollatzResearch.WordTrace]
  refine ⟨33063318310858450281224999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22042212207238966854149999 33063318310858450281224999)
  ·
    refine ⟨49594977466287675421837499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33063318310858450281224999 49594977466287675421837499)
    ·
      refine ⟨74392466199431513132756249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49594977466287675421837499 74392466199431513132756249)
      ·
        refine ⟨55794349649573634849567187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74392466199431513132756249 55794349649573634849567187)
        ·
          refine ⟨83691524474360452274350781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55794349649573634849567187 83691524474360452274350781)
          ·
            refine ⟨31384321677885169602881543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83691524474360452274350781 31384321677885169602881543)
            ·
              refine ⟨47076482516827754404322315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31384321677885169602881543 47076482516827754404322315)
              ·
                refine ⟨70614723775241631606483473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47076482516827754404322315 70614723775241631606483473)
                ·
                  refine ⟨52961042831431223704862605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70614723775241631606483473 52961042831431223704862605)
                  ·
                    refine ⟨19860391061786708889323477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52961042831431223704862605 19860391061786708889323477)
                    ·
                      refine ⟨465477915510625989593519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19860391061786708889323477 465477915510625989593519)
                      ·
                        rfl

theorem cell23_906515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_906515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906515 prefixEnd_906515 := by exact prefixLift 906515
  have htrace : WordTrace (prefixWord ++ tailWord_906515) baseStart_906515 baseEnd_906515 := by
    simpa [prefixWord, tailWord_906515, baseEnd_906515] using wordTrace_append hprefix tailTrace_906515
  have hstable : (prefixWord ++ tailWord_906515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906515).length < 2 ^ (prefixWord ++ tailWord_906515).sum := by decide
  have hdescent : baseEnd_906515 < baseStart_906515 := by decide
  rcases family_descends (prefixWord ++ tailWord_906515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906520 : List Nat := [2, 1, 2, 3, 1, 3, 4, 2, 1, 2, 2]
def baseStart_906520 : Nat := 118140960795 + 906520 * 2 ^ 59
def prefixEnd_906520 : Nat := 4983230072969 + 3 ^ 40 * 906520 * 2
def baseEnd_906520 : Nat := 465480482913898470030997

theorem tailTrace_906520 : CollatzResearch.WordTrace tailWord_906520 prefixEnd_906520 465480482913898470030997 := by
  unfold tailWord_906520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16531750337920168067578507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22042333783893557423438009 16531750337920168067578507)
  ·
    refine ⟨24797625506880252101367761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16531750337920168067578507 24797625506880252101367761)
    ·
      refine ⟨18598219130160189076025821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24797625506880252101367761 18598219130160189076025821)
      ·
        refine ⟨6974332173810070903509683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18598219130160189076025821 6974332173810070903509683)
        ·
          refine ⟨10461498260715106355264525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974332173810070903509683 10461498260715106355264525)
          ·
            refine ⟨3923061847768164883224197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10461498260715106355264525 3923061847768164883224197)
            ·
              refine ⟨735574096456530915604537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3923061847768164883224197 735574096456530915604537)
              ·
                refine ⟨551680572342398186703403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735574096456530915604537 551680572342398186703403)
                ·
                  refine ⟨827520858513597280055105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551680572342398186703403 827520858513597280055105)
                  ·
                    refine ⟨620640643885197960041329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 827520858513597280055105 620640643885197960041329)
                    ·
                      refine ⟨465480482913898470030997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620640643885197960041329 465480482913898470030997)
                      ·
                        rfl

theorem cell23_906520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_906520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906520 prefixEnd_906520 := by exact prefixLift 906520
  have htrace : WordTrace (prefixWord ++ tailWord_906520) baseStart_906520 baseEnd_906520 := by
    simpa [prefixWord, tailWord_906520, baseEnd_906520] using wordTrace_append hprefix tailTrace_906520
  have hstable : (prefixWord ++ tailWord_906520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906520).length < 2 ^ (prefixWord ++ tailWord_906520).sum := by decide
  have hdescent : baseEnd_906520 < baseStart_906520 := by decide
  rcases family_descends (prefixWord ++ tailWord_906520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906522 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_906522 : Nat := 118140960795 + 906522 * 2 ^ 59
def prefixEnd_906522 : Nat := 4983230072969 + 3 ^ 40 * 906522 * 2
def baseEnd_906522 : Nat := 155160503291735820735329

theorem tailTrace_906522 : CollatzResearch.WordTrace tailWord_906522 prefixEnd_906522 155160503291735820735329 := by
  unfold tailWord_906522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265893405458272619182455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22042382414555393651153213 8265893405458272619182455)
  ·
    refine ⟨12398840108187408928773683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8265893405458272619182455 12398840108187408928773683)
    ·
      refine ⟨18598260162281113393160525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12398840108187408928773683 18598260162281113393160525)
      ·
        refine ⟨6974347560855417522435197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18598260162281113393160525 6974347560855417522435197)
        ·
          refine ⟨2615380335320781570913199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6974347560855417522435197 2615380335320781570913199)
          ·
            refine ⟨3923070502981172356369799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615380335320781570913199 3923070502981172356369799)
            ·
              refine ⟨5884605754471758534554699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923070502981172356369799 5884605754471758534554699)
              ·
                refine ⟨8826908631707637801832049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884605754471758534554699 8826908631707637801832049)
                ·
                  refine ⟨6620181473780728351374037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8826908631707637801832049 6620181473780728351374037)
                  ·
                    refine ⟨155160503291735820735329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6620181473780728351374037 155160503291735820735329)
                    ·
                      rfl

theorem cell23_906522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_906522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906522 prefixEnd_906522 := by exact prefixLift 906522
  have htrace : WordTrace (prefixWord ++ tailWord_906522) baseStart_906522 baseEnd_906522 := by
    simpa [prefixWord, tailWord_906522, baseEnd_906522] using wordTrace_append hprefix tailTrace_906522
  have hstable : (prefixWord ++ tailWord_906522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906522).length < 2 ^ (prefixWord ++ tailWord_906522).sum := by decide
  have hdescent : baseEnd_906522 < baseStart_906522 := by decide
  rcases family_descends (prefixWord ++ tailWord_906522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906536 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_906536 : Nat := 118140960795 + 906536 * 2 ^ 59
def prefixEnd_906536 : Nat := 4983230072969 + 3 ^ 40 * 906536 * 2
def baseEnd_906536 : Nat := 465488698604370407430923

theorem tailTrace_906536 : CollatzResearch.WordTrace tailWord_906536 prefixEnd_906536 465488698604370407430923 := by
  unfold tailWord_906536
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532042121891185433869731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22042722829188247245159641 16532042121891185433869731)
  ·
    refine ⟨24798063182836778150804597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16532042121891185433869731 24798063182836778150804597)
    ·
      refine ⟨2324818423390947951637931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24798063182836778150804597 2324818423390947951637931)
      ·
        refine ⟨3487227635086421927456897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324818423390947951637931 3487227635086421927456897)
        ·
          refine ⟨2615420726314816445592673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3487227635086421927456897 2615420726314816445592673)
          ·
            refine ⟨1961565544736112334194505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615420726314816445592673 1961565544736112334194505)
            ·
              refine ⟨1471174158552084250645879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961565544736112334194505 1471174158552084250645879)
              ·
                refine ⟨2206761237828126375968819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471174158552084250645879 2206761237828126375968819)
                ·
                  refine ⟨3310141856742189563953229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206761237828126375968819 3310141856742189563953229)
                  ·
                    refine ⟨1241303196278321086482461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310141856742189563953229 1241303196278321086482461)
                    ·
                      refine ⟨465488698604370407430923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1241303196278321086482461 465488698604370407430923)
                      ·
                        rfl

theorem cell23_906536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_906536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906536 prefixEnd_906536 := by exact prefixLift 906536
  have htrace : WordTrace (prefixWord ++ tailWord_906536) baseStart_906536 baseEnd_906536 := by
    simpa [prefixWord, tailWord_906536, baseEnd_906536] using wordTrace_append hprefix tailTrace_906536
  have hstable : (prefixWord ++ tailWord_906536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906536).length < 2 ^ (prefixWord ++ tailWord_906536).sum := by decide
  have hdescent : baseEnd_906536 < baseStart_906536 := by decide
  rcases family_descends (prefixWord ++ tailWord_906536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906546 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_906546 : Nat := 118140960795 + 906546 * 2 ^ 59
def prefixEnd_906546 : Nat := 4983230072969 + 3 ^ 40 * 906546 * 2
def baseEnd_906546 : Nat := 465493833410915368305877

theorem tailTrace_906546 : CollatzResearch.WordTrace tailWord_906546 prefixEnd_906546 465493833410915368305877 := by
  unfold tailWord_906546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266112243436535643900873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22042965982497428383735661 8266112243436535643900873)
  ·
    refine ⟨6199584182577401732925655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8266112243436535643900873 6199584182577401732925655)
    ·
      refine ⟨9299376273866102599388483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6199584182577401732925655 9299376273866102599388483)
      ·
        refine ⟨13949064410799153899082725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9299376273866102599388483 13949064410799153899082725)
        ·
          refine ⟨2615449577024841356078011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13949064410799153899082725 2615449577024841356078011)
          ·
            refine ⟨3923174365537262034117017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615449577024841356078011 3923174365537262034117017)
            ·
              refine ⟨2942380774152946525587763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3923174365537262034117017 2942380774152946525587763)
              ·
                refine ⟨4413571161229419788381645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942380774152946525587763 4413571161229419788381645)
                ·
                  refine ⟨1655089185461032420643117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4413571161229419788381645 1655089185461032420643117)
                  ·
                    refine ⟨620658444547887157741169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655089185461032420643117 620658444547887157741169)
                    ·
                      refine ⟨465493833410915368305877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620658444547887157741169 465493833410915368305877)
                      ·
                        rfl

theorem cell23_906546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_906546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906546 prefixEnd_906546 := by exact prefixLift 906546
  have htrace : WordTrace (prefixWord ++ tailWord_906546) baseStart_906546 baseEnd_906546 := by
    simpa [prefixWord, tailWord_906546, baseEnd_906546] using wordTrace_append hprefix tailTrace_906546
  have hstable : (prefixWord ++ tailWord_906546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906546).length < 2 ^ (prefixWord ++ tailWord_906546).sum := by decide
  have hdescent : baseEnd_906546 < baseStart_906546 := by decide
  rcases family_descends (prefixWord ++ tailWord_906546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906557 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_906557 : Nat := 118140960795 + 906557 * 2 ^ 59
def prefixEnd_906557 : Nat := 4983230072969 + 3 ^ 40 * 906557 * 2
def baseEnd_906557 : Nat := 465499481698114825268327

theorem tailTrace_906557 : CollatzResearch.WordTrace tailWord_906557 prefixEnd_906557 465499481698114825268327 := by
  unfold tailWord_906557
  simp only [CollatzResearch.WordTrace]
  refine ⟨33064850176706291454253925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22043233451137527636169283 33064850176706291454253925)
  ·
    refine ⟨6199659408132429647672611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33064850176706291454253925 6199659408132429647672611)
    ·
      refine ⟨9299489112198644471508917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6199659408132429647672611 9299489112198644471508917)
      ·
        refine ⟨871827104268622919203961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9299489112198644471508917 871827104268622919203961)
        ·
          refine ⟨653870328201467189402971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871827104268622919203961 653870328201467189402971)
          ·
            refine ⟨980805492302200784104457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653870328201467189402971 980805492302200784104457)
            ·
              refine ⟨735604119226650588078343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980805492302200784104457 735604119226650588078343)
              ·
                refine ⟨1103406178839975882117515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735604119226650588078343 1103406178839975882117515)
                ·
                  refine ⟨1655109268259963823176273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103406178839975882117515 1655109268259963823176273)
                  ·
                    refine ⟨1241331951194972867382205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1655109268259963823176273 1241331951194972867382205)
                    ·
                      refine ⟨465499481698114825268327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1241331951194972867382205 465499481698114825268327)
                      ·
                        rfl

theorem cell23_906557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_906557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906557 prefixEnd_906557 := by exact prefixLift 906557
  have htrace : WordTrace (prefixWord ++ tailWord_906557) baseStart_906557 baseEnd_906557 := by
    simpa [prefixWord, tailWord_906557, baseEnd_906557] using wordTrace_append hprefix tailTrace_906557
  have hstable : (prefixWord ++ tailWord_906557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906557).length < 2 ^ (prefixWord ++ tailWord_906557).sum := by decide
  have hdescent : baseEnd_906557 < baseStart_906557 := by decide
  rcases family_descends (prefixWord ++ tailWord_906557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906576 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 4, 2, 2]
def baseStart_906576 : Nat := 118140960795 + 906576 * 2 ^ 59
def prefixEnd_906576 : Nat := 4983230072969 + 3 ^ 40 * 906576 * 2
def baseEnd_906576 : Nat := 465509237830550250930739

theorem tailTrace_906576 : CollatzResearch.WordTrace tailWord_906576 prefixEnd_906576 465509237830550250930739 := by
  unfold tailWord_906576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532771581818728849597791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22043695442424971799463721 16532771581818728849597791)
  ·
    refine ⟨24799157372728093274396687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16532771581818728849597791 24799157372728093274396687)
    ·
      refine ⟨37198736059092139911595031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24799157372728093274396687 37198736059092139911595031)
      ·
        refine ⟨55798104088638209867392547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37198736059092139911595031 55798104088638209867392547)
        ·
          refine ⟨83697156132957314801088821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55798104088638209867392547 83697156132957314801088821)
          ·
            refine ⟨7846608387464748262602077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83697156132957314801088821 7846608387464748262602077)
            ·
              refine ⟨2942478145299280598475779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7846608387464748262602077 2942478145299280598475779)
              ·
                refine ⟨4413717217948920897713669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942478145299280598475779 4413717217948920897713669)
                ·
                  refine ⟨827571978365422668321313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4413717217948920897713669 827571978365422668321313)
                  ·
                    refine ⟨620678983774067001240985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 827571978365422668321313 620678983774067001240985)
                    ·
                      refine ⟨465509237830550250930739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620678983774067001240985 465509237830550250930739)
                      ·
                        rfl

theorem cell23_906576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 2, 2].length) (baseStart_906576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906576 prefixEnd_906576 := by exact prefixLift 906576
  have htrace : WordTrace (prefixWord ++ tailWord_906576) baseStart_906576 baseEnd_906576 := by
    simpa [prefixWord, tailWord_906576, baseEnd_906576] using wordTrace_append hprefix tailTrace_906576
  have hstable : (prefixWord ++ tailWord_906576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906576).length < 2 ^ (prefixWord ++ tailWord_906576).sum := by decide
  have hdescent : baseEnd_906576 < baseStart_906576 := by decide
  rcases family_descends (prefixWord ++ tailWord_906576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906633 : List Nat := [1, 2, 1, 1, 7, 1, 3, 2, 5]
def baseStart_906633 : Nat := 118140960795 + 906633 * 2 ^ 59
def prefixEnd_906633 : Nat := 4983230072969 + 3 ^ 40 * 906633 * 2
def baseEnd_906633 : Nat := 51726500691984058657553

theorem tailTrace_906633 : CollatzResearch.WordTrace tailWord_906633 prefixEnd_906633 51726500691984058657553 := by
  unfold tailWord_906633
  simp only [CollatzResearch.WordTrace]
  refine ⟨33067622124430956434020553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22045081416287304289347035 33067622124430956434020553)
  ·
    refine ⟨24800716593323217325515415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33067622124430956434020553 24800716593323217325515415)
    ·
      refine ⟨37201074889984825988273123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24800716593323217325515415 37201074889984825988273123)
      ·
        refine ⟨55801612334977238982409685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37201074889984825988273123 55801612334977238982409685)
        ·
          refine ⟨1307850289101029038650227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 55801612334977238982409685 1307850289101029038650227)
          ·
            refine ⟨1961775433651543557975341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307850289101029038650227 1961775433651543557975341)
            ·
              refine ⟨735665787619328834240753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1961775433651543557975341 735665787619328834240753)
              ·
                refine ⟨551749340714496625680565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735665787619328834240753 551749340714496625680565)
                ·
                  refine ⟨51726500691984058657553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 551749340714496625680565 51726500691984058657553)
                  ·
                    rfl

theorem cell23_906633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 5].length) (baseStart_906633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906633 prefixEnd_906633 := by exact prefixLift 906633
  have htrace : WordTrace (prefixWord ++ tailWord_906633) baseStart_906633 baseEnd_906633 := by
    simpa [prefixWord, tailWord_906633, baseEnd_906633] using wordTrace_append hprefix tailTrace_906633
  have hstable : (prefixWord ++ tailWord_906633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906633).length < 2 ^ (prefixWord ++ tailWord_906633).sum := by decide
  have hdescent : baseEnd_906633 < baseStart_906633 := by decide
  rcases family_descends (prefixWord ++ tailWord_906633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906659 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 5, 4]
def baseStart_906659 : Nat := 118140960795 + 906659 * 2 ^ 59
def prefixEnd_906659 : Nat := 4983230072969 + 3 ^ 40 * 906659 * 2
def baseEnd_906659 : Nat := 155183952241624475397619

theorem tailTrace_906659 : CollatzResearch.WordTrace tailWord_906659 prefixEnd_906659 155183952241624475397619 := by
  unfold tailWord_906659
  simp only [CollatzResearch.WordTrace]
  refine ⟨33068570422336762874467031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22045713614891175249644687 33068570422336762874467031)
  ·
    refine ⟨49602855633505144311700547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33068570422336762874467031 49602855633505144311700547)
    ·
      refine ⟨74404283450257716467550821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49602855633505144311700547 74404283450257716467550821)
      ·
        refine ⟨13950803146923321837665779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74404283450257716467550821 13950803146923321837665779)
        ·
          refine ⟨20926204720384982756498669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13950803146923321837665779 20926204720384982756498669)
          ·
            refine ⟨7847326770144368533687001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20926204720384982756498669 7847326770144368533687001)
            ·
              refine ⟨5885495077608276400265251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7847326770144368533687001 5885495077608276400265251)
              ·
                refine ⟨8828242616412414600397877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5885495077608276400265251 8828242616412414600397877)
                ·
                  refine ⟨827647745288663868787301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8828242616412414600397877 827647745288663868787301)
                  ·
                    refine ⟨155183952241624475397619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827647745288663868787301 155183952241624475397619)
                    ·
                      rfl

theorem cell23_906659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 4].length) (baseStart_906659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906659 prefixEnd_906659 := by exact prefixLift 906659
  have htrace : WordTrace (prefixWord ++ tailWord_906659) baseStart_906659 baseEnd_906659 := by
    simpa [prefixWord, tailWord_906659, baseEnd_906659] using wordTrace_append hprefix tailTrace_906659
  have hstable : (prefixWord ++ tailWord_906659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906659).length < 2 ^ (prefixWord ++ tailWord_906659).sum := by decide
  have hdescent : baseEnd_906659 < baseStart_906659 := by decide
  rcases family_descends (prefixWord ++ tailWord_906659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906672 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 8]
def baseStart_906672 : Nat := 118140960795 + 906672 * 2 ^ 59
def prefixEnd_906672 : Nat := 4983230072969 + 3 ^ 40 * 906672 * 2
def baseEnd_906672 : Nat := 51728725774820208370033

theorem tailTrace_906672 : CollatzResearch.WordTrace tailWord_906672 prefixEnd_906672 51728725774820208370033 := by
  unfold tailWord_906672
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534522285644833047345135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22046029714193110729793513 16534522285644833047345135)
  ·
    refine ⟨24801783428467249571017703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16534522285644833047345135 24801783428467249571017703)
    ·
      refine ⟨37202675142700874356526555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24801783428467249571017703 37202675142700874356526555)
      ·
        refine ⟨55804012714051311534789833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37202675142700874356526555 55804012714051311534789833)
        ·
          refine ⟨41853009535538483651092375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55804012714051311534789833 41853009535538483651092375)
          ·
            refine ⟨62779514303307725476638563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41853009535538483651092375 62779514303307725476638563)
            ·
              refine ⟨94169271454961588214957845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62779514303307725476638563 94169271454961588214957845)
              ·
                refine ⟨4414184599451324447576149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94169271454961588214957845 4414184599451324447576149)
                ·
                  refine ⟨51728725774820208370033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4414184599451324447576149 51728725774820208370033)
                  ·
                    rfl

theorem cell23_906672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_906672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906672 prefixEnd_906672 := by exact prefixLift 906672
  have htrace : WordTrace (prefixWord ++ tailWord_906672) baseStart_906672 baseEnd_906672 := by
    simpa [prefixWord, tailWord_906672, baseEnd_906672] using wordTrace_append hprefix tailTrace_906672
  have hstable : (prefixWord ++ tailWord_906672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906672).length < 2 ^ (prefixWord ++ tailWord_906672).sum := by decide
  have hdescent : baseEnd_906672 < baseStart_906672 := by decide
  rcases family_descends (prefixWord ++ tailWord_906672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906719 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 3, 5]
def baseStart_906719 : Nat := 118140960795 + 906719 * 2 ^ 59
def prefixEnd_906719 : Nat := 4983230072969 + 3 ^ 40 * 906719 * 2
def baseEnd_906719 : Nat := 155194221854714397147527

theorem tailTrace_906719 : CollatzResearch.WordTrace tailWord_906719 prefixEnd_906719 155194221854714397147527 := by
  unfold tailWord_906719
  simp only [CollatzResearch.WordTrace]
  refine ⟨33070758802119393121651211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22047172534746262081100807 33070758802119393121651211)
  ·
    refine ⟨49606138203179089682476817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33070758802119393121651211 49606138203179089682476817)
    ·
      refine ⟨37204603652384317261857613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49606138203179089682476817 37204603652384317261857613)
      ·
        refine ⟨13951726369644118973196605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37204603652384317261857613 13951726369644118973196605)
        ·
          refine ⟨5231897388616544614948727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13951726369644118973196605 5231897388616544614948727)
          ·
            refine ⟨7847846082924816922423091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231897388616544614948727 7847846082924816922423091)
            ·
              refine ⟨11771769124387225383634637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7847846082924816922423091 11771769124387225383634637)
              ·
                refine ⟨4414413421645209518862989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11771769124387225383634637 4414413421645209518862989)
                ·
                  refine ⟨1655405033116953569573621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4414413421645209518862989 1655405033116953569573621)
                  ·
                    refine ⟨155194221854714397147527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1655405033116953569573621 155194221854714397147527)
                    ·
                      rfl

theorem cell23_906719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_906719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906719 prefixEnd_906719 := by exact prefixLift 906719
  have htrace : WordTrace (prefixWord ++ tailWord_906719) baseStart_906719 baseEnd_906719 := by
    simpa [prefixWord, tailWord_906719, baseEnd_906719] using wordTrace_append hprefix tailTrace_906719
  have hstable : (prefixWord ++ tailWord_906719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906719).length < 2 ^ (prefixWord ++ tailWord_906719).sum := by decide
  have hdescent : baseEnd_906719 < baseStart_906719 := by decide
  rcases family_descends (prefixWord ++ tailWord_906719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906736 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 1, 5]
def baseStart_906736 : Nat := 118140960795 + 906736 * 2 ^ 59
def prefixEnd_906736 : Nat := 4983230072969 + 3 ^ 40 * 906736 * 2
def baseEnd_906736 : Nat := 155197131578423208310001

theorem tailTrace_906736 : CollatzResearch.WordTrace tailWord_906736 prefixEnd_906736 155197131578423208310001 := by
  unfold tailWord_906736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16535689421528902512510031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22047585895371870016680041 16535689421528902512510031)
  ·
    refine ⟨24803534132293353768765047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16535689421528902512510031 24803534132293353768765047)
    ·
      refine ⟨37205301198440030653147571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24803534132293353768765047 37205301198440030653147571)
      ·
        refine ⟨55807951797660045979721357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37205301198440030653147571 55807951797660045979721357)
        ·
          refine ⟨20927981924122517242395509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55807951797660045979721357 20927981924122517242395509)
          ·
            refine ⟨1961998305386485991474579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20927981924122517242395509 1961998305386485991474579)
            ·
              refine ⟨2942997458079728987211869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961998305386485991474579 2942997458079728987211869)
              ·
                refine ⟨1103624046779898370204451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2942997458079728987211869 1103624046779898370204451)
                ·
                  refine ⟨1655436070169847555306677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103624046779898370204451 1655436070169847555306677)
                  ·
                    refine ⟨155197131578423208310001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1655436070169847555306677 155197131578423208310001)
                    ·
                      rfl

theorem cell23_906736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_906736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906736 prefixEnd_906736 := by exact prefixLift 906736
  have htrace : WordTrace (prefixWord ++ tailWord_906736) baseStart_906736 baseEnd_906736 := by
    simpa [prefixWord, tailWord_906736, baseEnd_906736] using wordTrace_append hprefix tailTrace_906736
  have hstable : (prefixWord ++ tailWord_906736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906736).length < 2 ^ (prefixWord ++ tailWord_906736).sum := by decide
  have hdescent : baseEnd_906736 < baseStart_906736 := by decide
  rcases family_descends (prefixWord ++ tailWord_906736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906739 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 4]
def baseStart_906739 : Nat := 118140960795 + 906739 * 2 ^ 59
def prefixEnd_906739 : Nat := 4983230072969 + 3 ^ 40 * 906739 * 2
def baseEnd_906739 : Nat := 465592935177233113192489

theorem tailTrace_906739 : CollatzResearch.WordTrace tailWord_906739 prefixEnd_906739 465592935177233113192489 := by
  unfold tailWord_906739
  simp only [CollatzResearch.WordTrace]
  refine ⟨33071488262046936537379271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22047658841364624358252847 33071488262046936537379271)
  ·
    refine ⟨49607232393070404806068907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33071488262046936537379271 49607232393070404806068907)
    ·
      refine ⟨74410848589605607209103361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49607232393070404806068907 74410848589605607209103361)
      ·
        refine ⟨55808136442204205406827521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74410848589605607209103361 55808136442204205406827521)
        ·
          refine ⟨41856102331653154055120641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55808136442204205406827521 41856102331653154055120641)
          ·
            refine ⟨31392076748739865541340481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41856102331653154055120641 31392076748739865541340481)
            ·
              refine ⟨23544057561554899156005361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31392076748739865541340481 23544057561554899156005361)
              ·
                refine ⟨17658043171166174367004021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23544057561554899156005361 17658043171166174367004021)
                ·
                  refine ⟨1655441547296828846906627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17658043171166174367004021 1655441547296828846906627)
                  ·
                    refine ⟨2483162320945243270359941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1655441547296828846906627 2483162320945243270359941)
                    ·
                      refine ⟨465592935177233113192489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2483162320945243270359941 465592935177233113192489)
                      ·
                        rfl

theorem cell23_906739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_906739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906739 prefixEnd_906739 := by exact prefixLift 906739
  have htrace : WordTrace (prefixWord ++ tailWord_906739) baseStart_906739 baseEnd_906739 := by
    simpa [prefixWord, tailWord_906739, baseEnd_906739] using wordTrace_append hprefix tailTrace_906739
  have hstable : (prefixWord ++ tailWord_906739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906739).length < 2 ^ (prefixWord ++ tailWord_906739).sum := by decide
  have hdescent : baseEnd_906739 < baseStart_906739 := by decide
  rcases family_descends (prefixWord ++ tailWord_906739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906769 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_906769 : Nat := 118140960795 + 906769 * 2 ^ 59
def prefixEnd_906769 : Nat := 4983230072969 + 3 ^ 40 * 906769 * 2
def baseEnd_906769 : Nat := 465608339596867995817351

theorem tailTrace_906769 : CollatzResearch.WordTrace tailWord_906769 prefixEnd_906769 465608339596867995817351 := by
  unfold tailWord_906769
  simp only [CollatzResearch.WordTrace]
  refine ⟨33072582451938251660971361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22048388301292167773980907 33072582451938251660971361)
  ·
    refine ⟨24804436838953688745728521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33072582451938251660971361 24804436838953688745728521)
    ·
      refine ⟨18603327629215266559296391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24804436838953688745728521 18603327629215266559296391)
      ·
        refine ⟨27904991443822899838944587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18603327629215266559296391 27904991443822899838944587)
        ·
          refine ⟨41857487165734349758416881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27904991443822899838944587 41857487165734349758416881)
          ·
            refine ⟨31393115374300762318812661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41857487165734349758416881 31393115374300762318812661)
            ·
              refine ⟨2943104566340696467388687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31393115374300762318812661 2943104566340696467388687)
              ·
                refine ⟨4414656849511044701083031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943104566340696467388687 4414656849511044701083031)
                ·
                  refine ⟨6621985274266567051624547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414656849511044701083031 6621985274266567051624547)
                  ·
                    refine ⟨9932977911399850577436821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621985274266567051624547 9932977911399850577436821)
                    ·
                      refine ⟨465608339596867995817351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9932977911399850577436821 465608339596867995817351)
                      ·
                        rfl

theorem cell23_906769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_906769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906769 prefixEnd_906769 := by exact prefixLift 906769
  have htrace : WordTrace (prefixWord ++ tailWord_906769) baseStart_906769 baseEnd_906769 := by
    simpa [prefixWord, tailWord_906769, baseEnd_906769] using wordTrace_append hprefix tailTrace_906769
  have hstable : (prefixWord ++ tailWord_906769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906769).length < 2 ^ (prefixWord ++ tailWord_906769).sum := by decide
  have hdescent : baseEnd_906769 < baseStart_906769 := by decide
  rcases family_descends (prefixWord ++ tailWord_906769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906773 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_906773 : Nat := 118140960795 + 906773 * 2 ^ 59
def prefixEnd_906773 : Nat := 4983230072969 + 3 ^ 40 * 906773 * 2
def baseEnd_906773 : Nat := 465610393519485980167333

theorem tailTrace_906773 : CollatzResearch.WordTrace tailWord_906773 prefixEnd_906773 465610393519485980167333 := by
  unfold tailWord_906773
  simp only [CollatzResearch.WordTrace]
  refine ⟨33072728343923760344116973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22048485562615840229411315 33072728343923760344116973)
  ·
    refine ⟨12402273128971410129043865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33072728343923760344116973 12402273128971410129043865)
    ·
      refine ⟨9301704846728557596782899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12402273128971410129043865 9301704846728557596782899)
      ·
        refine ⟨13952557270092836395174349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9301704846728557596782899 13952557270092836395174349)
        ·
          refine ⟨5232208976284813648190381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13952557270092836395174349 5232208976284813648190381)
          ·
            refine ⟨1962078366106805118071393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5232208976284813648190381 1962078366106805118071393)
            ·
              refine ⟨1471558774580103838553545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962078366106805118071393 1471558774580103838553545)
              ·
                refine ⟨1103669080935077878915159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471558774580103838553545 1103669080935077878915159)
                ·
                  refine ⟨1655503621402616818372739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103669080935077878915159 1655503621402616818372739)
                  ·
                    refine ⟨2483255432103925227559109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1655503621402616818372739 2483255432103925227559109)
                    ·
                      refine ⟨465610393519485980167333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2483255432103925227559109 465610393519485980167333)
                      ·
                        rfl

theorem cell23_906773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_906773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906773 prefixEnd_906773 := by exact prefixLift 906773
  have htrace : WordTrace (prefixWord ++ tailWord_906773) baseStart_906773 baseEnd_906773 := by
    simpa [prefixWord, tailWord_906773, baseEnd_906773] using wordTrace_append hprefix tailTrace_906773
  have hstable : (prefixWord ++ tailWord_906773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906773).length < 2 ^ (prefixWord ++ tailWord_906773).sum := by decide
  have hdescent : baseEnd_906773 < baseStart_906773 := by decide
  rcases family_descends (prefixWord ++ tailWord_906773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906786 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_906786 : Nat := 118140960795 + 906786 * 2 ^ 59
def prefixEnd_906786 : Nat := 4983230072969 + 3 ^ 40 * 906786 * 2
def baseEnd_906786 : Nat := 465617068767994429304773

theorem tailTrace_906786 : CollatzResearch.WordTrace tailWord_906786 prefixEnd_906786 465617068767994429304773 := by
  unfold tailWord_906786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8268300623219165891085053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22048801661917775709560141 8268300623219165891085053)
  ·
    refine ⟨3100612733707187209156895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8268300623219165891085053 3100612733707187209156895)
    ·
      refine ⟨4650919100560780813735343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100612733707187209156895 4650919100560780813735343)
      ·
        refine ⟨6976378650841171220603015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650919100560780813735343 6976378650841171220603015)
        ·
          refine ⟨10464567976261756830904523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976378650841171220603015 10464567976261756830904523)
          ·
            refine ⟨15696851964392635246356785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10464567976261756830904523 15696851964392635246356785)
            ·
              refine ⟨11772638973294476434767589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15696851964392635246356785 11772638973294476434767589)
              ·
                refine ⟨2207369807492714331518923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11772638973294476434767589 2207369807492714331518923)
                ·
                  refine ⟨3311054711239071497278385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207369807492714331518923 3311054711239071497278385)
                  ·
                    refine ⟨2483291033429303622958789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3311054711239071497278385 2483291033429303622958789)
                    ·
                      refine ⟨465617068767994429304773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2483291033429303622958789 465617068767994429304773)
                      ·
                        rfl

theorem cell23_906786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_906786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906786 prefixEnd_906786 := by exact prefixLift 906786
  have htrace : WordTrace (prefixWord ++ tailWord_906786) baseStart_906786 baseEnd_906786 := by
    simpa [prefixWord, tailWord_906786, baseEnd_906786] using wordTrace_append hprefix tailTrace_906786
  have hstable : (prefixWord ++ tailWord_906786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906786).length < 2 ^ (prefixWord ++ tailWord_906786).sum := by decide
  have hdescent : baseEnd_906786 < baseStart_906786 := by decide
  rcases family_descends (prefixWord ++ tailWord_906786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906816 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 7, 2]
def baseStart_906816 : Nat := 118140960795 + 906816 * 2 ^ 59
def prefixEnd_906816 : Nat := 4983230072969 + 3 ^ 40 * 906816 * 2
def baseEnd_906816 : Nat := 465632473187629311929635

theorem tailTrace_906816 : CollatzResearch.WordTrace tailWord_906816 prefixEnd_906816 465632473187629311929635 := by
  unfold tailWord_906816
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537148341383989343966151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22049531121845319125288201 16537148341383989343966151)
  ·
    refine ⟨24805722512075984015949227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16537148341383989343966151 24805722512075984015949227)
    ·
      refine ⟨37208583768113976023923841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24805722512075984015949227 37208583768113976023923841)
      ·
        refine ⟨27906437826085482017942881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37208583768113976023923841 27906437826085482017942881)
        ·
          refine ⟨20929828369564111513457161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27906437826085482017942881 20929828369564111513457161)
          ·
            refine ⟨15697371277173083635092871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20929828369564111513457161 15697371277173083635092871)
            ·
              refine ⟨23546056915759625452639307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15697371277173083635092871 23546056915759625452639307)
              ·
                refine ⟨35319085373639438178958961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23546056915759625452639307 35319085373639438178958961)
                ·
                  refine ⟨26489314030229578634219221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35319085373639438178958961 26489314030229578634219221)
                  ·
                    refine ⟨620843297583505749239513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26489314030229578634219221 620843297583505749239513)
                    ·
                      refine ⟨465632473187629311929635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620843297583505749239513 465632473187629311929635)
                      ·
                        rfl

theorem cell23_906816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_906816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906816 prefixEnd_906816 := by exact prefixLift 906816
  have htrace : WordTrace (prefixWord ++ tailWord_906816) baseStart_906816 baseEnd_906816 := by
    simpa [prefixWord, tailWord_906816, baseEnd_906816] using wordTrace_append hprefix tailTrace_906816
  have hstable : (prefixWord ++ tailWord_906816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906816).length < 2 ^ (prefixWord ++ tailWord_906816).sum := by decide
  have hdescent : baseEnd_906816 < baseStart_906816 := by decide
  rcases family_descends (prefixWord ++ tailWord_906816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906833 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 3, 3, 2]
def baseStart_906833 : Nat := 118140960795 + 906833 * 2 ^ 59
def prefixEnd_906833 : Nat := 4983230072969 + 3 ^ 40 * 906833 * 2
def baseEnd_906833 : Nat := 465641202358755745417057

theorem tailTrace_906833 : CollatzResearch.WordTrace tailWord_906833 prefixEnd_906833 465641202358755745417057 := by
  unfold tailWord_906833
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074916723706390591301153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22049944482470927060867435 33074916723706390591301153)
  ·
    refine ⟨24806187542779792943475865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33074916723706390591301153 24806187542779792943475865)
    ·
      refine ⟨18604640657084844707606899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24806187542779792943475865 18604640657084844707606899)
      ·
        refine ⟨27906960985627267061410349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18604640657084844707606899 27906960985627267061410349)
        ·
          refine ⟨10465110369610225148028881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27906960985627267061410349 10465110369610225148028881)
          ·
            refine ⟨7848832777207668861021661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10465110369610225148028881 7848832777207668861021661)
            ·
              refine ⟨2943312291452875822883123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7848832777207668861021661 2943312291452875822883123)
              ·
                refine ⟨4414968437179313734324685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943312291452875822883123 4414968437179313734324685)
                ·
                  refine ⟨1655613163942242650371757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4414968437179313734324685 1655613163942242650371757)
                  ·
                    refine ⟨620854936478340993889409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655613163942242650371757 620854936478340993889409)
                    ·
                      refine ⟨465641202358755745417057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620854936478340993889409 465641202358755745417057)
                      ·
                        rfl

theorem cell23_906833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_906833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906833 prefixEnd_906833 := by exact prefixLift 906833
  have htrace : WordTrace (prefixWord ++ tailWord_906833) baseStart_906833 baseEnd_906833 := by
    simpa [prefixWord, tailWord_906833, baseEnd_906833] using wordTrace_append hprefix tailTrace_906833
  have hstable : (prefixWord ++ tailWord_906833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906833).length < 2 ^ (prefixWord ++ tailWord_906833).sum := by decide
  have hdescent : baseEnd_906833 < baseStart_906833 := by decide
  rcases family_descends (prefixWord ++ tailWord_906833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906879 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_906879 : Nat := 118140960795 + 906879 * 2 ^ 59
def prefixEnd_906879 : Nat := 4983230072969 + 3 ^ 40 * 906879 * 2
def baseEnd_906879 : Nat := 465664822468862565441845

theorem tailTrace_906879 : CollatzResearch.WordTrace tailWord_906879 prefixEnd_906879 465664822468862565441845 := by
  unfold tailWord_906879
  simp only [CollatzResearch.WordTrace]
  refine ⟨33076594481539740447475691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22051062987693160298317127 33076594481539740447475691)
  ·
    refine ⟨49614891722309610671213537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33076594481539740447475691 49614891722309610671213537)
    ·
      refine ⟨37211168791732208003410153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49614891722309610671213537 37211168791732208003410153)
      ·
        refine ⟨27908376593799156002557615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37211168791732208003410153 27908376593799156002557615)
        ·
          refine ⟨41862564890698734003836423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27908376593799156002557615 41862564890698734003836423)
          ·
            refine ⟨62793847336048101005754635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41862564890698734003836423 62793847336048101005754635)
            ·
              refine ⟨94190771004072151508631953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62793847336048101005754635 94190771004072151508631953)
              ·
                refine ⟨70643078253054113631473965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94190771004072151508631953 70643078253054113631473965)
                ·
                  refine ⟨26491154344895292611802737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70643078253054113631473965 26491154344895292611802737)
                  ·
                    refine ⟨19868365758671469458852053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26491154344895292611802737 19868365758671469458852053)
                    ·
                      refine ⟨465664822468862565441845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19868365758671469458852053 465664822468862565441845)
                      ·
                        rfl

theorem cell23_906879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_906879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906879 prefixEnd_906879 := by exact prefixLift 906879
  have htrace : WordTrace (prefixWord ++ tailWord_906879) baseStart_906879 baseEnd_906879 := by
    simpa [prefixWord, tailWord_906879, baseEnd_906879] using wordTrace_append hprefix tailTrace_906879
  have hstable : (prefixWord ++ tailWord_906879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906879).length < 2 ^ (prefixWord ++ tailWord_906879).sum := by decide
  have hdescent : baseEnd_906879 < baseStart_906879 := by decide
  rcases family_descends (prefixWord ++ tailWord_906879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906880 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 2, 2, 2]
def baseStart_906880 : Nat := 118140960795 + 906880 * 2 ^ 59
def prefixEnd_906880 : Nat := 4983230072969 + 3 ^ 40 * 906880 * 2
def baseEnd_906880 : Nat := 465665335949517061529341

theorem tailTrace_906880 : CollatzResearch.WordTrace tailWord_906880 prefixEnd_906880 465665335949517061529341 := by
  unfold tailWord_906880
  simp only [CollatzResearch.WordTrace]
  refine ⟨16538315477268058809131047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22051087303024078412174729 16538315477268058809131047)
  ·
    refine ⟨24807473215902088213696571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16538315477268058809131047 24807473215902088213696571)
    ·
      refine ⟨37211209823853132320544857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24807473215902088213696571 37211209823853132320544857)
      ·
        refine ⟨27908407367889849240408643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37211209823853132320544857 27908407367889849240408643)
        ·
          refine ⟨41862611051834773860612965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27908407367889849240408643 41862611051834773860612965)
          ·
            refine ⟨7849239572219020098864931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41862611051834773860612965 7849239572219020098864931)
            ·
              refine ⟨11773859358328530148297397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849239572219020098864931 11773859358328530148297397)
              ·
                refine ⟨1103799314843299701402881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11773859358328530148297397 1103799314843299701402881)
                ·
                  refine ⟨827849486132474776052161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1103799314843299701402881 827849486132474776052161)
                  ·
                    refine ⟨620887114599356082039121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 827849486132474776052161 620887114599356082039121)
                    ·
                      refine ⟨465665335949517061529341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620887114599356082039121 465665335949517061529341)
                      ·
                        rfl

theorem cell23_906880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_906880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906880 prefixEnd_906880 := by exact prefixLift 906880
  have htrace : WordTrace (prefixWord ++ tailWord_906880) baseStart_906880 baseEnd_906880 := by
    simpa [prefixWord, tailWord_906880, baseEnd_906880] using wordTrace_append hprefix tailTrace_906880
  have hstable : (prefixWord ++ tailWord_906880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906880).length < 2 ^ (prefixWord ++ tailWord_906880).sum := by decide
  have hdescent : baseEnd_906880 < baseStart_906880 := by decide
  rcases family_descends (prefixWord ++ tailWord_906880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906903 : List Nat := [1, 1, 3, 3, 2, 2, 1, 5, 5]
def baseStart_906903 : Nat := 118140960795 + 906903 * 2 ^ 59
def prefixEnd_906903 : Nat := 4983230072969 + 3 ^ 40 * 906903 * 2
def baseEnd_906903 : Nat := 51741905111618941282415

theorem tailTrace_906903 : CollatzResearch.WordTrace tailWord_906903 prefixEnd_906903 51741905111618941282415 := by
  unfold tailWord_906903
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077469833452792546349363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22051646555635195030899575 33077469833452792546349363)
  ·
    refine ⟨49616204750179188819524045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33077469833452792546349363 49616204750179188819524045)
    ·
      refine ⟨18606076781317195807321517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49616204750179188819524045 18606076781317195807321517)
      ·
        refine ⟨6977278792993948427745569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18606076781317195807321517 6977278792993948427745569)
        ·
          refine ⟨5232959094745461320809177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6977278792993948427745569 5232959094745461320809177)
          ·
            refine ⟨3924719321059095990606883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5232959094745461320809177 3924719321059095990606883)
            ·
              refine ⟨5887078981588643985910325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924719321059095990606883 5887078981588643985910325)
              ·
                refine ⟨551913654523935373679093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5887078981588643985910325 551913654523935373679093)
                ·
                  refine ⟨51741905111618941282415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 551913654523935373679093 51741905111618941282415)
                  ·
                    rfl

theorem cell23_906903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 5].length) (baseStart_906903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906903 prefixEnd_906903 := by exact prefixLift 906903
  have htrace : WordTrace (prefixWord ++ tailWord_906903) baseStart_906903 baseEnd_906903 := by
    simpa [prefixWord, tailWord_906903, baseEnd_906903] using wordTrace_append hprefix tailTrace_906903
  have hstable : (prefixWord ++ tailWord_906903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906903).length < 2 ^ (prefixWord ++ tailWord_906903).sum := by decide
  have hdescent : baseEnd_906903 < baseStart_906903 := by decide
  rcases family_descends (prefixWord ++ tailWord_906903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906913 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_906913 : Nat := 118140960795 + 906913 * 2 ^ 59
def prefixEnd_906913 : Nat := 4983230072969 + 3 ^ 40 * 906913 * 2
def baseEnd_906913 : Nat := 465682280811115432416689

theorem tailTrace_906913 : CollatzResearch.WordTrace tailWord_906913 prefixEnd_906913 465682280811115432416689 := by
  unfold tailWord_906913
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077834563416564254213393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22051889708944376169475595 33077834563416564254213393)
  ·
    refine ⟨24808375922562423190660045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33077834563416564254213393 24808375922562423190660045)
    ·
      refine ⟨9303140970960908696497517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24808375922562423190660045 9303140970960908696497517)
      ·
        refine ⟨3488677864110340761186569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9303140970960908696497517 3488677864110340761186569)
        ·
          refine ⟨2616508398082755570889927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488677864110340761186569 2616508398082755570889927)
          ·
            refine ⟨3924762597124133356334891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616508398082755570889927 3924762597124133356334891)
            ·
              refine ⟨5887143895686200034502337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924762597124133356334891 5887143895686200034502337)
              ·
                refine ⟨4415357921764650025876753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887143895686200034502337 4415357921764650025876753)
                ·
                  refine ⟨3311518441323487519407565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415357921764650025876753 3311518441323487519407565)
                  ·
                    refine ⟨1241819415496307819777837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311518441323487519407565 1241819415496307819777837)
                    ·
                      refine ⟨465682280811115432416689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1241819415496307819777837 465682280811115432416689)
                      ·
                        rfl

theorem cell23_906913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_906913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906913 prefixEnd_906913 := by exact prefixLift 906913
  have htrace : WordTrace (prefixWord ++ tailWord_906913) baseStart_906913 baseEnd_906913 := by
    simpa [prefixWord, tailWord_906913, baseEnd_906913] using wordTrace_append hprefix tailTrace_906913
  have hstable : (prefixWord ++ tailWord_906913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906913).length < 2 ^ (prefixWord ++ tailWord_906913).sum := by decide
  have hdescent : baseEnd_906913 < baseStart_906913 := by decide
  rcases family_descends (prefixWord ++ tailWord_906913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906914 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_906914 : Nat := 118140960795 + 906914 * 2 ^ 59
def prefixEnd_906914 : Nat := 4983230072969 + 3 ^ 40 * 906914 * 2
def baseEnd_906914 : Nat := 465682794291769928504185

theorem tailTrace_906914 : CollatzResearch.WordTrace tailWord_906914 prefixEnd_906914 465682794291769928504185 := by
  unfold tailWord_906914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8269467759103235356249949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22051914024275294283333197 8269467759103235356249949)
  ·
    refine ⟨3101050409663713258593731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8269467759103235356249949 3101050409663713258593731)
    ·
      refine ⟨4651575614495569887890597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101050409663713258593731 4651575614495569887890597)
      ·
        refine ⟨872170427717919353979487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4651575614495569887890597 872170427717919353979487)
        ·
          refine ⟨1308255641576879030969231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872170427717919353979487 1308255641576879030969231)
          ·
            refine ⟨1962383462365318546453847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308255641576879030969231 1962383462365318546453847)
            ·
              refine ⟨2943575193547977819680771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962383462365318546453847 2943575193547977819680771)
              ·
                refine ⟨4415362790321966729521157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943575193547977819680771 4415362790321966729521157)
                ·
                  refine ⟨827880523185368761785217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4415362790321966729521157 827880523185368761785217)
                  ·
                    refine ⟨620910392389026571338913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 827880523185368761785217 620910392389026571338913)
                    ·
                      refine ⟨465682794291769928504185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 620910392389026571338913 465682794291769928504185)
                      ·
                        rfl

theorem cell23_906914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_906914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906914 prefixEnd_906914 := by exact prefixLift 906914
  have htrace : WordTrace (prefixWord ++ tailWord_906914) baseStart_906914 baseEnd_906914 := by
    simpa [prefixWord, tailWord_906914, baseEnd_906914] using wordTrace_append hprefix tailTrace_906914
  have hstable : (prefixWord ++ tailWord_906914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906914).length < 2 ^ (prefixWord ++ tailWord_906914).sum := by decide
  have hdescent : baseEnd_906914 < baseStart_906914 := by decide
  rcases family_descends (prefixWord ++ tailWord_906914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906976 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 8]
def baseStart_906976 : Nat := 118140960795 + 906976 * 2 ^ 59
def prefixEnd_906976 : Nat := 4983230072969 + 3 ^ 40 * 906976 * 2
def baseEnd_906976 : Nat := 51746070010260965103211

theorem tailTrace_906976 : CollatzResearch.WordTrace tailWord_906976 prefixEnd_906976 51746070010260965103211 := by
  unfold tailWord_906976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16540066181094163006878391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22053421574792217342504521 16540066181094163006878391)
  ·
    refine ⟨24810099271641244510317587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16540066181094163006878391 24810099271641244510317587)
    ·
      refine ⟨37215148907461866765476381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24810099271641244510317587 37215148907461866765476381)
      ·
        refine ⟨13955680840298200037053643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37215148907461866765476381 13955680840298200037053643)
        ·
          refine ⟨20933521260447300055580465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13955680840298200037053643 20933521260447300055580465)
          ·
            refine ⟨15700140945335475041685349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20933521260447300055580465 15700140945335475041685349)
            ·
              refine ⟨2943776427250401570316003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15700140945335475041685349 2943776427250401570316003)
              ·
                refine ⟨4415664640875602355474005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943776427250401570316003 4415664640875602355474005)
                ·
                  refine ⟨51746070010260965103211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4415664640875602355474005 51746070010260965103211)
                  ·
                    rfl

theorem cell23_906976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_906976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906976 prefixEnd_906976 := by exact prefixLift 906976
  have htrace : WordTrace (prefixWord ++ tailWord_906976) baseStart_906976 baseEnd_906976 := by
    simpa [prefixWord, tailWord_906976, baseEnd_906976] using wordTrace_append hprefix tailTrace_906976
  have hstable : (prefixWord ++ tailWord_906976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906976).length < 2 ^ (prefixWord ++ tailWord_906976).sum := by decide
  have hdescent : baseEnd_906976 < baseStart_906976 := by decide
  rcases family_descends (prefixWord ++ tailWord_906976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906993 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 6]
def baseStart_906993 : Nat := 118140960795 + 906993 * 2 ^ 59
def prefixEnd_906993 : Nat := 4983230072969 + 3 ^ 40 * 906993 * 2
def baseEnd_906993 : Nat := 51747039918163902157369

theorem tailTrace_906993 : CollatzResearch.WordTrace tailWord_906993 prefixEnd_906993 51747039918163902157369 := by
  unfold tailWord_906993
  simp only [CollatzResearch.WordTrace]
  refine ⟨33080752403126737917125633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22053834935417825278083755 33080752403126737917125633)
  ·
    refine ⟨24810564302345053437844225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33080752403126737917125633 24810564302345053437844225)
    ·
      refine ⟨18607923226758790078383169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24810564302345053437844225 18607923226758790078383169)
      ·
        refine ⟨13955942420069092558787377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18607923226758790078383169 13955942420069092558787377)
        ·
          refine ⟨10466956815051819419090533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13955942420069092558787377 10466956815051819419090533)
          ·
            refine ⟨1962554402822216141079475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10466956815051819419090533 1962554402822216141079475)
            ·
              refine ⟨2943831604233324211619213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962554402822216141079475 2943831604233324211619213)
              ·
                refine ⟨1103936851587496579357205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2943831604233324211619213 1103936851587496579357205)
                ·
                  refine ⟨51747039918163902157369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1103936851587496579357205 51747039918163902157369)
                  ·
                    rfl

theorem cell23_906993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 6].length) (baseStart_906993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_906993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_906993 prefixEnd_906993 := by exact prefixLift 906993
  have htrace : WordTrace (prefixWord ++ tailWord_906993) baseStart_906993 baseEnd_906993 := by
    simpa [prefixWord, tailWord_906993, baseEnd_906993] using wordTrace_append hprefix tailTrace_906993
  have hstable : (prefixWord ++ tailWord_906993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906993).length < 2 ^ (prefixWord ++ tailWord_906993).sum := by decide
  have hdescent : baseEnd_906993 < baseStart_906993 := by decide
  rcases family_descends (prefixWord ++ tailWord_906993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907043 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 4]
def baseStart_907043 : Nat := 118140960795 + 907043 * 2 ^ 59
def prefixEnd_907043 : Nat := 4983230072969 + 3 ^ 40 * 907043 * 2
def baseEnd_907043 : Nat := 465749033296199923791091

theorem tailTrace_907043 : CollatzResearch.WordTrace tailWord_907043 prefixEnd_907043 465749033296199923791091 := by
  unfold tailWord_907043
  simp only [CollatzResearch.WordTrace]
  refine ⟨33082576052945596456445783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22055050701963730970963855 33082576052945596456445783)
  ·
    refine ⟨49623864079418394684668675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33082576052945596456445783 49623864079418394684668675)
    ·
      refine ⟨74435796119127592027003013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49623864079418394684668675 74435796119127592027003013)
      ·
        refine ⟨13956711772336423505063065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74435796119127592027003013 13956711772336423505063065)
        ·
          refine ⟨10467533829252317628797299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13956711772336423505063065 10467533829252317628797299)
          ·
            refine ⟨15701300743878476443195949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467533829252317628797299 15701300743878476443195949)
            ·
              refine ⟨5887987778954428666198481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15701300743878476443195949 5887987778954428666198481)
              ·
                refine ⟨4415990834215821499648861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887987778954428666198481 4415990834215821499648861)
                ·
                  refine ⟨1655996562830933062368323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4415990834215821499648861 1655996562830933062368323)
                  ·
                    refine ⟨2483994844246399593552485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1655996562830933062368323 2483994844246399593552485)
                    ·
                      refine ⟨465749033296199923791091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2483994844246399593552485 465749033296199923791091)
                      ·
                        rfl

theorem cell23_907043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_907043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907043 prefixEnd_907043 := by exact prefixLift 907043
  have htrace : WordTrace (prefixWord ++ tailWord_907043) baseStart_907043 baseEnd_907043 := by
    simpa [prefixWord, tailWord_907043, baseEnd_907043] using wordTrace_append hprefix tailTrace_907043
  have hstable : (prefixWord ++ tailWord_907043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907043).length < 2 ^ (prefixWord ++ tailWord_907043).sum := by decide
  have hdescent : baseEnd_907043 < baseStart_907043 := by decide
  rcases family_descends (prefixWord ++ tailWord_907043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907054 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_907054 : Nat := 118140960795 + 907054 * 2 ^ 59
def prefixEnd_907054 : Nat := 4983230072969 + 3 ^ 40 * 907054 * 2
def baseEnd_907054 : Nat := 465754681583399380753541

theorem tailTrace_907054 : CollatzResearch.WordTrace tailWord_907054 prefixEnd_907054 465754681583399380753541 := by
  unfold tailWord_907054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135372156988218166887027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22055318170603830223397477 4135372156988218166887027)
  ·
    refine ⟨6203058235482327250330541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4135372156988218166887027 6203058235482327250330541)
    ·
      refine ⟨2326146838305872718873953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6203058235482327250330541 2326146838305872718873953)
      ·
        refine ⟨1744610128729404539155465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326146838305872718873953 1744610128729404539155465)
        ·
          refine ⟨1308457596547053404366599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744610128729404539155465 1308457596547053404366599)
          ·
            refine ⟨1962686394820580106549899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308457596547053404366599 1962686394820580106549899)
            ·
              refine ⟨2944029592230870159824849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962686394820580106549899 2944029592230870159824849)
              ·
                refine ⟨2208022194173152619868637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944029592230870159824849 2208022194173152619868637)
                ·
                  refine ⟨828008322814932232450739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2208022194173152619868637 828008322814932232450739)
                  ·
                    refine ⟨1242012484222398348676109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 828008322814932232450739 1242012484222398348676109)
                    ·
                      refine ⟨465754681583399380753541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1242012484222398348676109 465754681583399380753541)
                      ·
                        rfl

theorem cell23_907054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_907054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907054 prefixEnd_907054 := by exact prefixLift 907054
  have htrace : WordTrace (prefixWord ++ tailWord_907054) baseStart_907054 baseEnd_907054 := by
    simpa [prefixWord, tailWord_907054, baseEnd_907054] using wordTrace_append hprefix tailTrace_907054
  have hstable : (prefixWord ++ tailWord_907054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907054).length < 2 ^ (prefixWord ++ tailWord_907054).sum := by decide
  have hdescent : baseEnd_907054 < baseStart_907054 := by decide
  rcases family_descends (prefixWord ++ tailWord_907054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907070 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_907070 : Nat := 118140960795 + 907070 * 2 ^ 59
def prefixEnd_907070 : Nat := 4983230072969 + 3 ^ 40 * 907070 * 2
def baseEnd_907070 : Nat := 155254299091290439384489

theorem tailTrace_907070 : CollatzResearch.WordTrace tailWord_907070 prefixEnd_907070 155254299091290439384489 := by
  unfold tailWord_907070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135445102980972508459833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22055707215898520045119109 4135445102980972508459833)
  ·
    refine ⟨3101583827235729381344875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4135445102980972508459833 3101583827235729381344875)
    ·
      refine ⟨4652375740853594072017313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101583827235729381344875 4652375740853594072017313)
      ·
        refine ⟨3489281805640195554012985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4652375740853594072017313 3489281805640195554012985)
        ·
          refine ⟨2616961354230146665509739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3489281805640195554012985 2616961354230146665509739)
          ·
            refine ⟨3925442031345219998264609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616961354230146665509739 3925442031345219998264609)
            ·
              refine ⟨2944081523508914998698457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925442031345219998264609 2944081523508914998698457)
              ·
                refine ⟨2208061142631686249023843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944081523508914998698457 2208061142631686249023843)
                ·
                  refine ⟨3312091713947529373535765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208061142631686249023843 3312091713947529373535765)
                  ·
                    refine ⟨155254299091290439384489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3312091713947529373535765 155254299091290439384489)
                    ·
                      rfl

theorem cell23_907070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_907070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907070 prefixEnd_907070 := by exact prefixLift 907070
  have htrace : WordTrace (prefixWord ++ tailWord_907070) baseStart_907070 baseEnd_907070 := by
    simpa [prefixWord, tailWord_907070, baseEnd_907070] using wordTrace_append hprefix tailTrace_907070
  have hstable : (prefixWord ++ tailWord_907070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907070).length < 2 ^ (prefixWord ++ tailWord_907070).sum := by decide
  have hdescent : baseEnd_907070 < baseStart_907070 := by decide
  rcases family_descends (prefixWord ++ tailWord_907070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907107 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 4]
def baseStart_907107 : Nat := 118140960795 + 907107 * 2 ^ 59
def prefixEnd_907107 : Nat := 4983230072969 + 3 ^ 40 * 907107 * 2
def baseEnd_907107 : Nat := 465781896058087673390797

theorem tailTrace_907107 : CollatzResearch.WordTrace tailWord_907107 prefixEnd_907107 465781896058087673390797 := by
  unfold tailWord_907107
  simp only [CollatzResearch.WordTrace]
  refine ⟨33084910324713735386775575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22056606883142490257850383 33084910324713735386775575)
  ·
    refine ⟨49627365487070603080163363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33084910324713735386775575 49627365487070603080163363)
    ·
      refine ⟨74441048230605904620245045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49627365487070603080163363 74441048230605904620245045)
      ·
        refine ⟨6978848271619303558147973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74441048230605904620245045 6978848271619303558147973)
        ·
          refine ⟨1308534050928619417152745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6978848271619303558147973 1308534050928619417152745)
          ·
            refine ⟨981400538196464562864559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308534050928619417152745 981400538196464562864559)
            ·
              refine ⟨1472100807294696844296839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981400538196464562864559 1472100807294696844296839)
              ·
                refine ⟨2208151210942045266445259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472100807294696844296839 2208151210942045266445259)
                ·
                  refine ⟨3312226816413067899667889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208151210942045266445259 3312226816413067899667889)
                  ·
                    refine ⟨2484170112309800924750917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3312226816413067899667889 2484170112309800924750917)
                    ·
                      refine ⟨465781896058087673390797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2484170112309800924750917 465781896058087673390797)
                      ·
                        rfl

theorem cell23_907107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_907107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907107 prefixEnd_907107 := by exact prefixLift 907107
  have htrace : WordTrace (prefixWord ++ tailWord_907107) baseStart_907107 baseEnd_907107 := by
    simpa [prefixWord, tailWord_907107, baseEnd_907107] using wordTrace_append hprefix tailTrace_907107
  have hstable : (prefixWord ++ tailWord_907107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907107).length < 2 ^ (prefixWord ++ tailWord_907107).sum := by decide
  have hdescent : baseEnd_907107 < baseStart_907107 := by decide
  rcases family_descends (prefixWord ++ tailWord_907107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907133 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_907133 : Nat := 118140960795 + 907133 * 2 ^ 59
def prefixEnd_907133 : Nat := 4983230072969 + 3 ^ 40 * 907133 * 2
def baseEnd_907133 : Nat := 465795246555104571665677

theorem tailTrace_907133 : CollatzResearch.WordTrace tailWord_907133 prefixEnd_907133 465795246555104571665677 := by
  unfold tailWord_907133
  simp only [CollatzResearch.WordTrace]
  refine ⟨33085858622619541827222053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22057239081746361218148035 33085858622619541827222053)
  ·
    refine ⟨6203598491741164092604135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33085858622619541827222053 6203598491741164092604135)
    ·
      refine ⟨9305397737611746138906203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6203598491741164092604135 9305397737611746138906203)
      ·
        refine ⟨13958096606417619208359305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9305397737611746138906203 13958096606417619208359305)
        ·
          refine ⟨10468572454813214406269479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13958096606417619208359305 10468572454813214406269479)
          ·
            refine ⟨15702858682219821609404219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468572454813214406269479 15702858682219821609404219)
            ·
              refine ⟨23554288023329732414106329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15702858682219821609404219 23554288023329732414106329)
              ·
                refine ⟨17665716017497299310579747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23554288023329732414106329 17665716017497299310579747)
                ·
                  refine ⟨26498574026245948965869621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17665716017497299310579747 26498574026245948965869621)
                  ·
                    refine ⟨2484241314960557715550277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26498574026245948965869621 2484241314960557715550277)
                    ·
                      refine ⟨465795246555104571665677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2484241314960557715550277 465795246555104571665677)
                      ·
                        rfl

theorem cell23_907133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_907133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907133 prefixEnd_907133 := by exact prefixLift 907133
  have htrace : WordTrace (prefixWord ++ tailWord_907133) baseStart_907133 baseEnd_907133 := by
    simpa [prefixWord, tailWord_907133, baseEnd_907133] using wordTrace_append hprefix tailTrace_907133
  have hstable : (prefixWord ++ tailWord_907133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907133).length < 2 ^ (prefixWord ++ tailWord_907133).sum := by decide
  have hdescent : baseEnd_907133 < baseStart_907133 := by decide
  rcases family_descends (prefixWord ++ tailWord_907133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907173 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 7]
def baseStart_907173 : Nat := 118140960795 + 907173 * 2 ^ 59
def prefixEnd_907173 : Nat := 4983230072969 + 3 ^ 40 * 907173 * 2
def baseEnd_907173 : Nat := 51757309531253823907277

theorem tailTrace_907173 : CollatzResearch.WordTrace tailWord_907173 prefixEnd_907173 51757309531253823907277 := by
  unfold tailWord_907173
  simp only [CollatzResearch.WordTrace]
  refine ⟨33087317542474628658678173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22058211694983085772452115 33087317542474628658678173)
  ·
    refine ⟨12407744078427985747004315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33087317542474628658678173 12407744078427985747004315)
    ·
      refine ⟨18611616117641978620506473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12407744078427985747004315 18611616117641978620506473)
      ·
        refine ⟨13958712088231483965379855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18611616117641978620506473 13958712088231483965379855)
        ·
          refine ⟨20938068132347225948069783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13958712088231483965379855 20938068132347225948069783)
          ·
            refine ⟨31407102198520838922104675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20938068132347225948069783 31407102198520838922104675)
            ·
              refine ⟨47110653297781258383157013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31407102198520838922104675 47110653297781258383157013)
              ·
                refine ⟨2208311873333496486710485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47110653297781258383157013 2208311873333496486710485)
                ·
                  refine ⟨51757309531253823907277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2208311873333496486710485 51757309531253823907277)
                  ·
                    rfl

theorem cell23_907173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_907173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907173 prefixEnd_907173 := by exact prefixLift 907173
  have htrace : WordTrace (prefixWord ++ tailWord_907173) baseStart_907173 baseEnd_907173 := by
    simpa [prefixWord, tailWord_907173, baseEnd_907173] using wordTrace_append hprefix tailTrace_907173
  have hstable : (prefixWord ++ tailWord_907173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907173).length < 2 ^ (prefixWord ++ tailWord_907173).sum := by decide
  have hdescent : baseEnd_907173 < baseStart_907173 := by decide
  rcases family_descends (prefixWord ++ tailWord_907173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907200 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3]
def baseStart_907200 : Nat := 118140960795 + 907200 * 2 ^ 59
def prefixEnd_907200 : Nat := 4983230072969 + 3 ^ 40 * 907200 * 2
def baseEnd_907200 : Nat := 465829649758955809527869

theorem tailTrace_907200 : CollatzResearch.WordTrace tailWord_907200 prefixEnd_907200 465829649758955809527869 := by
  unfold tailWord_907200
  simp only [CollatzResearch.WordTrace]
  refine ⟨16544151156688406134955527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22058868208917874846607369 16544151156688406134955527)
  ·
    refine ⟨24816226735032609202433291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16544151156688406134955527 24816226735032609202433291)
    ·
      refine ⟨37224340102548913803649937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24816226735032609202433291 37224340102548913803649937)
      ·
        refine ⟨27918255076911685352737453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37224340102548913803649937 27918255076911685352737453)
        ·
          refine ⟨10469345653841882007276545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27918255076911685352737453 10469345653841882007276545)
          ·
            refine ⟨7852009240381411505457409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10469345653841882007276545 7852009240381411505457409)
            ·
              refine ⟨5889006930286058629093057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852009240381411505457409 5889006930286058629093057)
              ·
                refine ⟨4416755197714543971819793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5889006930286058629093057 4416755197714543971819793)
                ·
                  refine ⟨3312566398285907978864845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4416755197714543971819793 3312566398285907978864845)
                  ·
                    refine ⟨1242212399357215492074317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3312566398285907978864845 1242212399357215492074317)
                    ·
                      refine ⟨465829649758955809527869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1242212399357215492074317 465829649758955809527869)
                      ·
                        rfl

theorem cell23_907200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_907200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907200 prefixEnd_907200 := by exact prefixLift 907200
  have htrace : WordTrace (prefixWord ++ tailWord_907200) baseStart_907200 baseEnd_907200 := by
    simpa [prefixWord, tailWord_907200, baseEnd_907200] using wordTrace_append hprefix tailTrace_907200
  have hstable : (prefixWord ++ tailWord_907200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907200).length < 2 ^ (prefixWord ++ tailWord_907200).sum := by decide
  have hdescent : baseEnd_907200 < baseStart_907200 := by decide
  rcases family_descends (prefixWord ++ tailWord_907200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907220 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_907220 : Nat := 118140960795 + 907220 * 2 ^ 59
def prefixEnd_907220 : Nat := 4983230072969 + 3 ^ 40 * 907220 * 2
def baseEnd_907220 : Nat := 155279973124015243759259

theorem tailTrace_907220 : CollatzResearch.WordTrace tailWord_907220 prefixEnd_907220 155279973124015243759259 := by
  unfold tailWord_907220
  simp only [CollatzResearch.WordTrace]
  refine ⟨16544515886652177842819557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22059354515536237123759409 16544515886652177842819557)
  ·
    refine ⟨3102096728747283345528667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16544515886652177842819557 3102096728747283345528667)
    ·
      refine ⟨4653145093120925018293001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3102096728747283345528667 4653145093120925018293001)
      ·
        refine ⟨3489858819840693763719751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653145093120925018293001 3489858819840693763719751)
        ·
          refine ⟨5234788229761040645579627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3489858819840693763719751 5234788229761040645579627)
          ·
            refine ⟨7852182344641560968369441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234788229761040645579627 7852182344641560968369441)
            ·
              refine ⟨5889136758481170726277081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852182344641560968369441 5889136758481170726277081)
              ·
                refine ⟨4416852568860878044707811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5889136758481170726277081 4416852568860878044707811)
                ·
                  refine ⟨6625278853291317067061717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416852568860878044707811 6625278853291317067061717)
                  ·
                    refine ⟨155279973124015243759259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6625278853291317067061717 155279973124015243759259)
                    ·
                      rfl

theorem cell23_907220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_907220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907220 prefixEnd_907220 := by exact prefixLift 907220
  have htrace : WordTrace (prefixWord ++ tailWord_907220) baseStart_907220 baseEnd_907220 := by
    simpa [prefixWord, tailWord_907220, baseEnd_907220] using wordTrace_append hprefix tailTrace_907220
  have hstable : (prefixWord ++ tailWord_907220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907220).length < 2 ^ (prefixWord ++ tailWord_907220).sum := by decide
  have hdescent : baseEnd_907220 < baseStart_907220 := by decide
  rcases family_descends (prefixWord ++ tailWord_907220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907257 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 2, 4, 2]
def baseStart_907257 : Nat := 118140960795 + 907257 * 2 ^ 59
def prefixEnd_907257 : Nat := 4983230072969 + 3 ^ 40 * 907257 * 2
def baseEnd_907257 : Nat := 465858918156262086515107

theorem tailTrace_907257 : CollatzResearch.WordTrace tailWord_907257 prefixEnd_907257 465858918156262086515107 := by
  unfold tailWord_907257
  simp only [CollatzResearch.WordTrace]
  refine ⟨33090381274170311004736025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22060254182780207336490683 33090381274170311004736025)
  ·
    refine ⟨24817785955627733253552019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33090381274170311004736025 24817785955627733253552019)
    ·
      refine ⟨37226678933441599880328029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24817785955627733253552019 37226678933441599880328029)
      ·
        refine ⟨13960004600040599955123011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37226678933441599880328029 13960004600040599955123011)
        ·
          refine ⟨20940006900060899932684517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13960004600040599955123011 20940006900060899932684517)
          ·
            refine ⟨3926251293761418737378347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20940006900060899932684517 3926251293761418737378347)
            ·
              refine ⟨5889376940642128106067521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926251293761418737378347 5889376940642128106067521)
              ·
                refine ⟨4417032705481596079550641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5889376940642128106067521 4417032705481596079550641)
                ·
                  refine ⟨3312774529111197059662981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4417032705481596079550641 3312774529111197059662981)
                  ·
                    refine ⟨621145224208349448686809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312774529111197059662981 621145224208349448686809)
                    ·
                      refine ⟨465858918156262086515107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621145224208349448686809 465858918156262086515107)
                      ·
                        rfl

theorem cell23_907257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_907257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907257 prefixEnd_907257 := by exact prefixLift 907257
  have htrace : WordTrace (prefixWord ++ tailWord_907257) baseStart_907257 baseEnd_907257 := by
    simpa [prefixWord, tailWord_907257, baseEnd_907257] using wordTrace_append hprefix tailTrace_907257
  have hstable : (prefixWord ++ tailWord_907257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907257).length < 2 ^ (prefixWord ++ tailWord_907257).sum := by decide
  have hdescent : baseEnd_907257 < baseStart_907257 := by decide
  rcases family_descends (prefixWord ++ tailWord_907257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907301 : List Nat := [1, 3, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_907301 : Nat := 118140960795 + 907301 * 2 ^ 59
def prefixEnd_907301 : Nat := 4983230072969 + 3 ^ 40 * 907301 * 2
def baseEnd_907301 : Nat := 155293837101686638121635

theorem tailTrace_907301 : CollatzResearch.WordTrace tailWord_907301 prefixEnd_907301 155293837101686638121635 := by
  unfold tailWord_907301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33091986086010906519337757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22061324057340604346225171 33091986086010906519337757)
  ·
    refine ⟨12409494782254089944751659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33091986086010906519337757 12409494782254089944751659)
    ·
      refine ⟨18614242173381134917127489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409494782254089944751659 18614242173381134917127489)
      ·
        refine ⟨13960681630035851187845617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18614242173381134917127489 13960681630035851187845617)
        ·
          refine ⟨10470511222526888390884213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13960681630035851187845617 10470511222526888390884213)
          ·
            refine ⟨981610427111895786645395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10470511222526888390884213 981610427111895786645395)
            ·
              refine ⟨1472415640667843679968093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981610427111895786645395 1472415640667843679968093)
              ·
                refine ⟨552155865250441379988035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472415640667843679968093 552155865250441379988035)
                ·
                  refine ⟨828233797875662069982053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552155865250441379988035 828233797875662069982053)
                  ·
                    refine ⟨155293837101686638121635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 828233797875662069982053 155293837101686638121635)
                    ·
                      rfl

theorem cell23_907301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_907301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907301 prefixEnd_907301 := by exact prefixLift 907301
  have htrace : WordTrace (prefixWord ++ tailWord_907301) baseStart_907301 baseEnd_907301 := by
    simpa [prefixWord, tailWord_907301, baseEnd_907301] using wordTrace_append hprefix tailTrace_907301
  have hstable : (prefixWord ++ tailWord_907301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907301).length < 2 ^ (prefixWord ++ tailWord_907301).sum := by decide
  have hdescent : baseEnd_907301 < baseStart_907301 := by decide
  rcases family_descends (prefixWord ++ tailWord_907301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907318 : List Nat := [5, 1, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_907318 : Nat := 118140960795 + 907318 * 2 ^ 59
def prefixEnd_907318 : Nat := 4983230072969 + 3 ^ 40 * 907318 * 2
def baseEnd_907318 : Nat := 155296746825395449284109

theorem tailTrace_907318 : CollatzResearch.WordTrace tailWord_907318 prefixEnd_907318 155296746825395449284109 := by
  unfold tailWord_907318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068287882934332401419163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22061737417966212281804405 2068287882934332401419163)
  ·
    refine ⟨3102431824401498602128745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2068287882934332401419163 3102431824401498602128745)
    ·
      refine ⟨2326823868301123951596559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3102431824401498602128745 2326823868301123951596559)
      ·
        refine ⟨3490235802451685927394839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2326823868301123951596559 3490235802451685927394839)
        ·
          refine ⟨5235353703677528891092259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490235802451685927394839 5235353703677528891092259)
          ·
            refine ⟨7853030555516293336638389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235353703677528891092259 7853030555516293336638389)
            ·
              refine ⟨736221614579652500309849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7853030555516293336638389 736221614579652500309849)
              ·
                refine ⟨552166210934739375232387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736221614579652500309849 552166210934739375232387)
                ·
                  refine ⟨828249316402109062848581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552166210934739375232387 828249316402109062848581)
                  ·
                    refine ⟨155296746825395449284109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 828249316402109062848581 155296746825395449284109)
                    ·
                      rfl

theorem cell23_907318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_907318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907318 prefixEnd_907318 := by exact prefixLift 907318
  have htrace : WordTrace (prefixWord ++ tailWord_907318) baseStart_907318 baseEnd_907318 := by
    simpa [prefixWord, tailWord_907318, baseEnd_907318] using wordTrace_append hprefix tailTrace_907318
  have hstable : (prefixWord ++ tailWord_907318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907318).length < 2 ^ (prefixWord ++ tailWord_907318).sum := by decide
  have hdescent : baseEnd_907318 < baseStart_907318 := by decide
  rcases family_descends (prefixWord ++ tailWord_907318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907370 : List Nat := [3, 1, 3, 2, 14]
def baseStart_907370 : Nat := 118140960795 + 907370 * 2 ^ 59
def prefixEnd_907370 : Nat := 4983230072969 + 3 ^ 40 * 907370 * 2
def baseEnd_907370 : Nat := 639117889533909663103

theorem tailTrace_907370 : CollatzResearch.WordTrace tailWord_907370 prefixEnd_907370 639117889533909663103 := by
  unfold tailWord_907370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8273625680690232825899891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22063001815173954202399709 8273625680690232825899891)
  ·
    refine ⟨12410438521035349238849837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8273625680690232825899891 12410438521035349238849837)
    ·
      refine ⟨4653914445388255964568689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12410438521035349238849837 4653914445388255964568689)
      ·
        refine ⟨3490435834041191973426517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653914445388255964568689 3490435834041191973426517)
        ·
          refine ⟨639117889533909663103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 3490435834041191973426517 639117889533909663103)
          ·
            rfl

theorem cell23_907370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 14].length) (baseStart_907370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907370 prefixEnd_907370 := by exact prefixLift 907370
  have htrace : WordTrace (prefixWord ++ tailWord_907370) baseStart_907370 baseEnd_907370 := by
    simpa [prefixWord, tailWord_907370, baseEnd_907370] using wordTrace_append hprefix tailTrace_907370
  have hstable : (prefixWord ++ tailWord_907370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907370).length < 2 ^ (prefixWord ++ tailWord_907370).sum := by decide
  have hdescent : baseEnd_907370 < baseStart_907370 := by decide
  rcases family_descends (prefixWord ++ tailWord_907370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907415 : List Nat := [1, 1, 3, 3, 4, 1, 2, 3, 1, 2, 2]
def baseStart_907415 : Nat := 118140960795 + 907415 * 2 ^ 59
def prefixEnd_907415 : Nat := 4983230072969 + 3 ^ 40 * 907415 * 2
def baseEnd_907415 : Nat := 465940048099672468339381

theorem tailTrace_907415 : CollatzResearch.WordTrace tailWord_907415 prefixEnd_907415 465940048099672468339381 := by
  unfold tailWord_907415
  simp only [CollatzResearch.WordTrace]
  refine ⟨33096144007597903988987699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22064096005065269325991799 33096144007597903988987699)
  ·
    refine ⟨49644216011396855983481549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33096144007597903988987699 49644216011396855983481549)
    ·
      refine ⟨18616581004273820993805581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49644216011396855983481549 18616581004273820993805581)
      ·
        refine ⟨6981217876602682872677093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18616581004273820993805581 6981217876602682872677093)
        ·
          refine ⟨1308978351863003038626955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6981217876602682872677093 1308978351863003038626955)
          ·
            refine ⟨1963467527794504557940433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308978351863003038626955 1963467527794504557940433)
            ·
              refine ⟨1472600645845878418455325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963467527794504557940433 1472600645845878418455325)
              ·
                refine ⟨552225242192204406920747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472600645845878418455325 552225242192204406920747)
                ·
                  refine ⟨828337863288306610381121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552225242192204406920747 828337863288306610381121)
                  ·
                    refine ⟨621253397466229957785841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 828337863288306610381121 621253397466229957785841)
                    ·
                      refine ⟨465940048099672468339381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621253397466229957785841 465940048099672468339381)
                      ·
                        rfl

theorem cell23_907415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_907415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907415 prefixEnd_907415 := by exact prefixLift 907415
  have htrace : WordTrace (prefixWord ++ tailWord_907415) baseStart_907415 baseEnd_907415 := by
    simpa [prefixWord, tailWord_907415, baseEnd_907415] using wordTrace_append hprefix tailTrace_907415
  have hstable : (prefixWord ++ tailWord_907415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907415).length < 2 ^ (prefixWord ++ tailWord_907415).sum := by decide
  have hdescent : baseEnd_907415 < baseStart_907415 := by decide
  rcases family_descends (prefixWord ++ tailWord_907415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907447 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 2, 6]
def baseStart_907447 : Nat := 118140960795 + 907447 * 2 ^ 59
def prefixEnd_907447 : Nat := 4983230072969 + 3 ^ 40 * 907447 * 2
def baseEnd_907447 : Nat := 155318826493538781046411

theorem tailTrace_907447 : CollatzResearch.WordTrace tailWord_907447 prefixEnd_907447 155318826493538781046411 := by
  unfold tailWord_907447
  simp only [CollatzResearch.WordTrace]
  refine ⟨33097311143481973454152595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22064874095654648969435063 33097311143481973454152595)
  ·
    refine ⟨49645966715222960181228893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33097311143481973454152595 49645966715222960181228893)
    ·
      refine ⟨18617237518208610067960835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49645966715222960181228893 18617237518208610067960835)
      ·
        refine ⟨27925856277312915101941253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18617237518208610067960835 27925856277312915101941253)
        ·
          refine ⟨5236098051996171581613985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27925856277312915101941253 5236098051996171581613985)
          ·
            refine ⟨3927073538997128686210489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5236098051996171581613985 3927073538997128686210489)
            ·
              refine ⟨2945305154247846514657867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3927073538997128686210489 2945305154247846514657867)
              ·
                refine ⟨4417957731371769771986801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945305154247846514657867 4417957731371769771986801)
                ·
                  refine ⟨3313468298528827328990101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4417957731371769771986801 3313468298528827328990101)
                  ·
                    refine ⟨155318826493538781046411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3313468298528827328990101 155318826493538781046411)
                    ·
                      rfl

theorem cell23_907447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_907447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907447 prefixEnd_907447 := by exact prefixLift 907447
  have htrace : WordTrace (prefixWord ++ tailWord_907447) baseStart_907447 baseEnd_907447 := by
    simpa [prefixWord, tailWord_907447, baseEnd_907447] using wordTrace_append hprefix tailTrace_907447
  have hstable : (prefixWord ++ tailWord_907447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907447).length < 2 ^ (prefixWord ++ tailWord_907447).sum := by decide
  have hdescent : baseEnd_907447 < baseStart_907447 := by decide
  rcases family_descends (prefixWord ++ tailWord_907447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907474 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_907474 : Nat := 118140960795 + 907474 * 2 ^ 59
def prefixEnd_907474 : Nat := 4983230072969 + 3 ^ 40 * 907474 * 2
def baseEnd_907474 : Nat := 465970343458287737501609

theorem tailTrace_907474 : CollatzResearch.WordTrace tailWord_907474 prefixEnd_907474 465970343458287737501609 := by
  unfold tailWord_907474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8274573978596039266346369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22065530609589438043590317 8274573978596039266346369)
  ·
    refine ⟨6205930483947029449759777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8274573978596039266346369 6205930483947029449759777)
    ·
      refine ⟨4654447862960272087319833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6205930483947029449759777 4654447862960272087319833)
      ·
        refine ⟨3490835897220204065489875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4654447862960272087319833 3490835897220204065489875)
        ·
          refine ⟨5236253845830306098234813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490835897220204065489875 5236253845830306098234813)
          ·
            refine ⟨1963595192186364786838055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5236253845830306098234813 1963595192186364786838055)
            ·
              refine ⟨2945392788279547180257083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963595192186364786838055 2945392788279547180257083)
              ·
                refine ⟨4418089182419320770385625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945392788279547180257083 4418089182419320770385625)
                ·
                  refine ⟨3313566886814490577789219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418089182419320770385625 3313566886814490577789219)
                  ·
                    refine ⟨4970350330221735866683829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3313566886814490577789219 4970350330221735866683829)
                    ·
                      refine ⟨465970343458287737501609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4970350330221735866683829 465970343458287737501609)
                      ·
                        rfl

theorem cell23_907474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_907474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907474 prefixEnd_907474 := by exact prefixLift 907474
  have htrace : WordTrace (prefixWord ++ tailWord_907474) baseStart_907474 baseEnd_907474 := by
    simpa [prefixWord, tailWord_907474, baseEnd_907474] using wordTrace_append hprefix tailTrace_907474
  have hstable : (prefixWord ++ tailWord_907474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907474).length < 2 ^ (prefixWord ++ tailWord_907474).sum := by decide
  have hdescent : baseEnd_907474 < baseStart_907474 := by decide
  rcases family_descends (prefixWord ++ tailWord_907474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907507 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 4, 5]
def baseStart_907507 : Nat := 118140960795 + 907507 * 2 ^ 59
def prefixEnd_907507 : Nat := 4983230072969 + 3 ^ 40 * 907507 * 2
def baseEnd_907507 : Nat := 155329096106628702796319

theorem tailTrace_907507 : CollatzResearch.WordTrace tailWord_907507 prefixEnd_907507 155329096106628702796319 := by
  unfold tailWord_907507
  simp only [CollatzResearch.WordTrace]
  refine ⟨33099499523264603701336775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22066333015509735800891183 33099499523264603701336775)
  ·
    refine ⟨49649249284896905552005163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33099499523264603701336775 49649249284896905552005163)
    ·
      refine ⟨74473873927345358328007745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49649249284896905552005163 74473873927345358328007745)
      ·
        refine ⟨55855405445509018746005809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74473873927345358328007745 55855405445509018746005809)
        ·
          refine ⟨41891554084131764059504357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55855405445509018746005809 41891554084131764059504357)
          ·
            refine ⟨7854666390774705761157067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41891554084131764059504357 7854666390774705761157067)
            ·
              refine ⟨11781999586162058641735601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854666390774705761157067 11781999586162058641735601)
              ·
                refine ⟨8836499689621543981301701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11781999586162058641735601 8836499689621543981301701)
                ·
                  refine ⟨1656843691804039496494069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8836499689621543981301701 1656843691804039496494069)
                  ·
                    refine ⟨155329096106628702796319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1656843691804039496494069 155329096106628702796319)
                    ·
                      rfl

theorem cell23_907507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 5].length) (baseStart_907507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907507 prefixEnd_907507 := by exact prefixLift 907507
  have htrace : WordTrace (prefixWord ++ tailWord_907507) baseStart_907507 baseEnd_907507 := by
    simpa [prefixWord, tailWord_907507, baseEnd_907507] using wordTrace_append hprefix tailTrace_907507
  have hstable : (prefixWord ++ tailWord_907507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907507).length < 2 ^ (prefixWord ++ tailWord_907507).sum := by decide
  have hdescent : baseEnd_907507 < baseStart_907507 := by decide
  rcases family_descends (prefixWord ++ tailWord_907507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907544 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_907544 : Nat := 118140960795 + 907544 * 2 ^ 59
def prefixEnd_907544 : Nat := 4983230072969 + 3 ^ 40 * 907544 * 2
def baseEnd_907544 : Nat := 466006287104102463626287

theorem tailTrace_907544 : CollatzResearch.WordTrace tailWord_907544 prefixEnd_907544 466006287104102463626287 := by
  unfold tailWord_907544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16550424512065279510216843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22067232682753706013622457 16550424512065279510216843)
  ·
    refine ⟨24825636768097919265325265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16550424512065279510216843 24825636768097919265325265)
    ·
      refine ⟨18619227576073439448993949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24825636768097919265325265 18619227576073439448993949)
      ·
        refine ⟨6982210341027539793372731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18619227576073439448993949 6982210341027539793372731)
        ·
          refine ⟨10473315511541309690059097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982210341027539793372731 10473315511541309690059097)
          ·
            refine ⟨7854986633655982267544323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10473315511541309690059097 7854986633655982267544323)
            ·
              refine ⟨11782479950483973401316485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854986633655982267544323 11782479950483973401316485)
              ·
                refine ⟨2209214990715745012746841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11782479950483973401316485 2209214990715745012746841)
                ·
                  refine ⟨1656911243036808759560131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209214990715745012746841 1656911243036808759560131)
                  ·
                    refine ⟨2485366864555213139340197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1656911243036808759560131 2485366864555213139340197)
                    ·
                      refine ⟨466006287104102463626287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2485366864555213139340197 466006287104102463626287)
                      ·
                        rfl

theorem cell23_907544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_907544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907544 prefixEnd_907544 := by exact prefixLift 907544
  have htrace : WordTrace (prefixWord ++ tailWord_907544) baseStart_907544 baseEnd_907544 := by
    simpa [prefixWord, tailWord_907544, baseEnd_907544] using wordTrace_append hprefix tailTrace_907544
  have hstable : (prefixWord ++ tailWord_907544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907544).length < 2 ^ (prefixWord ++ tailWord_907544).sum := by decide
  have hdescent : baseEnd_907544 < baseStart_907544 := by decide
  rcases family_descends (prefixWord ++ tailWord_907544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907564 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_907564 : Nat := 118140960795 + 907564 * 2 ^ 59
def prefixEnd_907564 : Nat := 4983230072969 + 3 ^ 40 * 907564 * 2
def baseEnd_907564 : Nat := 466016556717192385376195

theorem tailTrace_907564 : CollatzResearch.WordTrace tailWord_907564 prefixEnd_907564 466016556717192385376195 := by
  unfold tailWord_907564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16550789242029051218080873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22067718989372068290774497 16550789242029051218080873)
  ·
    refine ⟨12413091931521788413560655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16550789242029051218080873 12413091931521788413560655)
    ·
      refine ⟨18619637897282682620340983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12413091931521788413560655 18619637897282682620340983)
      ·
        refine ⟨27929456845924023930511475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18619637897282682620340983 27929456845924023930511475)
        ·
          refine ⟨41894185268886035895767213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27929456845924023930511475 41894185268886035895767213)
          ·
            refine ⟨15710319475832263460912705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41894185268886035895767213 15710319475832263460912705)
            ·
              refine ⟨11782739606874197595684529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15710319475832263460912705 11782739606874197595684529)
              ·
                refine ⟨8837054705155648196763397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11782739606874197595684529 8837054705155648196763397)
                ·
                  refine ⟨1656947757216684036893137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8837054705155648196763397 1656947757216684036893137)
                  ·
                    refine ⟨1242710817912513027669853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1656947757216684036893137 1242710817912513027669853)
                    ·
                      refine ⟨466016556717192385376195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1242710817912513027669853 466016556717192385376195)
                      ·
                        rfl

theorem cell23_907564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_907564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907564 prefixEnd_907564 := by exact prefixLift 907564
  have htrace : WordTrace (prefixWord ++ tailWord_907564) baseStart_907564 baseEnd_907564 := by
    simpa [prefixWord, tailWord_907564, baseEnd_907564] using wordTrace_append hprefix tailTrace_907564
  have hstable : (prefixWord ++ tailWord_907564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907564).length < 2 ^ (prefixWord ++ tailWord_907564).sum := by decide
  have hdescent : baseEnd_907564 < baseStart_907564 := by decide
  rcases family_descends (prefixWord ++ tailWord_907564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907601 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 6]
def baseStart_907601 : Nat := 118140960795 + 907601 * 2 ^ 59
def prefixEnd_907601 : Nat := 4983230072969 + 3 ^ 40 * 907601 * 2
def baseEnd_907601 : Nat := 51781728389045415623725

theorem tailTrace_907601 : CollatzResearch.WordTrace tailWord_907601 prefixEnd_907601 51781728389045415623725 := by
  unfold tailWord_907601
  simp only [CollatzResearch.WordTrace]
  refine ⟨33102927984924057755258657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22068618656616038503505771 33102927984924057755258657)
  ·
    refine ⟨24827195988693043316443993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33102927984924057755258657 24827195988693043316443993)
    ·
      refine ⟨18620396991519782487332995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24827195988693043316443993 18620396991519782487332995)
      ·
        refine ⟨27930595487279673730999493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18620396991519782487332995 27930595487279673730999493)
        ·
          refine ⟨5236986653864938824562405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27930595487279673730999493 5236986653864938824562405)
          ·
            refine ⟨981934997599676029605451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5236986653864938824562405 981934997599676029605451)
            ·
              refine ⟨1472902496399514044408177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981934997599676029605451 1472902496399514044408177)
              ·
                refine ⟨1104676872299635533306133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472902496399514044408177 1104676872299635533306133)
                ·
                  refine ⟨51781728389045415623725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1104676872299635533306133 51781728389045415623725)
                  ·
                    rfl

theorem cell23_907601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 6].length) (baseStart_907601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907601 prefixEnd_907601 := by exact prefixLift 907601
  have htrace : WordTrace (prefixWord ++ tailWord_907601) baseStart_907601 baseEnd_907601 := by
    simpa [prefixWord, tailWord_907601, baseEnd_907601] using wordTrace_append hprefix tailTrace_907601
  have hstable : (prefixWord ++ tailWord_907601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907601).length < 2 ^ (prefixWord ++ tailWord_907601).sum := by decide
  have hdescent : baseEnd_907601 < baseStart_907601 := by decide
  rcases family_descends (prefixWord ++ tailWord_907601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907604 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_907604 : Nat := 118140960795 + 907604 * 2 ^ 59
def prefixEnd_907604 : Nat := 4983230072969 + 3 ^ 40 * 907604 * 2
def baseEnd_907604 : Nat := 466037095943372228876011

theorem tailTrace_907604 : CollatzResearch.WordTrace tailWord_907604 prefixEnd_907604 466037095943372228876011 := by
  unfold tailWord_907604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16551518701956594633808933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22068691602608792845078577 16551518701956594633808933)
  ·
    refine ⟨3103409756616861493839175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16551518701956594633808933 3103409756616861493839175)
    ·
      refine ⟨4655114634925292240758763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103409756616861493839175 4655114634925292240758763)
      ·
        refine ⟨6982671952387938361138145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655114634925292240758763 6982671952387938361138145)
        ·
          refine ⟨5237003964290953770853609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6982671952387938361138145 5237003964290953770853609)
          ·
            refine ⟨3927752973218215328140207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5237003964290953770853609 3927752973218215328140207)
            ·
              refine ⟨5891629459827322992210311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927752973218215328140207 5891629459827322992210311)
              ·
                refine ⟨8837444189740984488315467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891629459827322992210311 8837444189740984488315467)
                ·
                  refine ⟨13256166284611476732473201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8837444189740984488315467 13256166284611476732473201)
                  ·
                    refine ⟨9942124713458607549354901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13256166284611476732473201 9942124713458607549354901)
                    ·
                      refine ⟨466037095943372228876011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9942124713458607549354901 466037095943372228876011)
                      ·
                        rfl

theorem cell23_907604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_907604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907604 prefixEnd_907604 := by exact prefixLift 907604
  have htrace : WordTrace (prefixWord ++ tailWord_907604) baseStart_907604 baseEnd_907604 := by
    simpa [prefixWord, tailWord_907604, baseEnd_907604] using wordTrace_append hprefix tailTrace_907604
  have hstable : (prefixWord ++ tailWord_907604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907604).length < 2 ^ (prefixWord ++ tailWord_907604).sum := by decide
  have hdescent : baseEnd_907604 < baseStart_907604 := by decide
  rcases family_descends (prefixWord ++ tailWord_907604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907618 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 6]
def baseStart_907618 : Nat := 118140960795 + 907618 * 2 ^ 59
def prefixEnd_907618 : Nat := 4983230072969 + 3 ^ 40 * 907618 * 2
def baseEnd_907618 : Nat := 51782698296948352677883

theorem tailTrace_907618 : CollatzResearch.WordTrace tailWord_907618 prefixEnd_907618 51782698296948352677883 := by
  unfold tailWord_907618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275887006465617414656877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22069032017241646439085005 8275887006465617414656877)
  ·
    refine ⟨3103457627424606530496329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8275887006465617414656877 3103457627424606530496329)
    ·
      refine ⟨2327593220568454897872247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3103457627424606530496329 2327593220568454897872247)
      ·
        refine ⟨3491389830852682346808371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327593220568454897872247 3491389830852682346808371)
        ·
          refine ⟨5237084746279023520212557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491389830852682346808371 5237084746279023520212557)
          ·
            refine ⟨1963906779854633820079709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5237084746279023520212557 1963906779854633820079709)
            ·
              refine ⟨736465042445487682529891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1963906779854633820079709 736465042445487682529891)
              ·
                refine ⟨1104697563668231523794837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736465042445487682529891 1104697563668231523794837)
                ·
                  refine ⟨51782698296948352677883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1104697563668231523794837 51782698296948352677883)
                  ·
                    rfl

theorem cell23_907618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_907618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907618 prefixEnd_907618 := by exact prefixLift 907618
  have htrace : WordTrace (prefixWord ++ tailWord_907618) baseStart_907618 baseEnd_907618 := by
    simpa [prefixWord, tailWord_907618, baseEnd_907618] using wordTrace_append hprefix tailTrace_907618
  have hstable : (prefixWord ++ tailWord_907618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907618).length < 2 ^ (prefixWord ++ tailWord_907618).sum := by decide
  have hdescent : baseEnd_907618 < baseStart_907618 := by decide
  rcases family_descends (prefixWord ++ tailWord_907618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907621 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 1, 5, 2]
def baseStart_907621 : Nat := 118140960795 + 907621 * 2 ^ 59
def prefixEnd_907621 : Nat := 4983230072969 + 3 ^ 40 * 907621 * 2
def baseEnd_907621 : Nat := 466045825114498662363433

theorem tailTrace_907621 : CollatzResearch.WordTrace tailWord_907621 prefixEnd_907621 466045825114498662363433 := by
  unfold tailWord_907621
  simp only [CollatzResearch.WordTrace]
  refine ⟨33103657444851601170986717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22069104963234400780657811 33103657444851601170986717)
  ·
    refine ⟨12413871541819350439120019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33103657444851601170986717 12413871541819350439120019)
    ·
      refine ⟨18620807312729025658680029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12413871541819350439120019 18620807312729025658680029)
      ·
        refine ⟨6982802742273384622005011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18620807312729025658680029 6982802742273384622005011)
        ·
          refine ⟨10474204113410076933007517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982802742273384622005011 10474204113410076933007517)
          ·
            refine ⟨3927826542528778849877819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10474204113410076933007517 3927826542528778849877819)
            ·
              refine ⟨5891739813793168274816729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927826542528778849877819 5891739813793168274816729)
              ·
                refine ⟨4418804860344876206112547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5891739813793168274816729 4418804860344876206112547)
                ·
                  refine ⟨6628207290517314309168821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418804860344876206112547 6628207290517314309168821)
                  ·
                    refine ⟨621394433485998216484577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6628207290517314309168821 621394433485998216484577)
                    ·
                      refine ⟨466045825114498662363433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621394433485998216484577 466045825114498662363433)
                      ·
                        rfl

theorem cell23_907621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_907621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907621 prefixEnd_907621 := by exact prefixLift 907621
  have htrace : WordTrace (prefixWord ++ tailWord_907621) baseStart_907621 baseEnd_907621 := by
    simpa [prefixWord, tailWord_907621, baseEnd_907621] using wordTrace_append hprefix tailTrace_907621
  have hstable : (prefixWord ++ tailWord_907621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907621).length < 2 ^ (prefixWord ++ tailWord_907621).sum := by decide
  have hdescent : baseEnd_907621 < baseStart_907621 := by decide
  rcases family_descends (prefixWord ++ tailWord_907621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907645 : List Nat := [1, 4, 1, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_907645 : Nat := 118140960795 + 907645 * 2 ^ 59
def prefixEnd_907645 : Nat := 4983230072969 + 3 ^ 40 * 907645 * 2
def baseEnd_907645 : Nat := 466058148650206568463323

theorem tailTrace_907645 : CollatzResearch.WordTrace tailWord_907645 prefixEnd_907645 466058148650206568463323 := by
  unfold tailWord_907645
  simp only [CollatzResearch.WordTrace]
  refine ⟨33104532796764653269860389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22069688531176435513240259 33104532796764653269860389)
  ·
    refine ⟨6207099899393372488098823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33104532796764653269860389 6207099899393372488098823)
    ·
      refine ⟨9310649849090058732148235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207099899393372488098823 9310649849090058732148235)
      ·
        refine ⟨13965974773635088098222353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310649849090058732148235 13965974773635088098222353)
        ·
          refine ⟨10474481080226316073666765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13965974773635088098222353 10474481080226316073666765)
          ·
            refine ⟨3927930405084868527625037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10474481080226316073666765 3927930405084868527625037)
            ·
              refine ⟨1472973901906825697859389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3927930405084868527625037 1472973901906825697859389)
              ·
                refine ⟨552365213215059636697271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472973901906825697859389 552365213215059636697271)
                ·
                  refine ⟨828547819822589455045907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552365213215059636697271 828547819822589455045907)
                  ·
                    refine ⟨1242821729733884182568861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 828547819822589455045907 1242821729733884182568861)
                    ·
                      refine ⟨466058148650206568463323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1242821729733884182568861 466058148650206568463323)
                      ·
                        rfl

theorem cell23_907645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_907645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907645 prefixEnd_907645 := by exact prefixLift 907645
  have htrace : WordTrace (prefixWord ++ tailWord_907645) baseStart_907645 baseEnd_907645 := by
    simpa [prefixWord, tailWord_907645, baseEnd_907645] using wordTrace_append hprefix tailTrace_907645
  have hstable : (prefixWord ++ tailWord_907645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907645).length < 2 ^ (prefixWord ++ tailWord_907645).sum := by decide
  have hdescent : baseEnd_907645 < baseStart_907645 := by decide
  rcases family_descends (prefixWord ++ tailWord_907645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907674 : List Nat := [3, 1, 1, 4, 1, 2, 1, 10]
def baseStart_907674 : Nat := 118140960795 + 907674 * 2 ^ 59
def prefixEnd_907674 : Nat := 4983230072969 + 3 ^ 40 * 907674 * 2
def baseEnd_907674 : Nat := 17261964429229146481507

theorem tailTrace_907674 : CollatzResearch.WordTrace tailWord_907674 prefixEnd_907674 17261964429229146481507 := by
  unfold tailWord_907674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276397628414897805666519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22070393675773060815110717 8276397628414897805666519)
  ·
    refine ⟨12414596442622346708499779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8276397628414897805666519 12414596442622346708499779)
    ·
      refine ⟨18621894663933520062749669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12414596442622346708499779 18621894663933520062749669)
      ·
        refine ⟨3491605249487535011765563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18621894663933520062749669 3491605249487535011765563)
        ·
          refine ⟨5237407874231302517648345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491605249487535011765563 5237407874231302517648345)
          ·
            refine ⟨3928055905673476888236259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5237407874231302517648345 3928055905673476888236259)
            ·
              refine ⟨5892083858510215332354389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3928055905673476888236259 5892083858510215332354389)
              ·
                refine ⟨17261964429229146481507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5892083858510215332354389 17261964429229146481507)
                ·
                  rfl

theorem cell23_907674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_907674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907674 prefixEnd_907674 := by exact prefixLift 907674
  have htrace : WordTrace (prefixWord ++ tailWord_907674) baseStart_907674 baseEnd_907674 := by
    simpa [prefixWord, tailWord_907674, baseEnd_907674] using wordTrace_append hprefix tailTrace_907674
  have hstable : (prefixWord ++ tailWord_907674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907674).length < 2 ^ (prefixWord ++ tailWord_907674).sum := by decide
  have hdescent : baseEnd_907674 < baseStart_907674 := by decide
  rcases family_descends (prefixWord ++ tailWord_907674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907705 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 1, 2, 3]
def baseStart_907705 : Nat := 118140960795 + 907705 * 2 ^ 59
def prefixEnd_907705 : Nat := 4983230072969 + 3 ^ 40 * 907705 * 2
def baseEnd_907705 : Nat := 466088957489476333713047

theorem tailTrace_907705 : CollatzResearch.WordTrace tailWord_907705 prefixEnd_907705 466088957489476333713047 := by
  unfold tailWord_907705
  simp only [CollatzResearch.WordTrace]
  refine ⟨33106721176547283517044569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22071147451031522344696379 33106721176547283517044569)
  ·
    refine ⟨24830040882410462637783427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33106721176547283517044569 24830040882410462637783427)
    ·
      refine ⟨37245061323615693956675141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24830040882410462637783427 37245061323615693956675141)
      ·
        refine ⟨6983448998177942616876589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37245061323615693956675141 6983448998177942616876589)
        ·
          refine ⟨2618793374316728481328721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6983448998177942616876589 2618793374316728481328721)
          ·
            refine ⟨1964095030737546360996541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2618793374316728481328721 1964095030737546360996541)
            ·
              refine ⟨736535636526579885373703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1964095030737546360996541 736535636526579885373703)
              ·
                refine ⟨1104803454789869828060555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736535636526579885373703 1104803454789869828060555)
                ·
                  refine ⟨1657205182184804742090833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104803454789869828060555 1657205182184804742090833)
                  ·
                    refine ⟨1242903886638603556568125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1657205182184804742090833 1242903886638603556568125)
                    ·
                      refine ⟨466088957489476333713047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1242903886638603556568125 466088957489476333713047)
                      ·
                        rfl

theorem cell23_907705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_907705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907705 prefixEnd_907705 := by exact prefixLift 907705
  have htrace : WordTrace (prefixWord ++ tailWord_907705) baseStart_907705 baseEnd_907705 := by
    simpa [prefixWord, tailWord_907705, baseEnd_907705] using wordTrace_append hprefix tailTrace_907705
  have hstable : (prefixWord ++ tailWord_907705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907705).length < 2 ^ (prefixWord ++ tailWord_907705).sum := by decide
  have hdescent : baseEnd_907705 < baseStart_907705 := by decide
  rcases family_descends (prefixWord ++ tailWord_907705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907713 : List Nat := [1, 2, 7, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_907713 : Nat := 118140960795 + 907713 * 2 ^ 59
def prefixEnd_907713 : Nat := 4983230072969 + 3 ^ 40 * 907713 * 2
def baseEnd_907713 : Nat := 466093065334712302413011

theorem tailTrace_907713 : CollatzResearch.WordTrace tailWord_907713 prefixEnd_907713 466093065334712302413011 := by
  unfold tailWord_907713
  simp only [CollatzResearch.WordTrace]
  refine ⟨33107012960518300883335793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22071341973678867255557195 33107012960518300883335793)
  ·
    refine ⟨24830259720388725662501845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33107012960518300883335793 24830259720388725662501845)
    ·
      refine ⟨581959212196610757714887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24830259720388725662501845 581959212196610757714887)
      ·
        refine ⟨872938818294916136572331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581959212196610757714887 872938818294916136572331)
        ·
          refine ⟨1309408227442374204858497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872938818294916136572331 1309408227442374204858497)
          ·
            refine ⟨982056170581780653643873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309408227442374204858497 982056170581780653643873)
            ·
              refine ⟨736542127936335490232905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982056170581780653643873 736542127936335490232905)
              ·
                refine ⟨552406595952251617674679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736542127936335490232905 552406595952251617674679)
                ·
                  refine ⟨828609893928377426512019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552406595952251617674679 828609893928377426512019)
                  ·
                    refine ⟨1242914840892566139768029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 828609893928377426512019 1242914840892566139768029)
                    ·
                      refine ⟨466093065334712302413011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1242914840892566139768029 466093065334712302413011)
                      ·
                        rfl

theorem cell23_907713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_907713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907713 prefixEnd_907713 := by exact prefixLift 907713
  have htrace : WordTrace (prefixWord ++ tailWord_907713) baseStart_907713 baseEnd_907713 := by
    simpa [prefixWord, tailWord_907713, baseEnd_907713] using wordTrace_append hprefix tailTrace_907713
  have hstable : (prefixWord ++ tailWord_907713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907713).length < 2 ^ (prefixWord ++ tailWord_907713).sum := by decide
  have hdescent : baseEnd_907713 < baseStart_907713 := by decide
  rcases family_descends (prefixWord ++ tailWord_907713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907719 : List Nat := [1, 1, 4, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_907719 : Nat := 118140960795 + 907719 * 2 ^ 59
def prefixEnd_907719 : Nat := 4983230072969 + 3 ^ 40 * 907719 * 2
def baseEnd_907719 : Nat := 466096146218639278937983

theorem tailTrace_907719 : CollatzResearch.WordTrace tailWord_907719 prefixEnd_907719 466096146218639278937983 := by
  unfold tailWord_907719
  simp only [CollatzResearch.WordTrace]
  refine ⟨33107231798496563908054211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22071487865664375938702807 33107231798496563908054211)
  ·
    refine ⟨49660847697744845862081317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33107231798496563908054211 49660847697744845862081317)
    ·
      refine ⟨9311408943327158599140247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49660847697744845862081317 9311408943327158599140247)
      ·
        refine ⟨13967113414990737898710371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9311408943327158599140247 13967113414990737898710371)
        ·
          refine ⟨20950670122486106848065557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13967113414990737898710371 20950670122486106848065557)
          ·
            refine ⟨982062661991536258503073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20950670122486106848065557 982062661991536258503073)
            ·
              refine ⟨736546996493652193877305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982062661991536258503073 736546996493652193877305)
              ·
                refine ⟨552410247370239145407979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736546996493652193877305 552410247370239145407979)
                ·
                  refine ⟨828615371055358718111969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552410247370239145407979 828615371055358718111969)
                  ·
                    refine ⟨621461528291519038583977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 828615371055358718111969 621461528291519038583977)
                    ·
                      refine ⟨466096146218639278937983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621461528291519038583977 466096146218639278937983)
                      ·
                        rfl

theorem cell23_907719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_907719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907719 prefixEnd_907719 := by exact prefixLift 907719
  have htrace : WordTrace (prefixWord ++ tailWord_907719) baseStart_907719 baseEnd_907719 := by
    simpa [prefixWord, tailWord_907719, baseEnd_907719] using wordTrace_append hprefix tailTrace_907719
  have hstable : (prefixWord ++ tailWord_907719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907719).length < 2 ^ (prefixWord ++ tailWord_907719).sum := by decide
  have hdescent : baseEnd_907719 < baseStart_907719 := by decide
  rcases family_descends (prefixWord ++ tailWord_907719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907741 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_907741 : Nat := 118140960795 + 907741 * 2 ^ 59
def prefixEnd_907741 : Nat := 4983230072969 + 3 ^ 40 * 907741 * 2
def baseEnd_907741 : Nat := 466107442793038192862881

theorem tailTrace_907741 : CollatzResearch.WordTrace tailWord_907741 prefixEnd_907741 466107442793038192862881 := by
  unfold tailWord_907741
  simp only [CollatzResearch.WordTrace]
  refine ⟨33108034204416861665355077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22072022802944574443570051 33108034204416861665355077)
  ·
    refine ⟨6207756413328161562254077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33108034204416861665355077 6207756413328161562254077)
    ·
      refine ⟨2327908654998060585845279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6207756413328161562254077 2327908654998060585845279)
      ·
        refine ⟨3491862982497090878767919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327908654998060585845279 3491862982497090878767919)
        ·
          refine ⟨5237794473745636318151879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491862982497090878767919 5237794473745636318151879)
          ·
            refine ⟨7856691710618454477227819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237794473745636318151879 7856691710618454477227819)
            ·
              refine ⟨11785037565927681715841729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856691710618454477227819 11785037565927681715841729)
              ·
                refine ⟨8838778174445761286881297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11785037565927681715841729 8838778174445761286881297)
                ·
                  refine ⟨6629083630834320965160973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838778174445761286881297 6629083630834320965160973)
                  ·
                    refine ⟨2485906361562870361935365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6629083630834320965160973 2485906361562870361935365)
                    ·
                      refine ⟨466107442793038192862881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2485906361562870361935365 466107442793038192862881)
                      ·
                        rfl

theorem cell23_907741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_907741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907741 prefixEnd_907741 := by exact prefixLift 907741
  have htrace : WordTrace (prefixWord ++ tailWord_907741) baseStart_907741 baseEnd_907741 := by
    simpa [prefixWord, tailWord_907741, baseEnd_907741] using wordTrace_append hprefix tailTrace_907741
  have hstable : (prefixWord ++ tailWord_907741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907741).length < 2 ^ (prefixWord ++ tailWord_907741).sum := by decide
  have hdescent : baseEnd_907741 < baseStart_907741 := by decide
  rcases family_descends (prefixWord ++ tailWord_907741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907762 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_907762 : Nat := 118140960795 + 907762 * 2 ^ 59
def prefixEnd_907762 : Nat := 4983230072969 + 3 ^ 40 * 907762 * 2
def baseEnd_907762 : Nat := 466118225886782610700285

theorem tailTrace_907762 : CollatzResearch.WordTrace tailWord_907762 prefixEnd_907762 466118225886782610700285 := by
  unfold tailWord_907762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8277200034335195562967385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22072533424893854834579693 8277200034335195562967385)
  ·
    refine ⟨6207900025751396672225539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8277200034335195562967385 6207900025751396672225539)
    ·
      refine ⟨9311850038627095008338309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207900025751396672225539 9311850038627095008338309)
      ·
        refine ⟨1745971882242580314063433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9311850038627095008338309 1745971882242580314063433)
        ·
          refine ⟨1309478911681935235547575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1745971882242580314063433 1309478911681935235547575)
          ·
            refine ⟨1964218367522902853321363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309478911681935235547575 1964218367522902853321363)
            ·
              refine ⟨2946327551284354279982045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964218367522902853321363 2946327551284354279982045)
              ·
                refine ⟨1104872831731632854993267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946327551284354279982045 1104872831731632854993267)
                ·
                  refine ⟨1657309247597449282489901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104872831731632854993267 1657309247597449282489901)
                  ·
                    refine ⟨621490967849043480933713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657309247597449282489901 621490967849043480933713)
                    ·
                      refine ⟨466118225886782610700285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621490967849043480933713 466118225886782610700285)
                      ·
                        rfl

theorem cell23_907762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_907762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907762 prefixEnd_907762 := by exact prefixLift 907762
  have htrace : WordTrace (prefixWord ++ tailWord_907762) baseStart_907762 baseEnd_907762 := by
    simpa [prefixWord, tailWord_907762, baseEnd_907762] using wordTrace_append hprefix tailTrace_907762
  have hstable : (prefixWord ++ tailWord_907762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907762).length < 2 ^ (prefixWord ++ tailWord_907762).sum := by decide
  have hdescent : baseEnd_907762 < baseStart_907762 := by decide
  rcases family_descends (prefixWord ++ tailWord_907762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907811 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 1, 7]
def baseStart_907811 : Nat := 118140960795 + 907811 * 2 ^ 59
def prefixEnd_907811 : Nat := 4983230072969 + 3 ^ 40 * 907811 * 2
def baseEnd_907811 : Nat := 155381128812950972995853

theorem tailTrace_907811 : CollatzResearch.WordTrace tailWord_907811 prefixEnd_907811 155381128812950972995853 := by
  unfold tailWord_907811
  simp only [CollatzResearch.WordTrace]
  refine ⟨33110587314163263620403287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22073724876108842413602191 33110587314163263620403287)
  ·
    refine ⟨49665880971244895430604931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33110587314163263620403287 49665880971244895430604931)
    ·
      refine ⟨74498821456867343145907397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49665880971244895430604931 74498821456867343145907397)
      ·
        refine ⟨13968529023162626839857637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74498821456867343145907397 13968529023162626839857637)
        ·
          refine ⟨2619099191842992532473307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13968529023162626839857637 2619099191842992532473307)
          ·
            refine ⟨3928648787764488798709961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619099191842992532473307 3928648787764488798709961)
            ·
              refine ⟨2946486590823366599032471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928648787764488798709961 2946486590823366599032471)
              ·
                refine ⟨4419729886235049898548707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946486590823366599032471 4419729886235049898548707)
                ·
                  refine ⟨6629594829352574847823061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419729886235049898548707 6629594829352574847823061)
                  ·
                    refine ⟨155381128812950972995853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6629594829352574847823061 155381128812950972995853)
                    ·
                      rfl

theorem cell23_907811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 7].length) (baseStart_907811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907811 prefixEnd_907811 := by exact prefixLift 907811
  have htrace : WordTrace (prefixWord ++ tailWord_907811) baseStart_907811 baseEnd_907811 := by
    simpa [prefixWord, tailWord_907811, baseEnd_907811] using wordTrace_append hprefix tailTrace_907811
  have hstable : (prefixWord ++ tailWord_907811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907811).length < 2 ^ (prefixWord ++ tailWord_907811).sum := by decide
  have hdescent : baseEnd_907811 < baseStart_907811 := by decide
  rcases family_descends (prefixWord ++ tailWord_907811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907848 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_907848 : Nat := 118140960795 + 907848 * 2 ^ 59
def prefixEnd_907848 : Nat := 4983230072969 + 3 ^ 40 * 907848 * 2
def baseEnd_907848 : Nat := 466162385223069274224889

theorem tailTrace_907848 : CollatzResearch.WordTrace tailWord_907848 prefixEnd_907848 466162385223069274224889 := by
  unfold tailWord_907848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16555968407514609469750099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22074624543352812626333465 16555968407514609469750099)
  ·
    refine ⟨24833952611271914204625149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16555968407514609469750099 24833952611271914204625149)
    ·
      refine ⟨9312732229226967826734431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24833952611271914204625149 9312732229226967826734431)
      ·
        refine ⟨13969098343840451740101647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9312732229226967826734431 13969098343840451740101647)
        ·
          refine ⟨20953647515760677610152471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13969098343840451740101647 20953647515760677610152471)
          ·
            refine ⟨31430471273641016415228707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20953647515760677610152471 31430471273641016415228707)
            ·
              refine ⟨47145706910461524622843061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31430471273641016415228707 47145706910461524622843061)
              ·
                refine ⟨4419910022855767933391537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47145706910461524622843061 4419910022855767933391537)
                ·
                  refine ⟨3314932517141825950043653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4419910022855767933391537 3314932517141825950043653)
                  ·
                    refine ⟨621549846964092365633185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3314932517141825950043653 621549846964092365633185)
                    ·
                      refine ⟨466162385223069274224889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621549846964092365633185 466162385223069274224889)
                      ·
                        rfl

theorem cell23_907848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_907848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907848 prefixEnd_907848 := by exact prefixLift 907848
  have htrace : WordTrace (prefixWord ++ tailWord_907848) baseStart_907848 baseEnd_907848 := by
    simpa [prefixWord, tailWord_907848, baseEnd_907848] using wordTrace_append hprefix tailTrace_907848
  have hstable : (prefixWord ++ tailWord_907848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907848).length < 2 ^ (prefixWord ++ tailWord_907848).sum := by decide
  have hdescent : baseEnd_907848 < baseStart_907848 := by decide
  rcases family_descends (prefixWord ++ tailWord_907848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907851 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 3]
def baseStart_907851 : Nat := 118140960795 + 907851 * 2 ^ 59
def prefixEnd_907851 : Nat := 4983230072969 + 3 ^ 40 * 907851 * 2
def baseEnd_907851 : Nat := 466163925665032762487375

theorem tailTrace_907851 : CollatzResearch.WordTrace tailWord_907851 prefixEnd_907851 466163925665032762487375 := by
  unfold tailWord_907851
  simp only [CollatzResearch.WordTrace]
  refine ⟨33112046234018350451859407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22074697489345566967906271 33112046234018350451859407)
  ·
    refine ⟨49668069351027525677789111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33112046234018350451859407 49668069351027525677789111)
    ·
      refine ⟨74502104026541288516683667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49668069351027525677789111 74502104026541288516683667)
      ·
        refine ⟨111753156039811932775025501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74502104026541288516683667 111753156039811932775025501)
        ·
          refine ⟨41907433514929474790634563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111753156039811932775025501 41907433514929474790634563)
          ·
            refine ⟨62861150272394212185951845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41907433514929474790634563 62861150272394212185951845)
            ·
              refine ⟨11786465676073914784865971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62861150272394212185951845 11786465676073914784865971)
              ·
                refine ⟨17679698514110872177298957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11786465676073914784865971 17679698514110872177298957)
                ·
                  refine ⟨6629886942791577066487109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17679698514110872177298957 6629886942791577066487109)
                  ·
                    refine ⟨1243103801773420699966333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6629886942791577066487109 1243103801773420699966333)
                    ·
                      refine ⟨466163925665032762487375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1243103801773420699966333 466163925665032762487375)
                      ·
                        rfl

theorem cell23_907851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 3].length) (baseStart_907851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907851 prefixEnd_907851 := by exact prefixLift 907851
  have htrace : WordTrace (prefixWord ++ tailWord_907851) baseStart_907851 baseEnd_907851 := by
    simpa [prefixWord, tailWord_907851, baseEnd_907851] using wordTrace_append hprefix tailTrace_907851
  have hstable : (prefixWord ++ tailWord_907851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907851).length < 2 ^ (prefixWord ++ tailWord_907851).sum := by decide
  have hdescent : baseEnd_907851 < baseStart_907851 := by decide
  rcases family_descends (prefixWord ++ tailWord_907851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907858 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_907858 : Nat := 118140960795 + 907858 * 2 ^ 59
def prefixEnd_907858 : Nat := 4983230072969 + 3 ^ 40 * 907858 * 2
def baseEnd_907858 : Nat := 155389173343204745033281

theorem tailTrace_907858 : CollatzResearch.WordTrace tailWord_907858 prefixEnd_907858 155389173343204745033281 := by
  unfold tailWord_907858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8278075386248247661841057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22074867696661993764909485 8278075386248247661841057)
  ·
    refine ⟨6208556539686185746380793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8278075386248247661841057 6208556539686185746380793)
    ·
      refine ⟨4656417404764639309785595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6208556539686185746380793 4656417404764639309785595)
      ·
        refine ⟨6984626107146958964678393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656417404764639309785595 6984626107146958964678393)
        ·
          refine ⟨5238469580360219223508795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6984626107146958964678393 5238469580360219223508795)
          ·
            refine ⟨7857704370540328835263193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238469580360219223508795 7857704370540328835263193)
            ·
              refine ⟨5893278277905246626447395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7857704370540328835263193 5893278277905246626447395)
              ·
                refine ⟨8839917416857869939671093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893278277905246626447395 8839917416857869939671093)
                ·
                  refine ⟨828742257830425306844165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8839917416857869939671093 828742257830425306844165)
                  ·
                    refine ⟨155389173343204745033281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 828742257830425306844165 155389173343204745033281)
                    ·
                      rfl

theorem cell23_907858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_907858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907858 prefixEnd_907858 := by exact prefixLift 907858
  have htrace : WordTrace (prefixWord ++ tailWord_907858) baseStart_907858 baseEnd_907858 := by
    simpa [prefixWord, tailWord_907858, baseEnd_907858] using wordTrace_append hprefix tailTrace_907858
  have hstable : (prefixWord ++ tailWord_907858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907858).length < 2 ^ (prefixWord ++ tailWord_907858).sum := by decide
  have hdescent : baseEnd_907858 < baseStart_907858 := by decide
  rcases family_descends (prefixWord ++ tailWord_907858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907861 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_907861 : Nat := 118140960795 + 907861 * 2 ^ 59
def prefixEnd_907861 : Nat := 4983230072969 + 3 ^ 40 * 907861 * 2
def baseEnd_907861 : Nat := 466169060471577723362329

theorem tailTrace_907861 : CollatzResearch.WordTrace tailWord_907861 prefixEnd_907861 466169060471577723362329 := by
  unfold tailWord_907861
  simp only [CollatzResearch.WordTrace]
  refine ⟨33112410963982122159723437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22074940642654748106482291 33112410963982122159723437)
  ·
    refine ⟨12417154111493295809896289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33112410963982122159723437 12417154111493295809896289)
    ·
      refine ⟨9312865583619971857422217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12417154111493295809896289 9312865583619971857422217)
      ·
        refine ⟨6984649187714978893066663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9312865583619971857422217 6984649187714978893066663)
        ·
          refine ⟨10476973781572468339599995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6984649187714978893066663 10476973781572468339599995)
          ·
            refine ⟨15715460672358702509399993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10476973781572468339599995 15715460672358702509399993)
            ·
              refine ⟨11786595504269026882049995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15715460672358702509399993 11786595504269026882049995)
              ·
                refine ⟨17679893256403540323074993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11786595504269026882049995 17679893256403540323074993)
                ·
                  refine ⟨13259919942302655242306245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17679893256403540323074993 13259919942302655242306245)
                  ·
                    refine ⟨2486234989181747857932421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13259919942302655242306245 2486234989181747857932421)
                    ·
                      refine ⟨466169060471577723362329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2486234989181747857932421 466169060471577723362329)
                      ·
                        rfl

theorem cell23_907861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_907861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907861 prefixEnd_907861 := by exact prefixLift 907861
  have htrace : WordTrace (prefixWord ++ tailWord_907861) baseStart_907861 baseEnd_907861 := by
    simpa [prefixWord, tailWord_907861, baseEnd_907861] using wordTrace_append hprefix tailTrace_907861
  have hstable : (prefixWord ++ tailWord_907861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907861).length < 2 ^ (prefixWord ++ tailWord_907861).sum := by decide
  have hdescent : baseEnd_907861 < baseStart_907861 := by decide
  rcases family_descends (prefixWord ++ tailWord_907861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907875 : List Nat := [1, 1, 1, 5, 1, 2, 2, 5, 1, 4]
def baseStart_907875 : Nat := 118140960795 + 907875 * 2 ^ 59
def prefixEnd_907875 : Nat := 4983230072969 + 3 ^ 40 * 907875 * 2
def baseEnd_907875 : Nat := 155392083066913556195755

theorem tailTrace_907875 : CollatzResearch.WordTrace tailWord_907875 prefixEnd_907875 155392083066913556195755 := by
  unfold tailWord_907875
  simp only [CollatzResearch.WordTrace]
  refine ⟨33112921585931402550733079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22075281057287601700488719 33112921585931402550733079)
  ·
    refine ⟨49669382378897103826099619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33112921585931402550733079 49669382378897103826099619)
    ·
      refine ⟨74504073568345655739149429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49669382378897103826099619 74504073568345655739149429)
      ·
        refine ⟨6984756897032405225545259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74504073568345655739149429 6984756897032405225545259)
        ·
          refine ⟨10477135345548607838317889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6984756897032405225545259 10477135345548607838317889)
          ·
            refine ⟨7857851509161455878738417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10477135345548607838317889 7857851509161455878738417)
            ·
              refine ⟨5893388631871091909053813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7857851509161455878738417 5893388631871091909053813)
              ·
                refine ⟨552505184237914866473795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5893388631871091909053813 552505184237914866473795)
                ·
                  refine ⟨828757776356872299710693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552505184237914866473795 828757776356872299710693)
                  ·
                    refine ⟨155392083066913556195755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 828757776356872299710693 155392083066913556195755)
                    ·
                      rfl

theorem cell23_907875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 4].length) (baseStart_907875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907875 prefixEnd_907875 := by exact prefixLift 907875
  have htrace : WordTrace (prefixWord ++ tailWord_907875) baseStart_907875 baseEnd_907875 := by
    simpa [prefixWord, tailWord_907875, baseEnd_907875] using wordTrace_append hprefix tailTrace_907875
  have hstable : (prefixWord ++ tailWord_907875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907875).length < 2 ^ (prefixWord ++ tailWord_907875).sum := by decide
  have hdescent : baseEnd_907875 < baseStart_907875 := by decide
  rcases family_descends (prefixWord ++ tailWord_907875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907885 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_907885 : Nat := 118140960795 + 907885 * 2 ^ 59
def prefixEnd_907885 : Nat := 4983230072969 + 3 ^ 40 * 907885 * 2
def baseEnd_907885 : Nat := 466181384007285629462219

theorem tailTrace_907885 : CollatzResearch.WordTrace tailWord_907885 prefixEnd_907885 466181384007285629462219 := by
  unfold tailWord_907885
  simp only [CollatzResearch.WordTrace]
  refine ⟨33113286315895174258597109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22075524210596782839064739 33113286315895174258597109)
  ·
    refine ⟨3104370592115172586743479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33113286315895174258597109 3104370592115172586743479)
    ·
      refine ⟨4656555888172758880115219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3104370592115172586743479 4656555888172758880115219)
      ·
        refine ⟨6984833832259138320172829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656555888172758880115219 6984833832259138320172829)
        ·
          refine ⟨2619312687097176870064811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6984833832259138320172829 2619312687097176870064811)
          ·
            refine ⟨3928969030645765305097217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619312687097176870064811 3928969030645765305097217)
            ·
              refine ⟨2946726772984323978822913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928969030645765305097217 2946726772984323978822913)
              ·
                refine ⟨2210045079738242984117185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946726772984323978822913 2210045079738242984117185)
                ·
                  refine ⟨1657533809803682238087889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2210045079738242984117185 1657533809803682238087889)
                  ·
                    refine ⟨1243150357352761678565917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1657533809803682238087889 1243150357352761678565917)
                    ·
                      refine ⟨466181384007285629462219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1243150357352761678565917 466181384007285629462219)
                      ·
                        rfl

theorem cell23_907885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_907885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907885 prefixEnd_907885 := by exact prefixLift 907885
  have htrace : WordTrace (prefixWord ++ tailWord_907885) baseStart_907885 baseEnd_907885 := by
    simpa [prefixWord, tailWord_907885, baseEnd_907885] using wordTrace_append hprefix tailTrace_907885
  have hstable : (prefixWord ++ tailWord_907885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907885).length < 2 ^ (prefixWord ++ tailWord_907885).sum := by decide
  have hdescent : baseEnd_907885 < baseStart_907885 := by decide
  rcases family_descends (prefixWord ++ tailWord_907885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907911 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_907911 : Nat := 118140960795 + 907911 * 2 ^ 59
def prefixEnd_907911 : Nat := 4983230072969 + 3 ^ 40 * 907911 * 2
def baseEnd_907911 : Nat := 466194734504302527737099

theorem tailTrace_907911 : CollatzResearch.WordTrace tailWord_907911 prefixEnd_907911 466194734504302527737099 := by
  unfold tailWord_907911
  simp only [CollatzResearch.WordTrace]
  refine ⟨33114234613800980699043587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22076156409200653799362391 33114234613800980699043587)
  ·
    refine ⟨49671351920701471048565381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33114234613800980699043587 49671351920701471048565381)
    ·
      refine ⟨9313378485131525821606009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49671351920701471048565381 9313378485131525821606009)
      ·
        refine ⟨6985033863848644366204507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9313378485131525821606009 6985033863848644366204507)
        ·
          refine ⟨10477550795772966549306761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6985033863848644366204507 10477550795772966549306761)
          ·
            refine ⟨7858163096829724911980071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10477550795772966549306761 7858163096829724911980071)
            ·
              refine ⟨11787244645244587367970107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858163096829724911980071 11787244645244587367970107)
              ·
                refine ⟨17680866967866881051955161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787244645244587367970107 17680866967866881051955161)
                ·
                  refine ⟨13260650225900160788966371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17680866967866881051955161 13260650225900160788966371)
                  ·
                    refine ⟨19890975338850241183449557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13260650225900160788966371 19890975338850241183449557)
                    ·
                      refine ⟨466194734504302527737099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19890975338850241183449557 466194734504302527737099)
                      ·
                        rfl

theorem cell23_907911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_907911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907911 prefixEnd_907911 := by exact prefixLift 907911
  have htrace : WordTrace (prefixWord ++ tailWord_907911) baseStart_907911 baseEnd_907911 := by
    simpa [prefixWord, tailWord_907911, baseEnd_907911] using wordTrace_append hprefix tailTrace_907911
  have hstable : (prefixWord ++ tailWord_907911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907911).length < 2 ^ (prefixWord ++ tailWord_907911).sum := by decide
  have hdescent : baseEnd_907911 < baseStart_907911 := by decide
  rcases family_descends (prefixWord ++ tailWord_907911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907918 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_907918 : Nat := 118140960795 + 907918 * 2 ^ 59
def prefixEnd_907918 : Nat := 4983230072969 + 3 ^ 40 * 907918 * 2
def baseEnd_907918 : Nat := 155399442956294666783189

theorem tailTrace_907918 : CollatzResearch.WordTrace tailWord_907918 prefixEnd_907918 155399442956294666783189 := by
  unfold tailWord_907918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139311240596952611818551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22076326616517080596365605 4139311240596952611818551)
  ·
    refine ⟨6208966860895428917727827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4139311240596952611818551 6208966860895428917727827)
    ·
      refine ⟨9313450291343143376591741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6208966860895428917727827 9313450291343143376591741)
      ·
        refine ⟨3492543859253678766221903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9313450291343143376591741 3492543859253678766221903)
        ·
          refine ⟨5238815788880518149332855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492543859253678766221903 5238815788880518149332855)
          ·
            refine ⟨7858223683320777223999283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238815788880518149332855 7858223683320777223999283)
            ·
              refine ⟨11787335524981165835998925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858223683320777223999283 11787335524981165835998925)
              ·
                refine ⟨4420250821867937188499597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11787335524981165835998925 4420250821867937188499597)
                ·
                  refine ⟨1657594058200476445687349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4420250821867937188499597 1657594058200476445687349)
                  ·
                    refine ⟨155399442956294666783189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1657594058200476445687349 155399442956294666783189)
                    ·
                      rfl

theorem cell23_907918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_907918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907918 prefixEnd_907918 := by exact prefixLift 907918
  have htrace : WordTrace (prefixWord ++ tailWord_907918) baseStart_907918 baseEnd_907918 := by
    simpa [prefixWord, tailWord_907918, baseEnd_907918] using wordTrace_append hprefix tailTrace_907918
  have hstable : (prefixWord ++ tailWord_907918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907918).length < 2 ^ (prefixWord ++ tailWord_907918).sum := by decide
  have hdescent : baseEnd_907918 < baseStart_907918 := by decide
  rcases family_descends (prefixWord ++ tailWord_907918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907949 : List Nat := [1, 5, 2, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_907949 : Nat := 118140960795 + 907949 * 2 ^ 59
def prefixEnd_907949 : Nat := 4983230072969 + 3 ^ 40 * 907949 * 2
def baseEnd_907949 : Nat := 466214246769173379061925

theorem tailTrace_907949 : CollatzResearch.WordTrace tailWord_907949 prefixEnd_907949 466214246769173379061925 := by
  unfold tailWord_907949
  simp only [CollatzResearch.WordTrace]
  refine ⟨33115620587663313188926901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22077080391775542125951267 33115620587663313188926901)
  ·
    refine ⟨3104589430093435611461897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33115620587663313188926901 3104589430093435611461897)
    ·
      refine ⟨2328442072570076708596423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3104589430093435611461897 2328442072570076708596423)
      ·
        refine ⟨3492663108855115062894635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328442072570076708596423 3492663108855115062894635)
        ·
          refine ⟨5238994663282672594341953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492663108855115062894635 5238994663282672594341953)
          ·
            refine ⟨3929245997462004445756465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5238994663282672594341953 3929245997462004445756465)
            ·
              refine ⟨2946934498096503334317349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3929245997462004445756465 2946934498096503334317349)
              ·
                refine ⟨552550218393094375184503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2946934498096503334317349 552550218393094375184503)
                ·
                  refine ⟨828825327589641562776755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552550218393094375184503 828825327589641562776755)
                  ·
                    refine ⟨1243237991384462344165133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 828825327589641562776755 1243237991384462344165133)
                    ·
                      refine ⟨466214246769173379061925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1243237991384462344165133 466214246769173379061925)
                      ·
                        rfl

theorem cell23_907949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_907949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907949 prefixEnd_907949 := by exact prefixLift 907949
  have htrace : WordTrace (prefixWord ++ tailWord_907949) baseStart_907949 baseEnd_907949 := by
    simpa [prefixWord, tailWord_907949, baseEnd_907949] using wordTrace_append hprefix tailTrace_907949
  have hstable : (prefixWord ++ tailWord_907949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907949).length < 2 ^ (prefixWord ++ tailWord_907949).sum := by decide
  have hdescent : baseEnd_907949 < baseStart_907949 := by decide
  rcases family_descends (prefixWord ++ tailWord_907949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907961 : List Nat := [1, 2, 1, 4, 1, 1, 1, 12]
def baseStart_907961 : Nat := 118140960795 + 907961 * 2 ^ 59
def prefixEnd_907961 : Nat := 4983230072969 + 3 ^ 40 * 907961 * 2
def baseEnd_907961 : Nat := 17267422538408419707847

theorem tailTrace_907961 : CollatzResearch.WordTrace tailWord_907961 prefixEnd_907961 17267422538408419707847 := by
  unfold tailWord_907961
  simp only [CollatzResearch.WordTrace]
  refine ⟨33116058263619839238363737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22077372175746559492242491 33116058263619839238363737)
  ·
    refine ⟨24837043697714879428772803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33116058263619839238363737 24837043697714879428772803)
    ·
      refine ⟨37255565546572319143159205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24837043697714879428772803 37255565546572319143159205)
      ·
        refine ⟨6985418539982309839342351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37255565546572319143159205 6985418539982309839342351)
        ·
          refine ⟨10478127809973464759013527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6985418539982309839342351 10478127809973464759013527)
          ·
            refine ⟨15717191714960197138520291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10478127809973464759013527 15717191714960197138520291)
            ·
              refine ⟨23575787572440295707780437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15717191714960197138520291 23575787572440295707780437)
              ·
                refine ⟨17267422538408419707847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 23575787572440295707780437 17267422538408419707847)
                ·
                  rfl

theorem cell23_907961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 12].length) (baseStart_907961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907961 prefixEnd_907961 := by exact prefixLift 907961
  have htrace : WordTrace (prefixWord ++ tailWord_907961) baseStart_907961 baseEnd_907961 := by
    simpa [prefixWord, tailWord_907961, baseEnd_907961] using wordTrace_append hprefix tailTrace_907961
  have hstable : (prefixWord ++ tailWord_907961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907961).length < 2 ^ (prefixWord ++ tailWord_907961).sum := by decide
  have hdescent : baseEnd_907961 < baseStart_907961 := by decide
  rcases family_descends (prefixWord ++ tailWord_907961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907965 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_907965 : Nat := 118140960795 + 907965 * 2 ^ 59
def prefixEnd_907965 : Nat := 4983230072969 + 3 ^ 40 * 907965 * 2
def baseEnd_907965 : Nat := 155407487486548438820617

theorem tailTrace_907965 : CollatzResearch.WordTrace tailWord_907965 prefixEnd_907965 155407487486548438820617 := by
  unfold tailWord_907965
  simp only [CollatzResearch.WordTrace]
  refine ⟨33116204155605347921509349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22077469437070231947672899 33116204155605347921509349)
  ·
    refine ⟨6209288279176002735283003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33116204155605347921509349 6209288279176002735283003)
    ·
      refine ⟨9313932418764004102924505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209288279176002735283003 9313932418764004102924505)
      ·
        refine ⟨6985449314073003077193379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9313932418764004102924505 6985449314073003077193379)
        ·
          refine ⟨10478173971109504615790069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6985449314073003077193379 10478173971109504615790069)
          ·
            refine ⟨982328809791516057730319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10478173971109504615790069 982328809791516057730319)
            ·
              refine ⟨1473493214687274086595479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982328809791516057730319 1473493214687274086595479)
              ·
                refine ⟨2210239822030911129893219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473493214687274086595479 2210239822030911129893219)
                ·
                  refine ⟨3315359733046366694839829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210239822030911129893219 3315359733046366694839829)
                  ·
                    refine ⟨155407487486548438820617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3315359733046366694839829 155407487486548438820617)
                    ·
                      rfl

theorem cell23_907965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_907965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907965 prefixEnd_907965 := by exact prefixLift 907965
  have htrace : WordTrace (prefixWord ++ tailWord_907965) baseStart_907965 baseEnd_907965 := by
    simpa [prefixWord, tailWord_907965, baseEnd_907965] using wordTrace_append hprefix tailTrace_907965
  have hstable : (prefixWord ++ tailWord_907965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907965).length < 2 ^ (prefixWord ++ tailWord_907965).sum := by decide
  have hdescent : baseEnd_907965 < baseStart_907965 := by decide
  rcases family_descends (prefixWord ++ tailWord_907965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907968 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_907968 : Nat := 118140960795 + 907968 * 2 ^ 59
def prefixEnd_907968 : Nat := 4983230072969 + 3 ^ 40 * 907968 * 2
def baseEnd_907968 : Nat := 466224002901608804724337

theorem tailTrace_907968 : CollatzResearch.WordTrace tailWord_907968 prefixEnd_907968 466224002901608804724337 := by
  unfold tailWord_907968
  simp only [CollatzResearch.WordTrace]
  refine ⟨16558156787297239716934279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22077542383062986289245705 16558156787297239716934279)
  ·
    refine ⟨24837235180945859575401419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16558156787297239716934279 24837235180945859575401419)
    ·
      refine ⟨37255852771418789363102129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24837235180945859575401419 37255852771418789363102129)
      ·
        refine ⟨27941889578564092022326597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37255852771418789363102129 27941889578564092022326597)
        ·
          refine ⟨5239104295980767254186237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27941889578564092022326597 5239104295980767254186237)
          ·
            refine ⟨1964664110992787720319839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5239104295980767254186237 1964664110992787720319839)
            ·
              refine ⟨2946996166489181580479759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964664110992787720319839 2946996166489181580479759)
              ·
                refine ⟨4420494249733772370719639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946996166489181580479759 4420494249733772370719639)
                ·
                  refine ⟨6630741374600658556079459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420494249733772370719639 6630741374600658556079459)
                  ·
                    refine ⟨9946112061900987834119189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6630741374600658556079459 9946112061900987834119189)
                    ·
                      refine ⟨466224002901608804724337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9946112061900987834119189 466224002901608804724337)
                      ·
                        rfl

theorem cell23_907968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_907968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907968 prefixEnd_907968 := by exact prefixLift 907968
  have htrace : WordTrace (prefixWord ++ tailWord_907968) baseStart_907968 baseEnd_907968 := by
    simpa [prefixWord, tailWord_907968, baseEnd_907968] using wordTrace_append hprefix tailTrace_907968
  have hstable : (prefixWord ++ tailWord_907968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907968).length < 2 ^ (prefixWord ++ tailWord_907968).sum := by decide
  have hdescent : baseEnd_907968 < baseStart_907968 := by decide
  rcases family_descends (prefixWord ++ tailWord_907968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907969 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 1, 5]
def baseStart_907969 : Nat := 118140960795 + 907969 * 2 ^ 59
def prefixEnd_907969 : Nat := 4983230072969 + 3 ^ 40 * 907969 * 2
def baseEnd_907969 : Nat := 155408172127421100270611

theorem tailTrace_907969 : CollatzResearch.WordTrace tailWord_907969 prefixEnd_907969 155408172127421100270611 := by
  unfold tailWord_907969
  simp only [CollatzResearch.WordTrace]
  refine ⟨33116350047590856604654961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22077566698393904403103307 33116350047590856604654961)
  ·
    refine ⟨24837262535693142453491221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33116350047590856604654961 24837262535693142453491221)
    ·
      refine ⟨1164246681360616052507401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24837262535693142453491221 1164246681360616052507401)
      ·
        refine ⟨873185011020462039380551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1164246681360616052507401 873185011020462039380551)
        ·
          refine ⟨1309777516530693059070827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873185011020462039380551 1309777516530693059070827)
          ·
            refine ⟨1964666274796039588606241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309777516530693059070827 1964666274796039588606241)
            ·
              refine ⟨1473499706097029691454681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964666274796039588606241 1473499706097029691454681)
              ·
                refine ⟨1105124779572772268591011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473499706097029691454681 1105124779572772268591011)
                ·
                  refine ⟨1657687169359158402886517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105124779572772268591011 1657687169359158402886517)
                  ·
                    refine ⟨155408172127421100270611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1657687169359158402886517 155408172127421100270611)
                    ·
                      rfl

theorem cell23_907969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_907969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907969 prefixEnd_907969 := by exact prefixLift 907969
  have htrace : WordTrace (prefixWord ++ tailWord_907969) baseStart_907969 baseEnd_907969 := by
    simpa [prefixWord, tailWord_907969, baseEnd_907969] using wordTrace_append hprefix tailTrace_907969
  have hstable : (prefixWord ++ tailWord_907969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907969).length < 2 ^ (prefixWord ++ tailWord_907969).sum := by decide
  have hdescent : baseEnd_907969 < baseStart_907969 := by decide
  rcases family_descends (prefixWord ++ tailWord_907969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907972 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_907972 : Nat := 118140960795 + 907972 * 2 ^ 59
def prefixEnd_907972 : Nat := 4983230072969 + 3 ^ 40 * 907972 * 2
def baseEnd_907972 : Nat := 466226056824226789074319

theorem tailTrace_907972 : CollatzResearch.WordTrace tailWord_907972 prefixEnd_907972 466226056824226789074319 := by
  unfold tailWord_907972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16558229733289994058507085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22077639644386658744676113 16558229733289994058507085)
  ·
    refine ⟨6209336149983747771940157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16558229733289994058507085 6209336149983747771940157)
    ·
      refine ⟨2328501056243905414477559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6209336149983747771940157 2328501056243905414477559)
      ·
        refine ⟨3492751584365858121716339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328501056243905414477559 3492751584365858121716339)
        ·
          refine ⟨5239127376548787182574509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492751584365858121716339 5239127376548787182574509)
          ·
            refine ⟨1964672766205795193465441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5239127376548787182574509 1964672766205795193465441)
            ·
              refine ⟨1473504574654346395099081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964672766205795193465441 1473504574654346395099081)
              ·
                refine ⟨1105128430990759796324311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473504574654346395099081 1105128430990759796324311)
                ·
                  refine ⟨1657692646486139694486467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105128430990759796324311 1657692646486139694486467)
                  ·
                    refine ⟨2486538969729209541729701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1657692646486139694486467 2486538969729209541729701)
                    ·
                      refine ⟨466226056824226789074319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2486538969729209541729701 466226056824226789074319)
                      ·
                        rfl

theorem cell23_907972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_907972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907972 prefixEnd_907972 := by exact prefixLift 907972
  have htrace : WordTrace (prefixWord ++ tailWord_907972) baseStart_907972 baseEnd_907972 := by
    simpa [prefixWord, tailWord_907972, baseEnd_907972] using wordTrace_append hprefix tailTrace_907972
  have hstable : (prefixWord ++ tailWord_907972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907972).length < 2 ^ (prefixWord ++ tailWord_907972).sum := by decide
  have hdescent : baseEnd_907972 < baseStart_907972 := by decide
  rcases family_descends (prefixWord ++ tailWord_907972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907978 : List Nat := [3, 1, 2, 1, 4, 2, 1, 9]
def baseStart_907978 : Nat := 118140960795 + 907978 * 2 ^ 59
def prefixEnd_907978 : Nat := 4983230072969 + 3 ^ 40 * 907978 * 2
def baseEnd_907978 : Nat := 17267745841042732059233

theorem tailTrace_907978 : CollatzResearch.WordTrace tailWord_907978 prefixEnd_907978 17267745841042732059233 := by
  unfold tailWord_907978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279169576139562785433147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22077785536372167427821725 8279169576139562785433147)
  ·
    refine ⟨12418754364209344178149721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8279169576139562785433147 12418754364209344178149721)
    ·
      refine ⟨9314065773157008133612291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12418754364209344178149721 9314065773157008133612291)
      ·
        refine ⟨13971098659735512200418437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314065773157008133612291 13971098659735512200418437)
        ·
          refine ⟨2619580998700408537578457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13971098659735512200418437 2619580998700408537578457)
          ·
            refine ⟨1964685749025306403183843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619580998700408537578457 1964685749025306403183843)
            ·
              refine ⟨2947028623537959604775765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964685749025306403183843 2947028623537959604775765)
              ·
                refine ⟨17267745841042732059233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2947028623537959604775765 17267745841042732059233)
                ·
                  rfl

theorem cell23_907978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_907978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_907978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_907978 prefixEnd_907978 := by exact prefixLift 907978
  have htrace : WordTrace (prefixWord ++ tailWord_907978) baseStart_907978 baseEnd_907978 := by
    simpa [prefixWord, tailWord_907978, baseEnd_907978] using wordTrace_append hprefix tailTrace_907978
  have hstable : (prefixWord ++ tailWord_907978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907978).length < 2 ^ (prefixWord ++ tailWord_907978).sum := by decide
  have hdescent : baseEnd_907978 < baseStart_907978 := by decide
  rcases family_descends (prefixWord ++ tailWord_907978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908085 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 7]
def baseStart_908085 : Nat := 118140960795 + 908085 * 2 ^ 59
def prefixEnd_908085 : Nat := 4983230072969 + 3 ^ 40 * 908085 * 2
def baseEnd_908085 : Nat := 51809342237576094106811

theorem tailTrace_908085 : CollatzResearch.WordTrace tailWord_908085 prefixEnd_908085 51809342237576094106811 := by
  unfold tailWord_908085
  simp only [CollatzResearch.WordTrace]
  refine ⟨33120580915170608415877709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22080387276780405610585139 33120580915170608415877709)
  ·
    refine ⟨12420217843188978155954141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33120580915170608415877709 12420217843188978155954141)
    ·
      refine ⟨4657581691195866808482803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12420217843188978155954141 4657581691195866808482803)
      ·
        refine ⟨6986372536793800212724205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657581691195866808482803 6986372536793800212724205)
        ·
          refine ⟨2619889701297675079771577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6986372536793800212724205 2619889701297675079771577)
          ·
            refine ⟨1964917275973256309828683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619889701297675079771577 1964917275973256309828683)
            ·
              refine ⟨2947375913959884464743025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964917275973256309828683 2947375913959884464743025)
              ·
                refine ⟨2210531935469913348557269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947375913959884464743025 2210531935469913348557269)
                ·
                  refine ⟨51809342237576094106811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2210531935469913348557269 51809342237576094106811)
                  ·
                    rfl

theorem cell23_908085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_908085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908085 prefixEnd_908085 := by exact prefixLift 908085
  have htrace : WordTrace (prefixWord ++ tailWord_908085) baseStart_908085 baseEnd_908085 := by
    simpa [prefixWord, tailWord_908085, baseEnd_908085] using wordTrace_append hprefix tailTrace_908085
  have hstable : (prefixWord ++ tailWord_908085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908085).length < 2 ^ (prefixWord ++ tailWord_908085).sum := by decide
  have hdescent : baseEnd_908085 < baseStart_908085 := by decide
  rcases family_descends (prefixWord ++ tailWord_908085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908100 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_908100 : Nat := 118140960795 + 908100 * 2 ^ 59
def prefixEnd_908100 : Nat := 4983230072969 + 3 ^ 40 * 908100 * 2
def baseEnd_908100 : Nat := 466291782348002288273731

theorem tailTrace_908100 : CollatzResearch.WordTrace tailWord_908100 prefixEnd_908100 466291782348002288273731 := by
  unfold tailWord_908100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16560564005058132988836877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22080752006744177318449169 16560564005058132988836877)
  ·
    refine ⟨6210211501896799870813829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16560564005058132988836877 6210211501896799870813829)
    ·
      refine ⟨1164414656605649975777593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6210211501896799870813829 1164414656605649975777593)
      ·
        refine ⟨873310992454237481833195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1164414656605649975777593 873310992454237481833195)
        ·
          refine ⟨1309966488681356222749793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873310992454237481833195 1309966488681356222749793)
          ·
            refine ⟨982474866511017167062345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309966488681356222749793 982474866511017167062345)
            ·
              refine ⟨736856149883262875296759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982474866511017167062345 736856149883262875296759)
              ·
                refine ⟨1105284224824894312945139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736856149883262875296759 1105284224824894312945139)
                ·
                  refine ⟨1657926337237341469417709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105284224824894312945139 1657926337237341469417709)
                  ·
                    refine ⟨621722376464003051031641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657926337237341469417709 621722376464003051031641)
                    ·
                      refine ⟨466291782348002288273731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621722376464003051031641 466291782348002288273731)
                      ·
                        rfl

theorem cell23_908100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_908100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908100 prefixEnd_908100 := by exact prefixLift 908100
  have htrace : WordTrace (prefixWord ++ tailWord_908100) baseStart_908100 baseEnd_908100 := by
    simpa [prefixWord, tailWord_908100, baseEnd_908100] using wordTrace_append hprefix tailTrace_908100
  have hstable : (prefixWord ++ tailWord_908100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908100).length < 2 ^ (prefixWord ++ tailWord_908100).sum := by decide
  have hdescent : baseEnd_908100 < baseStart_908100 := by decide
  rcases family_descends (prefixWord ++ tailWord_908100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908113 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 2, 2, 2]
def baseStart_908113 : Nat := 118140960795 + 908113 * 2 ^ 59
def prefixEnd_908113 : Nat := 4983230072969 + 3 ^ 40 * 908113 * 2
def baseEnd_908113 : Nat := 466298457596510737411171

theorem tailTrace_908113 : CollatzResearch.WordTrace tailWord_908113 prefixEnd_908113 466298457596510737411171 := by
  unfold tailWord_908113
  simp only [CollatzResearch.WordTrace]
  refine ⟨33121602159069169197896993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22081068106046112798597995 33121602159069169197896993)
  ·
    refine ⟨24841201619301876898422745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33121602159069169197896993 24841201619301876898422745)
    ·
      refine ⟨18630901214476407673817059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24841201619301876898422745 18630901214476407673817059)
      ·
        refine ⟨27946351821714611510725589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18630901214476407673817059 27946351821714611510725589)
        ·
          refine ⟨654992620821436207282631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27946351821714611510725589 654992620821436207282631)
          ·
            refine ⟨982488931232154310923947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654992620821436207282631 982488931232154310923947)
            ·
              refine ⟨1473733396848231466385921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982488931232154310923947 1473733396848231466385921)
              ·
                refine ⟨1105300047636173599789441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473733396848231466385921 1105300047636173599789441)
                ·
                  refine ⟨828975035727130199842081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1105300047636173599789441 828975035727130199842081)
                  ·
                    refine ⟨621731276795347649881561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 828975035727130199842081 621731276795347649881561)
                    ·
                      refine ⟨466298457596510737411171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621731276795347649881561 466298457596510737411171)
                      ·
                        rfl

theorem cell23_908113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_908113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908113 prefixEnd_908113 := by exact prefixLift 908113
  have htrace : WordTrace (prefixWord ++ tailWord_908113) baseStart_908113 baseEnd_908113 := by
    simpa [prefixWord, tailWord_908113, baseEnd_908113] using wordTrace_append hprefix tailTrace_908113
  have hstable : (prefixWord ++ tailWord_908113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908113).length < 2 ^ (prefixWord ++ tailWord_908113).sum := by decide
  have hdescent : baseEnd_908113 < baseStart_908113 := by decide
  rcases family_descends (prefixWord ++ tailWord_908113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908135 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_908135 : Nat := 118140960795 + 908135 * 2 ^ 59
def prefixEnd_908135 : Nat := 4983230072969 + 3 ^ 40 * 908135 * 2
def baseEnd_908135 : Nat := 466309754170909651336069

theorem tailTrace_908135 : CollatzResearch.WordTrace tailWord_908135 prefixEnd_908135 466309754170909651336069 := by
  unfold tailWord_908135
  simp only [CollatzResearch.WordTrace]
  refine ⟨33122404564989466955197859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22081603043326311303465239 33122404564989466955197859)
  ·
    refine ⟨49683606847484200432796789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33122404564989466955197859 49683606847484200432796789)
    ·
      refine ⟨4657838141951643790574699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49683606847484200432796789 4657838141951643790574699)
      ·
        refine ⟨6986757212927465685862049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657838141951643790574699 6986757212927465685862049)
        ·
          refine ⟨5240067909695599264396537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6986757212927465685862049 5240067909695599264396537)
          ·
            refine ⟨3930050932271699448297403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5240067909695599264396537 3930050932271699448297403)
            ·
              refine ⟨5895076398407549172446105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930050932271699448297403 5895076398407549172446105)
              ·
                refine ⟨4421307298805661879334579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5895076398407549172446105 4421307298805661879334579)
                ·
                  refine ⟨6631960948208492819001869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421307298805661879334579 6631960948208492819001869)
                  ·
                    refine ⟨2486985355578184807125701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6631960948208492819001869 2486985355578184807125701)
                    ·
                      refine ⟨466309754170909651336069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2486985355578184807125701 466309754170909651336069)
                      ·
                        rfl

theorem cell23_908135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_908135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908135 prefixEnd_908135 := by exact prefixLift 908135
  have htrace : WordTrace (prefixWord ++ tailWord_908135) baseStart_908135 baseEnd_908135 := by
    simpa [prefixWord, tailWord_908135, baseEnd_908135] using wordTrace_append hprefix tailTrace_908135
  have hstable : (prefixWord ++ tailWord_908135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908135).length < 2 ^ (prefixWord ++ tailWord_908135).sum := by decide
  have hdescent : baseEnd_908135 < baseStart_908135 := by decide
  rcases family_descends (prefixWord ++ tailWord_908135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908155 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 3]
def baseStart_908155 : Nat := 118140960795 + 908155 * 2 ^ 59
def prefixEnd_908155 : Nat := 4983230072969 + 3 ^ 40 * 908155 * 2
def baseEnd_908155 : Nat := 466320023783999573085977

theorem tailTrace_908155 : CollatzResearch.WordTrace tailWord_908155 prefixEnd_908155 466320023783999573085977 := by
  unfold tailWord_908155
  simp only [CollatzResearch.WordTrace]
  refine ⟨33123134024917010370925919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22082089349944673580617279 33123134024917010370925919)
  ·
    refine ⟨49684701037375515556388879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33123134024917010370925919 49684701037375515556388879)
    ·
      refine ⟨74527051556063273334583319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49684701037375515556388879 74527051556063273334583319)
      ·
        refine ⟨111790577334094910001874979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74527051556063273334583319 111790577334094910001874979)
        ·
          refine ⟨167685866001142365002812469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111790577334094910001874979 167685866001142365002812469)
          ·
            refine ⟨15720549937607096719013669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167685866001142365002812469 15720549937607096719013669)
            ·
              refine ⟨2947603113301330634815063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15720549937607096719013669 2947603113301330634815063)
              ·
                refine ⟨4421404669951995952222595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947603113301330634815063 4421404669951995952222595)
                ·
                  refine ⟨6632107004927993928333893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421404669951995952222595 6632107004927993928333893)
                  ·
                    refine ⟨1243520063423998861562605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632107004927993928333893 1243520063423998861562605)
                    ·
                      refine ⟨466320023783999573085977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1243520063423998861562605 466320023783999573085977)
                      ·
                        rfl

theorem cell23_908155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 3].length) (baseStart_908155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908155 prefixEnd_908155 := by exact prefixLift 908155
  have htrace : WordTrace (prefixWord ++ tailWord_908155) baseStart_908155 baseEnd_908155 := by
    simpa [prefixWord, tailWord_908155, baseEnd_908155] using wordTrace_append hprefix tailTrace_908155
  have hstable : (prefixWord ++ tailWord_908155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908155).length < 2 ^ (prefixWord ++ tailWord_908155).sum := by decide
  have hdescent : baseEnd_908155 < baseStart_908155 := by decide
  rcases family_descends (prefixWord ++ tailWord_908155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908192 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 6]
def baseStart_908192 : Nat := 118140960795 + 908192 * 2 ^ 59
def prefixEnd_908192 : Nat := 4983230072969 + 3 ^ 40 * 908192 * 2
def baseEnd_908192 : Nat := 51815446952023992035923

theorem tailTrace_908192 : CollatzResearch.WordTrace tailWord_908192 prefixEnd_908192 51815446952023992035923 := by
  unfold tailWord_908192
  simp only [CollatzResearch.WordTrace]
  refine ⟨16562241762891482845011415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22082989017188643793348553 16562241762891482845011415)
  ·
    refine ⟨24843362644337224267517123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16562241762891482845011415 24843362644337224267517123)
    ·
      refine ⟨37265043966505836401275685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24843362644337224267517123 37265043966505836401275685)
      ·
        refine ⟨6987195743719844325239191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37265043966505836401275685 6987195743719844325239191)
        ·
          refine ⟨10480793615579766487858787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987195743719844325239191 10480793615579766487858787)
          ·
            refine ⟨15721190423369649731788181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480793615579766487858787 15721190423369649731788181)
            ·
              refine ⟨736930801095452331177571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15721190423369649731788181 736930801095452331177571)
              ·
                refine ⟨1105396201643178496766357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736930801095452331177571 1105396201643178496766357)
                ·
                  refine ⟨51815446952023992035923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1105396201643178496766357 51815446952023992035923)
                  ·
                    rfl

theorem cell23_908192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 6].length) (baseStart_908192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908192 prefixEnd_908192 := by exact prefixLift 908192
  have htrace : WordTrace (prefixWord ++ tailWord_908192) baseStart_908192 baseEnd_908192 := by
    simpa [prefixWord, tailWord_908192, baseEnd_908192] using wordTrace_append hprefix tailTrace_908192
  have hstable : (prefixWord ++ tailWord_908192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908192).length < 2 ^ (prefixWord ++ tailWord_908192).sum := by decide
  have hdescent : baseEnd_908192 < baseStart_908192 := by decide
  rcases family_descends (prefixWord ++ tailWord_908192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908236 : List Nat := [2, 2, 1, 4, 1, 1, 3, 4, 1, 1, 3]
def baseStart_908236 : Nat := 118140960795 + 908236 * 2 ^ 59
def prefixEnd_908236 : Nat := 4983230072969 + 3 ^ 40 * 908236 * 2
def baseEnd_908236 : Nat := 466361615717013756173105

theorem tailTrace_908236 : CollatzResearch.WordTrace tailWord_908236 prefixEnd_908236 466361615717013756173105 := by
  unfold tailWord_908236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563044168811780602312281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22084058891749040803083041 16563044168811780602312281)
  ·
    refine ⟨12422283126608835451734211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16563044168811780602312281 12422283126608835451734211)
    ·
      refine ⟨18633424689913253177601317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12422283126608835451734211 18633424689913253177601317)
      ·
        refine ⟨3493767129358734970800247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18633424689913253177601317 3493767129358734970800247)
        ·
          refine ⟨5240650694038102456200371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493767129358734970800247 5240650694038102456200371)
          ·
            refine ⟨7860976041057153684300557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240650694038102456200371 7860976041057153684300557)
            ·
              refine ⟨2947866015396432631612709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7860976041057153684300557 2947866015396432631612709)
              ·
                refine ⟨552724877886831118427383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2947866015396432631612709 552724877886831118427383)
                ·
                  refine ⟨829087316830246677641075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552724877886831118427383 829087316830246677641075)
                  ·
                    refine ⟨1243630975245370016461613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829087316830246677641075 1243630975245370016461613)
                    ·
                      refine ⟨466361615717013756173105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1243630975245370016461613 466361615717013756173105)
                      ·
                        rfl

theorem cell23_908236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_908236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908236 prefixEnd_908236 := by exact prefixLift 908236
  have htrace : WordTrace (prefixWord ++ tailWord_908236) baseStart_908236 baseEnd_908236 := by
    simpa [prefixWord, tailWord_908236, baseEnd_908236] using wordTrace_append hprefix tailTrace_908236
  have hstable : (prefixWord ++ tailWord_908236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908236).length < 2 ^ (prefixWord ++ tailWord_908236).sum := by decide
  have hdescent : baseEnd_908236 < baseStart_908236 := by decide
  rcases family_descends (prefixWord ++ tailWord_908236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908285 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_908285 : Nat := 118140960795 + 908285 * 2 ^ 59
def prefixEnd_908285 : Nat := 4983230072969 + 3 ^ 40 * 908285 * 2
def baseEnd_908285 : Nat := 466386776269084064460379

theorem tailTrace_908285 : CollatzResearch.WordTrace tailWord_908285 prefixEnd_908285 466386776269084064460379 := by
  unfold tailWord_908285
  simp only [CollatzResearch.WordTrace]
  refine ⟨33127875514446042573158309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22085250342964028382105539 33127875514446042573158309)
  ·
    refine ⟨6211476658958632982467183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33127875514446042573158309 6211476658958632982467183)
    ·
      refine ⟨9317214988437949473700775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6211476658958632982467183 9317214988437949473700775)
      ·
        refine ⟨13975822482656924210551163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317214988437949473700775 13975822482656924210551163)
        ·
          refine ⟨20963733723985386315826745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13975822482656924210551163 20963733723985386315826745)
          ·
            refine ⟨15722800292989039736870059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20963733723985386315826745 15722800292989039736870059)
            ·
              refine ⟨23584200439483559605305089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722800292989039736870059 23584200439483559605305089)
              ·
                refine ⟨17688150329612669703978817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23584200439483559605305089 17688150329612669703978817)
                ·
                  refine ⟨13266112747209502277984113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17688150329612669703978817 13266112747209502277984113)
                  ·
                    refine ⟨9949584560407126708488085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13266112747209502277984113 9949584560407126708488085)
                    ·
                      refine ⟨466386776269084064460379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9949584560407126708488085 466386776269084064460379)
                      ·
                        rfl

theorem cell23_908285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_908285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908285 prefixEnd_908285 := by exact prefixLift 908285
  have htrace : WordTrace (prefixWord ++ tailWord_908285) baseStart_908285 baseEnd_908285 := by
    simpa [prefixWord, tailWord_908285, baseEnd_908285] using wordTrace_append hprefix tailTrace_908285
  have hstable : (prefixWord ++ tailWord_908285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908285).length < 2 ^ (prefixWord ++ tailWord_908285).sum := by decide
  have hdescent : baseEnd_908285 < baseStart_908285 := by decide
  rcases family_descends (prefixWord ++ tailWord_908285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908286 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_908286 : Nat := 118140960795 + 908286 * 2 ^ 59
def prefixEnd_908286 : Nat := 4983230072969 + 3 ^ 40 * 908286 * 2
def baseEnd_908286 : Nat := 155462429916579520182625

theorem tailTrace_908286 : CollatzResearch.WordTrace tailWord_908286 prefixEnd_908286 155462429916579520182625 := by
  unfold tailWord_908286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140988998430302467993089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22085274658294946495963141 4140988998430302467993089)
  ·
    refine ⟨3105741748822726850994817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4140988998430302467993089 3105741748822726850994817)
    ·
      refine ⟨2329306311617045138246113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3105741748822726850994817 2329306311617045138246113)
      ·
        refine ⟨1746979733712783853684585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2329306311617045138246113 1746979733712783853684585)
        ·
          refine ⟨1310234800284587890263439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746979733712783853684585 1310234800284587890263439)
          ·
            refine ⟨1965352200426881835395159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310234800284587890263439 1965352200426881835395159)
            ·
              refine ⟨2948028300640322753092739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965352200426881835395159 2948028300640322753092739)
              ·
                refine ⟨4422042450960484129639109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948028300640322753092739 4422042450960484129639109)
                ·
                  refine ⟨829132959555090774307333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4422042450960484129639109 829132959555090774307333)
                  ·
                    refine ⟨155462429916579520182625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 829132959555090774307333 155462429916579520182625)
                    ·
                      rfl

theorem cell23_908286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_908286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908286 prefixEnd_908286 := by exact prefixLift 908286
  have htrace : WordTrace (prefixWord ++ tailWord_908286) baseStart_908286 baseEnd_908286 := by
    simpa [prefixWord, tailWord_908286, baseEnd_908286] using wordTrace_append hprefix tailTrace_908286
  have hstable : (prefixWord ++ tailWord_908286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908286).length < 2 ^ (prefixWord ++ tailWord_908286).sum := by decide
  have hdescent : baseEnd_908286 < baseStart_908286 := by decide
  rcases family_descends (prefixWord ++ tailWord_908286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908305 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_908305 : Nat := 118140960795 + 908305 * 2 ^ 59
def prefixEnd_908305 : Nat := 4983230072969 + 3 ^ 40 * 908305 * 2
def baseEnd_908305 : Nat := 466397045882173986210287

theorem tailTrace_908305 : CollatzResearch.WordTrace tailWord_908305 prefixEnd_908305 466397045882173986210287 := by
  unfold tailWord_908305
  simp only [CollatzResearch.WordTrace]
  refine ⟨33128604974373585988886369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22085736649582390659257579 33128604974373585988886369)
  ·
    refine ⟨24846453730780189491664777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33128604974373585988886369 24846453730780189491664777)
    ·
      refine ⟨18634840298085142118748583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24846453730780189491664777 18634840298085142118748583)
      ·
        refine ⟨27952260447127713178122875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18634840298085142118748583 27952260447127713178122875)
        ·
          refine ⟨41928390670691569767184313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27952260447127713178122875 41928390670691569767184313)
          ·
            refine ⟨31446293003018677325388235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41928390670691569767184313 31446293003018677325388235)
            ·
              refine ⟨47169439504528015988082353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31446293003018677325388235 47169439504528015988082353)
              ·
                refine ⟨35377079628396011991061765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47169439504528015988082353 35377079628396011991061765)
                ·
                  refine ⟨6633202430324252248324081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35377079628396011991061765 6633202430324252248324081)
                  ·
                    refine ⟨4974901822743189186243061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633202430324252248324081 4974901822743189186243061)
                    ·
                      refine ⟨466397045882173986210287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4974901822743189186243061 466397045882173986210287)
                      ·
                        rfl

theorem cell23_908305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_908305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908305 prefixEnd_908305 := by exact prefixLift 908305
  have htrace : WordTrace (prefixWord ++ tailWord_908305) baseStart_908305 baseEnd_908305 := by
    simpa [prefixWord, tailWord_908305, baseEnd_908305] using wordTrace_append hprefix tailTrace_908305
  have hstable : (prefixWord ++ tailWord_908305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908305).length < 2 ^ (prefixWord ++ tailWord_908305).sum := by decide
  have hdescent : baseEnd_908305 < baseStart_908305 := by decide
  rcases family_descends (prefixWord ++ tailWord_908305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908309 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_908309 : Nat := 118140960795 + 908309 * 2 ^ 59
def prefixEnd_908309 : Nat := 4983230072969 + 3 ^ 40 * 908309 * 2
def baseEnd_908309 : Nat := 466399099804791970560269

theorem tailTrace_908309 : CollatzResearch.WordTrace tailWord_908309 prefixEnd_908309 466399099804791970560269 := by
  unfold tailWord_908309
  simp only [CollatzResearch.WordTrace]
  refine ⟨33128750866359094672031981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22085833910906063114687987 33128750866359094672031981)
  ·
    refine ⟨12423281574884660502011993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33128750866359094672031981 12423281574884660502011993)
    ·
      refine ⟨9317461181163495376508995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12423281574884660502011993 9317461181163495376508995)
      ·
        refine ⟨13976191771745243064763493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317461181163495376508995 13976191771745243064763493)
        ·
          refine ⟨2620535957202233074643155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13976191771745243064763493 2620535957202233074643155)
          ·
            refine ⟨3930803935803349611964733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620535957202233074643155 3930803935803349611964733)
            ·
              refine ⟨1474051475926256104486775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3930803935803349611964733 1474051475926256104486775)
              ·
                refine ⟨2211077213889384156730163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474051475926256104486775 2211077213889384156730163)
                ·
                  refine ⟨3316615820834076235095245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211077213889384156730163 3316615820834076235095245)
                  ·
                    refine ⟨1243730932812778588160717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3316615820834076235095245 1243730932812778588160717)
                    ·
                      refine ⟨466399099804791970560269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1243730932812778588160717 466399099804791970560269)
                      ·
                        rfl

theorem cell23_908309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_908309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908309 prefixEnd_908309 := by exact prefixLift 908309
  have htrace : WordTrace (prefixWord ++ tailWord_908309) baseStart_908309 baseEnd_908309 := by
    simpa [prefixWord, tailWord_908309, baseEnd_908309] using wordTrace_append hprefix tailTrace_908309
  have hstable : (prefixWord ++ tailWord_908309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908309).length < 2 ^ (prefixWord ++ tailWord_908309).sum := by decide
  have hdescent : baseEnd_908309 < baseStart_908309 := by decide
  rcases family_descends (prefixWord ++ tailWord_908309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908315 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4]
def baseStart_908315 : Nat := 118140960795 + 908315 * 2 ^ 59
def prefixEnd_908315 : Nat := 4983230072969 + 3 ^ 40 * 908315 * 2
def baseEnd_908315 : Nat := 466402180688718947085241

theorem tailTrace_908315 : CollatzResearch.WordTrace tailWord_908315 prefixEnd_908315 466402180688718947085241 := by
  unfold tailWord_908315
  simp only [CollatzResearch.WordTrace]
  refine ⟨33128969704337357696750399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22085979802891571797833599 33128969704337357696750399)
  ·
    refine ⟨49693454556506036545125599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33128969704337357696750399 49693454556506036545125599)
    ·
      refine ⟨74540181834759054817688399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49693454556506036545125599 74540181834759054817688399)
      ·
        refine ⟨111810272752138582226532599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74540181834759054817688399 111810272752138582226532599)
        ·
          refine ⟨167715409128207873339798899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111810272752138582226532599 167715409128207873339798899)
          ·
            refine ⟨251573113692311810009698349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167715409128207873339798899 251573113692311810009698349)
            ·
              refine ⟨94339917634616928753636881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251573113692311810009698349 94339917634616928753636881)
              ·
                refine ⟨70754938225962696565227661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94339917634616928753636881 70754938225962696565227661)
                ·
                  refine ⟨26533101834736011211960373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70754938225962696565227661 26533101834736011211960373)
                  ·
                    refine ⟨2487478297006501051121285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26533101834736011211960373 2487478297006501051121285)
                    ·
                      refine ⟨466402180688718947085241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2487478297006501051121285 466402180688718947085241)
                      ·
                        rfl

theorem cell23_908315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_908315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908315 prefixEnd_908315 := by exact prefixLift 908315
  have htrace : WordTrace (prefixWord ++ tailWord_908315) baseStart_908315 baseEnd_908315 := by
    simpa [prefixWord, tailWord_908315, baseEnd_908315] using wordTrace_append hprefix tailTrace_908315
  have hstable : (prefixWord ++ tailWord_908315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908315).length < 2 ^ (prefixWord ++ tailWord_908315).sum := by decide
  have hdescent : baseEnd_908315 < baseStart_908315 := by decide
  rcases family_descends (prefixWord ++ tailWord_908315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908316 : List Nat := [2, 2, 3, 1, 5, 1, 2, 7]
def baseStart_908316 : Nat := 118140960795 + 908316 * 2 ^ 59
def prefixEnd_908316 : Nat := 4983230072969 + 3 ^ 40 * 908316 * 2
def baseEnd_908316 : Nat := 17274173858124942339731

theorem tailTrace_908316 : CollatzResearch.WordTrace tailWord_908316 prefixEnd_908316 17274173858124942339731 := by
  unfold tailWord_908316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564503088666867433768401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22086004118222489911691201 16564503088666867433768401)
  ·
    refine ⟨12423377316500150575326301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16564503088666867433768401 12423377316500150575326301)
    ·
      refine ⟨4658766493687556465747363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12423377316500150575326301 4658766493687556465747363)
      ·
        refine ⟨6988149740531334698621045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658766493687556465747363 6988149740531334698621045)
        ·
          refine ⟨655139038174812627995723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6988149740531334698621045 655139038174812627995723)
          ·
            refine ⟨982708557262218941993585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655139038174812627995723 982708557262218941993585)
            ·
              refine ⟨737031417946664206495189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982708557262218941993585 737031417946664206495189)
              ·
                refine ⟨17274173858124942339731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 737031417946664206495189 17274173858124942339731)
                ·
                  rfl

theorem cell23_908316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 7].length) (baseStart_908316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908316 prefixEnd_908316 := by exact prefixLift 908316
  have htrace : WordTrace (prefixWord ++ tailWord_908316) baseStart_908316 baseEnd_908316 := by
    simpa [prefixWord, tailWord_908316, baseEnd_908316] using wordTrace_append hprefix tailTrace_908316
  have hstable : (prefixWord ++ tailWord_908316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908316).length < 2 ^ (prefixWord ++ tailWord_908316).sum := by decide
  have hdescent : baseEnd_908316 < baseStart_908316 := by decide
  rcases family_descends (prefixWord ++ tailWord_908316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908322 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_908322 : Nat := 118140960795 + 908322 * 2 ^ 59
def prefixEnd_908322 : Nat := 4983230072969 + 3 ^ 40 * 908322 * 2
def baseEnd_908322 : Nat := 466405775053300419697709

theorem tailTrace_908322 : CollatzResearch.WordTrace tailWord_908322 prefixEnd_908322 466405775053300419697709 := by
  unfold tailWord_908322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282306253827999473063805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22086150010207998594836813 8282306253827999473063805)
  ·
    refine ⟨3105864845185499802398927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8282306253827999473063805 3105864845185499802398927)
    ·
      refine ⟨4658797267778249703598391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105864845185499802398927 4658797267778249703598391)
      ·
        refine ⟨6988195901667374555397587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658797267778249703598391 6988195901667374555397587)
        ·
          refine ⟨10482293852501061833096381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988195901667374555397587 10482293852501061833096381)
          ·
            refine ⟨3930860194687898187411143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10482293852501061833096381 3930860194687898187411143)
            ·
              refine ⟨5896290292031847281116715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930860194687898187411143 5896290292031847281116715)
              ·
                refine ⟨8844435438047770921675073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896290292031847281116715 8844435438047770921675073)
                ·
                  refine ⟨6633326578535828191256305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8844435438047770921675073 6633326578535828191256305)
                  ·
                    refine ⟨4974994933901871143442229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633326578535828191256305 4974994933901871143442229)
                    ·
                      refine ⟨466405775053300419697709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4974994933901871143442229 466405775053300419697709)
                      ·
                        rfl

theorem cell23_908322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_908322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908322 prefixEnd_908322 := by exact prefixLift 908322
  have htrace : WordTrace (prefixWord ++ tailWord_908322) baseStart_908322 baseEnd_908322 := by
    simpa [prefixWord, tailWord_908322, baseEnd_908322] using wordTrace_append hprefix tailTrace_908322
  have hstable : (prefixWord ++ tailWord_908322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908322).length < 2 ^ (prefixWord ++ tailWord_908322).sum := by decide
  have hdescent : baseEnd_908322 < baseStart_908322 := by decide
  rcases family_descends (prefixWord ++ tailWord_908322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908327 : List Nat := [1, 1, 7, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_908327 : Nat := 118140960795 + 908327 * 2 ^ 59
def prefixEnd_908327 : Nat := 4983230072969 + 3 ^ 40 * 908327 * 2
def baseEnd_908327 : Nat := 466408342456572900135187

theorem tailTrace_908327 : CollatzResearch.WordTrace tailWord_908327 prefixEnd_908327 466408342456572900135187 := by
  unfold tailWord_908327
  simp only [CollatzResearch.WordTrace]
  refine ⟨33129407380293883746187235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22086271586862589164124823 33129407380293883746187235)
  ·
    refine ⟨49694111070440825619280853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33129407380293883746187235 49694111070440825619280853)
    ·
      refine ⟨1164705728213456850451895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 49694111070440825619280853 1164705728213456850451895)
      ·
        refine ⟨1747058592320185275677843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164705728213456850451895 1747058592320185275677843)
        ·
          refine ⟨2620587888480277913516765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747058592320185275677843 2620587888480277913516765)
          ·
            refine ⟨982720458180104217568787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2620587888480277913516765 982720458180104217568787)
            ·
              refine ⟨1474080687270156326353181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982720458180104217568787 1474080687270156326353181)
              ·
                refine ⟨552780257726308622382443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474080687270156326353181 552780257726308622382443)
                ·
                  refine ⟨829170386589462933573665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552780257726308622382443 829170386589462933573665)
                  ·
                    refine ⟨621877789942097200180249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 829170386589462933573665 621877789942097200180249)
                    ·
                      refine ⟨466408342456572900135187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 621877789942097200180249 466408342456572900135187)
                      ·
                        rfl

theorem cell23_908327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_908327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908327 prefixEnd_908327 := by exact prefixLift 908327
  have htrace : WordTrace (prefixWord ++ tailWord_908327) baseStart_908327 baseEnd_908327 := by
    simpa [prefixWord, tailWord_908327, baseEnd_908327] using wordTrace_append hprefix tailTrace_908327
  have hstable : (prefixWord ++ tailWord_908327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908327).length < 2 ^ (prefixWord ++ tailWord_908327).sum := by decide
  have hdescent : baseEnd_908327 < baseStart_908327 := by decide
  rcases family_descends (prefixWord ++ tailWord_908327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908352 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3]
def baseStart_908352 : Nat := 118140960795 + 908352 * 2 ^ 59
def prefixEnd_908352 : Nat := 4983230072969 + 3 ^ 40 * 908352 * 2
def baseEnd_908352 : Nat := 466421179472935302322571

theorem tailTrace_908352 : CollatzResearch.WordTrace tailWord_908352 prefixEnd_908352 466421179472935302322571 := by
  unfold tailWord_908352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565159602601656507923655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22086879470135542010564873 16565159602601656507923655)
  ·
    refine ⟨24847739403902484761885483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16565159602601656507923655 24847739403902484761885483)
    ·
      refine ⟨37271609105853727142828225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24847739403902484761885483 37271609105853727142828225)
      ·
        refine ⟨27953706829390295357121169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37271609105853727142828225 27953706829390295357121169)
        ·
          refine ⟨20965280122042721517840877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27953706829390295357121169 20965280122042721517840877)
          ·
            refine ⟨7861980045766020569190329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20965280122042721517840877 7861980045766020569190329)
            ·
              refine ⟨5896485034324515426892747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7861980045766020569190329 5896485034324515426892747)
              ·
                refine ⟨8844727551486773140339121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896485034324515426892747 8844727551486773140339121)
                ·
                  refine ⟨6633545663615079855254341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8844727551486773140339121 6633545663615079855254341)
                  ·
                    refine ⟨1243789811927827472860189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6633545663615079855254341 1243789811927827472860189)
                    ·
                      refine ⟨466421179472935302322571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1243789811927827472860189 466421179472935302322571)
                      ·
                        rfl

theorem cell23_908352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_908352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908352 prefixEnd_908352 := by exact prefixLift 908352
  have htrace : WordTrace (prefixWord ++ tailWord_908352) baseStart_908352 baseEnd_908352 := by
    simpa [prefixWord, tailWord_908352, baseEnd_908352] using wordTrace_append hprefix tailTrace_908352
  have hstable : (prefixWord ++ tailWord_908352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908352).length < 2 ^ (prefixWord ++ tailWord_908352).sum := by decide
  have hdescent : baseEnd_908352 < baseStart_908352 := by decide
  rcases family_descends (prefixWord ++ tailWord_908352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908362 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_908362 : Nat := 118140960795 + 908362 * 2 ^ 59
def prefixEnd_908362 : Nat := 4983230072969 + 3 ^ 40 * 908362 * 2
def baseEnd_908362 : Nat := 466426314279480263197525

theorem tailTrace_908362 : CollatzResearch.WordTrace tailWord_908362 prefixEnd_908362 466426314279480263197525 := by
  unfold tailWord_908362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282670983791771180927835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22087122623444723149140893 8282670983791771180927835)
  ·
    refine ⟨12424006475687656771391753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8282670983791771180927835 12424006475687656771391753)
    ·
      refine ⟨9318004856765742578543815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12424006475687656771391753 9318004856765742578543815)
      ·
        refine ⟨13977007285148613867815723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318004856765742578543815 13977007285148613867815723)
        ·
          refine ⟨20965510927722920801723585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13977007285148613867815723 20965510927722920801723585)
          ·
            refine ⟨15724133195792190601292689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20965510927722920801723585 15724133195792190601292689)
            ·
              refine ⟨11793099896844142950969517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15724133195792190601292689 11793099896844142950969517)
              ·
                refine ⟨4422412461316553606613569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11793099896844142950969517 4422412461316553606613569)
                ·
                  refine ⟨3316809345987415204960177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422412461316553606613569 3316809345987415204960177)
                  ·
                    refine ⟨2487607009490561403720133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3316809345987415204960177 2487607009490561403720133)
                    ·
                      refine ⟨466426314279480263197525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2487607009490561403720133 466426314279480263197525)
                      ·
                        rfl

theorem cell23_908362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_908362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908362 prefixEnd_908362 := by exact prefixLift 908362
  have htrace : WordTrace (prefixWord ++ tailWord_908362) baseStart_908362 baseEnd_908362 := by
    simpa [prefixWord, tailWord_908362, baseEnd_908362] using wordTrace_append hprefix tailTrace_908362
  have hstable : (prefixWord ++ tailWord_908362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908362).length < 2 ^ (prefixWord ++ tailWord_908362).sum := by decide
  have hdescent : baseEnd_908362 < baseStart_908362 := by decide
  rcases family_descends (prefixWord ++ tailWord_908362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908372 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 7]
def baseStart_908372 : Nat := 118140960795 + 908372 * 2 ^ 59
def prefixEnd_908372 : Nat := 4983230072969 + 3 ^ 40 * 908372 * 2
def baseEnd_908372 : Nat := 51825716565113913785831

theorem tailTrace_908372 : CollatzResearch.WordTrace tailWord_908372 prefixEnd_908372 51825716565113913785831 := by
  unfold tailWord_908372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565524332565428215787685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22087365776753904287716913 16565524332565428215787685)
  ·
    refine ⟨3106035812356017790460191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16565524332565428215787685 3106035812356017790460191)
    ·
      refine ⟨4659053718534026685690287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106035812356017790460191 4659053718534026685690287)
      ·
        refine ⟨6988580577801040028535431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4659053718534026685690287 6988580577801040028535431)
        ·
          refine ⟨10482870866701560042803147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988580577801040028535431 10482870866701560042803147)
          ·
            refine ⟨15724306300052340064204721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482870866701560042803147 15724306300052340064204721)
            ·
              refine ⟨11793229725039255048153541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15724306300052340064204721 11793229725039255048153541)
              ·
                refine ⟨2211230573444860321528789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11793229725039255048153541 2211230573444860321528789)
                ·
                  refine ⟨51825716565113913785831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2211230573444860321528789 51825716565113913785831)
                  ·
                    rfl

theorem cell23_908372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_908372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908372 prefixEnd_908372 := by exact prefixLift 908372
  have htrace : WordTrace (prefixWord ++ tailWord_908372) baseStart_908372 baseEnd_908372 := by
    simpa [prefixWord, tailWord_908372, baseEnd_908372] using wordTrace_append hprefix tailTrace_908372
  have hstable : (prefixWord ++ tailWord_908372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908372).length < 2 ^ (prefixWord ++ tailWord_908372).sum := by decide
  have hdescent : baseEnd_908372 < baseStart_908372 := by decide
  rcases family_descends (prefixWord ++ tailWord_908372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908389 : List Nat := [1, 3, 1, 3, 2, 1, 2, 5, 5]
def baseStart_908389 : Nat := 118140960795 + 908389 * 2 ^ 59
def prefixEnd_908389 : Nat := 4983230072969 + 3 ^ 40 * 908389 * 2
def baseEnd_908389 : Nat := 51826686473016850839989

theorem tailTrace_908389 : CollatzResearch.WordTrace tailWord_908389 prefixEnd_908389 51826686473016850839989 := by
  unfold tailWord_908389
  simp only [CollatzResearch.WordTrace]
  refine ⟨33131668706069268334944221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22087779137379512223296147 33131668706069268334944221)
  ·
    refine ⟨12424375764775975625604083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33131668706069268334944221 12424375764775975625604083)
    ·
      refine ⟨18636563647163963438406125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12424375764775975625604083 18636563647163963438406125)
      ·
        refine ⟨6988711367686486289402297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18636563647163963438406125 6988711367686486289402297)
        ·
          refine ⟨5241533525764864717051723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6988711367686486289402297 5241533525764864717051723)
          ·
            refine ⟨7862300288647297075577585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241533525764864717051723 7862300288647297075577585)
            ·
              refine ⟨5896725216485472806683189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7862300288647297075577585 5896725216485472806683189)
              ·
                refine ⟨552817989045513075626549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5896725216485472806683189 552817989045513075626549)
                ·
                  refine ⟨51826686473016850839989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 552817989045513075626549 51826686473016850839989)
                  ·
                    rfl

theorem cell23_908389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_908389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908389 prefixEnd_908389 := by exact prefixLift 908389
  have htrace : WordTrace (prefixWord ++ tailWord_908389) baseStart_908389 baseEnd_908389 := by
    simpa [prefixWord, tailWord_908389, baseEnd_908389] using wordTrace_append hprefix tailTrace_908389
  have hstable : (prefixWord ++ tailWord_908389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908389).length < 2 ^ (prefixWord ++ tailWord_908389).sum := by decide
  have hdescent : baseEnd_908389 < baseStart_908389 := by decide
  rcases family_descends (prefixWord ++ tailWord_908389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908406 : List Nat := [5, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_908406 : Nat := 118140960795 + 908406 * 2 ^ 59
def prefixEnd_908406 : Nat := 4983230072969 + 3 ^ 40 * 908406 * 2
def baseEnd_908406 : Nat := 51827656380919787894147

theorem tailTrace_908406 : CollatzResearch.WordTrace tailWord_908406 prefixEnd_908406 51827656380919787894147 := by
  unfold tailWord_908406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070768046687980014894567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22088192498005120158875381 2070768046687980014894567)
  ·
    refine ⟨3106152070031970022341851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2070768046687980014894567 3106152070031970022341851)
    ·
      refine ⟨4659228105047955033512777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106152070031970022341851 4659228105047955033512777)
      ·
        refine ⟨3494421078785966275134583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4659228105047955033512777 3494421078785966275134583)
        ·
          refine ⟨5241631618178949412701875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494421078785966275134583 5241631618178949412701875)
          ·
            refine ⟨7862447427268424119052813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241631618178949412701875 7862447427268424119052813)
            ·
              refine ⟨2948417785225659044644805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7862447427268424119052813 2948417785225659044644805)
              ·
                refine ⟨552828334729811070870901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2948417785225659044644805 552828334729811070870901)
                ·
                  refine ⟨51827656380919787894147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 552828334729811070870901 51827656380919787894147)
                  ·
                    rfl

theorem cell23_908406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_908406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908406 prefixEnd_908406 := by exact prefixLift 908406
  have htrace : WordTrace (prefixWord ++ tailWord_908406) baseStart_908406 baseEnd_908406 := by
    simpa [prefixWord, tailWord_908406, baseEnd_908406] using wordTrace_append hprefix tailTrace_908406
  have hstable : (prefixWord ++ tailWord_908406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908406).length < 2 ^ (prefixWord ++ tailWord_908406).sum := by decide
  have hdescent : baseEnd_908406 < baseStart_908406 := by decide
  rcases family_descends (prefixWord ++ tailWord_908406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908412 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_908412 : Nat := 118140960795 + 908412 * 2 ^ 59
def prefixEnd_908412 : Nat := 4983230072969 + 3 ^ 40 * 908412 * 2
def baseEnd_908412 : Nat := 466451988312205067572295

theorem tailTrace_908412 : CollatzResearch.WordTrace tailWord_908412 prefixEnd_908412 466451988312205067572295 := by
  unfold tailWord_908412
  simp only [CollatzResearch.WordTrace]
  refine ⟨16566253792492971631515745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22088338389990628842020993 16566253792492971631515745)
  ·
    refine ⟨12424690344369728723636809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16566253792492971631515745 12424690344369728723636809)
    ·
      refine ⟨9318517758277296542727607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12424690344369728723636809 9318517758277296542727607)
      ·
        refine ⟨13977776637415944814091411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318517758277296542727607 13977776637415944814091411)
        ·
          refine ⟨20966664956123917221137117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13977776637415944814091411 20966664956123917221137117)
          ·
            refine ⟨7862499358546468957926419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20966664956123917221137117 7862499358546468957926419)
            ·
              refine ⟨11793749037819703436889629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862499358546468957926419 11793749037819703436889629)
              ·
                refine ⟨4422655889182388788833611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11793749037819703436889629 4422655889182388788833611)
                ·
                  refine ⟨6633983833773583183250417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422655889182388788833611 6633983833773583183250417)
                  ·
                    refine ⟨4975487875330187387437813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633983833773583183250417 4975487875330187387437813)
                    ·
                      refine ⟨466451988312205067572295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4975487875330187387437813 466451988312205067572295)
                      ·
                        rfl

theorem cell23_908412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_908412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908412 prefixEnd_908412 := by exact prefixLift 908412
  have htrace : WordTrace (prefixWord ++ tailWord_908412) baseStart_908412 baseEnd_908412 := by
    simpa [prefixWord, tailWord_908412, baseEnd_908412] using wordTrace_append hprefix tailTrace_908412
  have hstable : (prefixWord ++ tailWord_908412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908412).length < 2 ^ (prefixWord ++ tailWord_908412).sum := by decide
  have hdescent : baseEnd_908412 < baseStart_908412 := by decide
  rcases family_descends (prefixWord ++ tailWord_908412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908439 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_908439 : Nat := 118140960795 + 908439 * 2 ^ 59
def prefixEnd_908439 : Nat := 4983230072969 + 3 ^ 40 * 908439 * 2
def baseEnd_908439 : Nat := 466465852289876461934671

theorem tailTrace_908439 : CollatzResearch.WordTrace tailWord_908439 prefixEnd_908439 466465852289876461934671 := by
  unfold tailWord_908439
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133492355888126874264371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22088994903925417916176247 33133492355888126874264371)
  ·
    refine ⟨49700238533832190311396557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33133492355888126874264371 49700238533832190311396557)
    ·
      refine ⟨18637589450187071366773709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49700238533832190311396557 18637589450187071366773709)
      ·
        refine ⟨6989096043820151762540141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18637589450187071366773709 6989096043820151762540141)
        ·
          refine ⟨2620911016432556910952553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6989096043820151762540141 2620911016432556910952553)
          ·
            refine ⟨1965683262324417683214415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620911016432556910952553 1965683262324417683214415)
            ·
              refine ⟨2948524893486626524821623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965683262324417683214415 2948524893486626524821623)
              ·
                refine ⟨4422787340229939787232435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948524893486626524821623 4422787340229939787232435)
                ·
                  refine ⟨6634181010344909680848653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422787340229939787232435 6634181010344909680848653)
                  ·
                    refine ⟨2487817878879341130318245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6634181010344909680848653 2487817878879341130318245)
                    ·
                      refine ⟨466465852289876461934671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2487817878879341130318245 466465852289876461934671)
                      ·
                        rfl

theorem cell23_908439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_908439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908439 prefixEnd_908439 := by exact prefixLift 908439
  have htrace : WordTrace (prefixWord ++ tailWord_908439) baseStart_908439 baseEnd_908439 := by
    simpa [prefixWord, tailWord_908439, baseEnd_908439] using wordTrace_append hprefix tailTrace_908439
  have hstable : (prefixWord ++ tailWord_908439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908439).length < 2 ^ (prefixWord ++ tailWord_908439).sum := by decide
  have hdescent : baseEnd_908439 < baseStart_908439 := by decide
  rcases family_descends (prefixWord ++ tailWord_908439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908449 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 5, 4]
def baseStart_908449 : Nat := 118140960795 + 908449 * 2 ^ 59
def prefixEnd_908449 : Nat := 4983230072969 + 3 ^ 40 * 908449 * 2
def baseEnd_908449 : Nat := 155490329032140474269875

theorem tailTrace_908449 : CollatzResearch.WordTrace tailWord_908449 prefixEnd_908449 155490329032140474269875 := by
  unfold tailWord_908449
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133857085851898582128401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22089238057234599054752267 33133857085851898582128401)
  ·
    refine ⟨24850392814388923936596301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33133857085851898582128401 24850392814388923936596301)
    ·
      refine ⟨9318897305395846476223613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24850392814388923936596301 9318897305395846476223613)
      ·
        refine ⟨3494586489523442428583855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9318897305395846476223613 3494586489523442428583855)
        ·
          refine ⟨5241879734285163642875783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494586489523442428583855 5241879734285163642875783)
          ·
            refine ⟨7862819601427745464313675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241879734285163642875783 7862819601427745464313675)
            ·
              refine ⟨11794229402141618196470513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862819601427745464313675 11794229402141618196470513)
              ·
                refine ⟨8845672051606213647352885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11794229402141618196470513 8845672051606213647352885)
                ·
                  refine ⟨829281754838082529439333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8845672051606213647352885 829281754838082529439333)
                  ·
                    refine ⟨155490329032140474269875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 829281754838082529439333 155490329032140474269875)
                    ·
                      rfl

theorem cell23_908449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_908449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908449 prefixEnd_908449 := by exact prefixLift 908449
  have htrace : WordTrace (prefixWord ++ tailWord_908449) baseStart_908449 baseEnd_908449 := by
    simpa [prefixWord, tailWord_908449, baseEnd_908449] using wordTrace_append hprefix tailTrace_908449
  have hstable : (prefixWord ++ tailWord_908449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908449).length < 2 ^ (prefixWord ++ tailWord_908449).sum := by decide
  have hdescent : baseEnd_908449 < baseStart_908449 := by decide
  rcases family_descends (prefixWord ++ tailWord_908449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908466 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_908466 : Nat := 118140960795 + 908466 * 2 ^ 59
def prefixEnd_908466 : Nat := 4983230072969 + 3 ^ 40 * 908466 * 2
def baseEnd_908466 : Nat := 155493238755849285432349

theorem tailTrace_908466 : CollatzResearch.WordTrace tailWord_908466 prefixEnd_908466 155493238755849285432349 := by
  unfold tailWord_908466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8283619281697577621374313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22089651417860206990331501 8283619281697577621374313)
  ·
    refine ⟨6212714461273183216030735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8283619281697577621374313 6212714461273183216030735)
    ·
      refine ⟨9319071691909774824046103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6212714461273183216030735 9319071691909774824046103)
      ·
        refine ⟨13978607537864662236069155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9319071691909774824046103 13978607537864662236069155)
        ·
          refine ⟨20967911306796993354103733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978607537864662236069155 20967911306796993354103733)
          ·
            refine ⟨1965741685012218126947225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20967911306796993354103733 1965741685012218126947225)
            ·
              refine ⟨1474306263759163595210419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965741685012218126947225 1474306263759163595210419)
              ·
                refine ⟨2211459395638745392815629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474306263759163595210419 2211459395638745392815629)
                ·
                  refine ⟨829297273364529522305861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2211459395638745392815629 829297273364529522305861)
                  ·
                    refine ⟨155493238755849285432349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 829297273364529522305861 155493238755849285432349)
                    ·
                      rfl

theorem cell23_908466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_908466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908466 prefixEnd_908466 := by exact prefixLift 908466
  have htrace : WordTrace (prefixWord ++ tailWord_908466) baseStart_908466 baseEnd_908466 := by
    simpa [prefixWord, tailWord_908466, baseEnd_908466] using wordTrace_append hprefix tailTrace_908466
  have hstable : (prefixWord ++ tailWord_908466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908466).length < 2 ^ (prefixWord ++ tailWord_908466).sum := by decide
  have hdescent : baseEnd_908466 < baseStart_908466 := by decide
  rcases family_descends (prefixWord ++ tailWord_908466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908516 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_908516 : Nat := 118140960795 + 908516 * 2 ^ 59
def prefixEnd_908516 : Nat := 4983230072969 + 3 ^ 40 * 908516 * 2
def baseEnd_908516 : Nat := 466505390300272660671817

theorem tailTrace_908516 : CollatzResearch.WordTrace tailWord_908516 prefixEnd_908516 466505390300272660671817 := by
  unfold tailWord_908516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16568150388304584512408701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22090867184406112683211601 16568150388304584512408701)
  ·
    refine ⟨6213056395614219192153263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16568150388304584512408701 6213056395614219192153263)
    ·
      refine ⟨9319584593421328788229895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6213056395614219192153263 9319584593421328788229895)
      ·
        refine ⟨13979376890131993182344843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9319584593421328788229895 13979376890131993182344843)
        ·
          refine ⟨20969065335197989773517265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13979376890131993182344843 20969065335197989773517265)
          ·
            refine ⟨15726799001398492330137949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20969065335197989773517265 15726799001398492330137949)
            ·
              refine ⟨5897549625524434623801731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15726799001398492330137949 5897549625524434623801731)
              ·
                refine ⟨8846324438286651935702597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897549625524434623801731 8846324438286651935702597)
                ·
                  refine ⟨1658685832178747237944237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8846324438286651935702597 1658685832178747237944237)
                  ·
                    refine ⟨622007187067030214229089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1658685832178747237944237 622007187067030214229089)
                    ·
                      refine ⟨466505390300272660671817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622007187067030214229089 466505390300272660671817)
                      ·
                        rfl

theorem cell23_908516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_908516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908516 prefixEnd_908516 := by exact prefixLift 908516
  have htrace : WordTrace (prefixWord ++ tailWord_908516) baseStart_908516 baseEnd_908516 := by
    simpa [prefixWord, tailWord_908516, baseEnd_908516] using wordTrace_append hprefix tailTrace_908516
  have hstable : (prefixWord ++ tailWord_908516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908516).length < 2 ^ (prefixWord ++ tailWord_908516).sum := by decide
  have hdescent : baseEnd_908516 < baseStart_908516 := by decide
  rcases family_descends (prefixWord ++ tailWord_908516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908523 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 3]
def baseStart_908523 : Nat := 118140960795 + 908523 * 2 ^ 59
def prefixEnd_908523 : Nat := 4983230072969 + 3 ^ 40 * 908523 * 2
def baseEnd_908523 : Nat := 466508984664854133284285

theorem tailTrace_908523 : CollatzResearch.WordTrace tailWord_908523 prefixEnd_908523 466508984664854133284285 := by
  unfold tailWord_908523
  simp only [CollatzResearch.WordTrace]
  refine ⟨33136556087583809220322223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22091037391722539480214815 33136556087583809220322223)
  ·
    refine ⟨49704834131375713830483335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33136556087583809220322223 49704834131375713830483335)
    ·
      refine ⟨74557251197063570745725003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49704834131375713830483335 74557251197063570745725003)
      ·
        refine ⟨111835876795595356118587505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74557251197063570745725003 111835876795595356118587505)
        ·
          refine ⟨83876907596696517088940629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111835876795595356118587505 83876907596696517088940629)
          ·
            refine ⟨982932510898787309636023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 83876907596696517088940629 982932510898787309636023)
            ·
              refine ⟨1474398766348180964454035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982932510898787309636023 1474398766348180964454035)
              ·
                refine ⟨2211598149522271446681053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474398766348180964454035 2211598149522271446681053)
                ·
                  refine ⟨829349306070851792505395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2211598149522271446681053 829349306070851792505395)
                  ·
                    refine ⟨1244023959106277688758093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829349306070851792505395 1244023959106277688758093)
                    ·
                      refine ⟨466508984664854133284285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244023959106277688758093 466508984664854133284285)
                      ·
                        rfl

theorem cell23_908523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 3].length) (baseStart_908523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908523 prefixEnd_908523 := by exact prefixLift 908523
  have htrace : WordTrace (prefixWord ++ tailWord_908523) baseStart_908523 baseEnd_908523 := by
    simpa [prefixWord, tailWord_908523, baseEnd_908523] using wordTrace_append hprefix tailTrace_908523
  have hstable : (prefixWord ++ tailWord_908523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908523).length < 2 ^ (prefixWord ++ tailWord_908523).sum := by decide
  have hdescent : baseEnd_908523 < baseStart_908523 := by decide
  rcases family_descends (prefixWord ++ tailWord_908523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908529 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_908529 : Nat := 118140960795 + 908529 * 2 ^ 59
def prefixEnd_908529 : Nat := 4983230072969 + 3 ^ 40 * 908529 * 2
def baseEnd_908529 : Nat := 466512065548781109809257

theorem tailTrace_908529 : CollatzResearch.WordTrace tailWord_908529 prefixEnd_908529 466512065548781109809257 := by
  unfold tailWord_908529
  simp only [CollatzResearch.WordTrace]
  refine ⟨33136774925562072245040641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22091183283708048163360427 33136774925562072245040641)
  ·
    refine ⟨24852581194171554183780481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33136774925562072245040641 24852581194171554183780481)
    ·
      refine ⟨18639435895628665637835361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24852581194171554183780481 18639435895628665637835361)
      ·
        refine ⟨13979576921721499228376521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18639435895628665637835361 13979576921721499228376521)
        ·
          refine ⟨10484682691291124421282391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13979576921721499228376521 10484682691291124421282391)
          ·
            refine ⟨15727024036936686631923587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484682691291124421282391 15727024036936686631923587)
            ·
              refine ⟨23590536055405029947885381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15727024036936686631923587 23590536055405029947885381)
              ·
                refine ⟨4423225510388443115228509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23590536055405029947885381 4423225510388443115228509)
                ·
                  refine ⟨1658709566395666168210691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4423225510388443115228509 1658709566395666168210691)
                  ·
                    refine ⟨2488064349593499252316037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1658709566395666168210691 2488064349593499252316037)
                    ·
                      refine ⟨466512065548781109809257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2488064349593499252316037 466512065548781109809257)
                      ·
                        rfl

theorem cell23_908529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_908529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908529 prefixEnd_908529 := by exact prefixLift 908529
  have htrace : WordTrace (prefixWord ++ tailWord_908529) baseStart_908529 baseEnd_908529 := by
    simpa [prefixWord, tailWord_908529, baseEnd_908529] using wordTrace_append hprefix tailTrace_908529
  have hstable : (prefixWord ++ tailWord_908529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908529).length < 2 ^ (prefixWord ++ tailWord_908529).sum := by decide
  have hdescent : baseEnd_908529 < baseStart_908529 := by decide
  rcases family_descends (prefixWord ++ tailWord_908529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908530 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 6]
def baseStart_908530 : Nat := 118140960795 + 908530 * 2 ^ 59
def prefixEnd_908530 : Nat := 4983230072969 + 3 ^ 40 * 908530 * 2
def baseEnd_908530 : Nat := 51834731003270622877417

theorem tailTrace_908530 : CollatzResearch.WordTrace tailWord_908530 prefixEnd_908530 51834731003270622877417 := by
  unfold tailWord_908530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8284202849639612353956761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22091207599038966277218029 8284202849639612353956761)
  ·
    refine ⟨6213152137229709265467571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8284202849639612353956761 6213152137229709265467571)
    ·
      refine ⟨9319728205844563898201357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6213152137229709265467571 9319728205844563898201357)
      ·
        refine ⟨3494898077191711461825509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9319728205844563898201357 3494898077191711461825509)
        ·
          refine ⟨655293389473445899092283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3494898077191711461825509 655293389473445899092283)
          ·
            refine ⟨982940084210168848638425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655293389473445899092283 982940084210168848638425)
            ·
              refine ⟨737205063157626636478819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982940084210168848638425 737205063157626636478819)
              ·
                refine ⟨1105807594736439954718229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737205063157626636478819 1105807594736439954718229)
                ·
                  refine ⟨51834731003270622877417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1105807594736439954718229 51834731003270622877417)
                  ·
                    rfl

theorem cell23_908530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_908530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908530 prefixEnd_908530 := by exact prefixLift 908530
  have htrace : WordTrace (prefixWord ++ tailWord_908530) baseStart_908530 baseEnd_908530 := by
    simpa [prefixWord, tailWord_908530, baseEnd_908530] using wordTrace_append hprefix tailTrace_908530
  have hstable : (prefixWord ++ tailWord_908530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908530).length < 2 ^ (prefixWord ++ tailWord_908530).sum := by decide
  have hdescent : baseEnd_908530 < baseStart_908530 := by decide
  rcases family_descends (prefixWord ++ tailWord_908530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908573 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_908573 : Nat := 118140960795 + 908573 * 2 ^ 59
def prefixEnd_908573 : Nat := 4983230072969 + 3 ^ 40 * 908573 * 2
def baseEnd_908573 : Nat := 155511552899192979219685

theorem tailTrace_908573 : CollatzResearch.WordTrace tailWord_908573 prefixEnd_908573 155511552899192979219685 := by
  unfold tailWord_908573
  simp only [CollatzResearch.WordTrace]
  refine ⟨33138379737402667759642373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22092253158268445173094915 33138379737402667759642373)
  ·
    refine ⟨6213446200763000204932945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33138379737402667759642373 6213446200763000204932945)
    ·
      refine ⟨4660084650572250153699709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6213446200763000204932945 4660084650572250153699709)
      ·
        refine ⟨1747531743964593807637391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4660084650572250153699709 1747531743964593807637391)
        ·
          refine ⟨2621297615946890711456087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747531743964593807637391 2621297615946890711456087)
          ·
            refine ⟨3931946423920336067184131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621297615946890711456087 3931946423920336067184131)
            ·
              refine ⟨5897919635880504100776197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931946423920336067184131 5897919635880504100776197)
              ·
                refine ⟨1105859931727594518895537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5897919635880504100776197 1105859931727594518895537)
                ·
                  refine ⟨829394948795695889171653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1105859931727594518895537 829394948795695889171653)
                  ·
                    refine ⟨155511552899192979219685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 829394948795695889171653 155511552899192979219685)
                    ·
                      rfl

theorem cell23_908573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_908573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908573 prefixEnd_908573 := by exact prefixLift 908573
  have htrace : WordTrace (prefixWord ++ tailWord_908573) baseStart_908573 baseEnd_908573 := by
    simpa [prefixWord, tailWord_908573, baseEnd_908573] using wordTrace_append hprefix tailTrace_908573
  have hstable : (prefixWord ++ tailWord_908573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908573).length < 2 ^ (prefixWord ++ tailWord_908573).sum := by decide
  have hdescent : baseEnd_908573 < baseStart_908573 := by decide
  rcases family_descends (prefixWord ++ tailWord_908573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908574 : List Nat := [4, 3, 2, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_908574 : Nat := 118140960795 + 908574 * 2 ^ 59
def prefixEnd_908574 : Nat := 4983230072969 + 3 ^ 40 * 908574 * 2
def baseEnd_908574 : Nat := 466535172178233433746551

theorem tailTrace_908574 : CollatzResearch.WordTrace tailWord_908574 prefixEnd_908574 466535172178233433746551 := by
  unfold tailWord_908574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142302026299880616303597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22092277473599363286952517 4142302026299880616303597)
  ·
    refine ⟨1553363259862455231113849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4142302026299880616303597 1553363259862455231113849)
    ·
      refine ⟨1165022444896841423335387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1553363259862455231113849 1165022444896841423335387)
      ·
        refine ⟨1747533667345262135003081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165022444896841423335387 1747533667345262135003081)
        ·
          refine ⟨1310650250508946601252311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1747533667345262135003081 1310650250508946601252311)
          ·
            refine ⟨1965975375763419901878467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310650250508946601252311 1965975375763419901878467)
            ·
              refine ⟨2948963063645129852817701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965975375763419901878467 2948963063645129852817701)
              ·
                refine ⟨552930574433461847403319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2948963063645129852817701 552930574433461847403319)
                ·
                  refine ⟨829395861650192771104979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552930574433461847403319 829395861650192771104979)
                  ·
                    refine ⟨1244093792475289156657469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829395861650192771104979 1244093792475289156657469)
                    ·
                      refine ⟨466535172178233433746551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244093792475289156657469 466535172178233433746551)
                      ·
                        rfl

theorem cell23_908574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_908574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908574 prefixEnd_908574 := by exact prefixLift 908574
  have htrace : WordTrace (prefixWord ++ tailWord_908574) baseStart_908574 baseEnd_908574 := by
    simpa [prefixWord, tailWord_908574, baseEnd_908574] using wordTrace_append hprefix tailTrace_908574
  have hstable : (prefixWord ++ tailWord_908574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908574).length < 2 ^ (prefixWord ++ tailWord_908574).sum := by decide
  have hdescent : baseEnd_908574 < baseStart_908574 := by decide
  rcases family_descends (prefixWord ++ tailWord_908574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908586 : List Nat := [3, 1, 4, 2, 1, 1, 3, 8]
def baseStart_908586 : Nat := 118140960795 + 908586 * 2 ^ 59
def prefixEnd_908586 : Nat := 4983230072969 + 3 ^ 40 * 908586 * 2
def baseEnd_908586 : Nat := 17279308664669903214685

theorem tailTrace_908586 : CollatzResearch.WordTrace tailWord_908586 prefixEnd_908586 17279308664669903214685 := by
  unfold tailWord_908586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8284713471588892744966403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22092569257570380653243741 8284713471588892744966403)
  ·
    refine ⟨12427070207383339117449605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8284713471588892744966403 12427070207383339117449605)
    ·
      refine ⟨2330075663884376084521801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12427070207383339117449605 2330075663884376084521801)
      ·
        refine ⟨1747556747913282063391351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330075663884376084521801 1747556747913282063391351)
        ·
          refine ⟨2621335121869923095087027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747556747913282063391351 2621335121869923095087027)
          ·
            refine ⟨3932002682804884642630541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621335121869923095087027 3932002682804884642630541)
            ·
              refine ⟨1474501006051831740986453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3932002682804884642630541 1474501006051831740986453)
              ·
                refine ⟨17279308664669903214685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1474501006051831740986453 17279308664669903214685)
                ·
                  rfl

theorem cell23_908586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_908586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908586 prefixEnd_908586 := by exact prefixLift 908586
  have htrace : WordTrace (prefixWord ++ tailWord_908586) baseStart_908586 baseEnd_908586 := by
    simpa [prefixWord, tailWord_908586, baseEnd_908586] using wordTrace_append hprefix tailTrace_908586
  have hstable : (prefixWord ++ tailWord_908586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908586).length < 2 ^ (prefixWord ++ tailWord_908586).sum := by decide
  have hdescent : baseEnd_908586 < baseStart_908586 := by decide
  rcases family_descends (prefixWord ++ tailWord_908586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908639 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_908639 : Nat := 118140960795 + 908639 * 2 ^ 59
def prefixEnd_908639 : Nat := 4983230072969 + 3 ^ 40 * 908639 * 2
def baseEnd_908639 : Nat := 466568548420775679433751

theorem tailTrace_908639 : CollatzResearch.WordTrace tailWord_908639 prefixEnd_908639 466568548420775679433751 := by
  unfold tailWord_908639
  simp only [CollatzResearch.WordTrace]
  refine ⟨33140786955163561031544971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22093857970109040687696647 33140786955163561031544971)
  ·
    refine ⟨49711180432745341547317457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33140786955163561031544971 49711180432745341547317457)
    ·
      refine ⟨37283385324559006160488093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49711180432745341547317457 37283385324559006160488093)
      ·
        refine ⟨13981269496709627310183035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37283385324559006160488093 13981269496709627310183035)
        ·
          refine ⟨20971904245064440965274553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13981269496709627310183035 20971904245064440965274553)
          ·
            refine ⟨15728928183798330723955915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20971904245064440965274553 15728928183798330723955915)
            ·
              refine ⟨23593392275697496085933873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15728928183798330723955915 23593392275697496085933873)
              ·
                refine ⟨17695044206773122064450405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23593392275697496085933873 17695044206773122064450405)
                ·
                  refine ⟨3317820788769960387084451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17695044206773122064450405 3317820788769960387084451)
                  ·
                    refine ⟨4976731183154940580626677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3317820788769960387084451 4976731183154940580626677)
                    ·
                      refine ⟨466568548420775679433751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4976731183154940580626677 466568548420775679433751)
                      ·
                        rfl

theorem cell23_908639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_908639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908639 prefixEnd_908639 := by exact prefixLift 908639
  have htrace : WordTrace (prefixWord ++ tailWord_908639) baseStart_908639 baseEnd_908639 := by
    simpa [prefixWord, tailWord_908639, baseEnd_908639] using wordTrace_append hprefix tailTrace_908639
  have hstable : (prefixWord ++ tailWord_908639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908639).length < 2 ^ (prefixWord ++ tailWord_908639).sum := by decide
  have hdescent : baseEnd_908639 < baseStart_908639 := by decide
  rcases family_descends (prefixWord ++ tailWord_908639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908647 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_908647 : Nat := 118140960795 + 908647 * 2 ^ 59
def prefixEnd_908647 : Nat := 4983230072969 + 3 ^ 40 * 908647 * 2
def baseEnd_908647 : Nat := 466572656266011648133715

theorem tailTrace_908647 : CollatzResearch.WordTrace tailWord_908647 prefixEnd_908647 466572656266011648133715 := by
  unfold tailWord_908647
  simp only [CollatzResearch.WordTrace]
  refine ⟨33141078739134578397836195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22094052492756385598557463 33141078739134578397836195)
  ·
    refine ⟨49711618108701867596754293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33141078739134578397836195 49711618108701867596754293)
    ·
      refine ⟨4660464197690800087195715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49711618108701867596754293 4660464197690800087195715)
      ·
        refine ⟨6990696296536200130793573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660464197690800087195715 6990696296536200130793573)
        ·
          refine ⟨1310755555600537524523795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6990696296536200130793573 1310755555600537524523795)
          ·
            refine ⟨1966133333400806286785693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310755555600537524523795 1966133333400806286785693)
            ·
              refine ⟨737300000025302357544635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1966133333400806286785693 737300000025302357544635)
              ·
                refine ⟨1105950000037953536316953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737300000025302357544635 1105950000037953536316953)
                ·
                  refine ⟨829462500028465152237715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1105950000037953536316953 829462500028465152237715)
                  ·
                    refine ⟨1244193750042697728356573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829462500028465152237715 1244193750042697728356573)
                    ·
                      refine ⟨466572656266011648133715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244193750042697728356573 466572656266011648133715)
                      ·
                        rfl

theorem cell23_908647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_908647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908647 prefixEnd_908647 := by exact prefixLift 908647
  have htrace : WordTrace (prefixWord ++ tailWord_908647) baseStart_908647 baseEnd_908647 := by
    simpa [prefixWord, tailWord_908647, baseEnd_908647] using wordTrace_append hprefix tailTrace_908647
  have hstable : (prefixWord ++ tailWord_908647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908647).length < 2 ^ (prefixWord ++ tailWord_908647).sum := by decide
  have hdescent : baseEnd_908647 < baseStart_908647 := by decide
  rcases family_descends (prefixWord ++ tailWord_908647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908649 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_908649 : Nat := 118140960795 + 908649 * 2 ^ 59
def prefixEnd_908649 : Nat := 4983230072969 + 3 ^ 40 * 908649 * 2
def baseEnd_908649 : Nat := 466573683227320640308705

theorem tailTrace_908649 : CollatzResearch.WordTrace tailWord_908649 prefixEnd_908649 466573683227320640308705 := by
  unfold tailWord_908649
  simp only [CollatzResearch.WordTrace]
  refine ⟨33141151685127332739409001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22094101123418221826272667 33141151685127332739409001)
  ·
    refine ⟨24855863763845499554556751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33141151685127332739409001 24855863763845499554556751)
    ·
      refine ⟨37283795645768249331835127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24855863763845499554556751 37283795645768249331835127)
      ·
        refine ⟨55925693468652373997752691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37283795645768249331835127 55925693468652373997752691)
        ·
          refine ⟨83888540202978560996629037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55925693468652373997752691 83888540202978560996629037)
          ·
            refine ⟨31458202576116960373735889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83888540202978560996629037 31458202576116960373735889)
            ·
              refine ⟨23593651932087720280301917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31458202576116960373735889 23593651932087720280301917)
              ·
                refine ⟨8847619474532895105113219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23593651932087720280301917 8847619474532895105113219)
                ·
                  refine ⟨13271429211799342657669829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8847619474532895105113219 13271429211799342657669829)
                  ·
                    refine ⟨2488392977212376748313093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13271429211799342657669829 2488392977212376748313093)
                    ·
                      refine ⟨466573683227320640308705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2488392977212376748313093 466573683227320640308705)
                      ·
                        rfl

theorem cell23_908649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_908649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908649 prefixEnd_908649 := by exact prefixLift 908649
  have htrace : WordTrace (prefixWord ++ tailWord_908649) baseStart_908649 baseEnd_908649 := by
    simpa [prefixWord, tailWord_908649, baseEnd_908649] using wordTrace_append hprefix tailTrace_908649
  have hstable : (prefixWord ++ tailWord_908649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908649).length < 2 ^ (prefixWord ++ tailWord_908649).sum := by decide
  have hdescent : baseEnd_908649 < baseStart_908649 := by decide
  rcases family_descends (prefixWord ++ tailWord_908649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908673 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_908673 : Nat := 118140960795 + 908673 * 2 ^ 59
def prefixEnd_908673 : Nat := 4983230072969 + 3 ^ 40 * 908673 * 2
def baseEnd_908673 : Nat := 466586006763028546408595

theorem tailTrace_908673 : CollatzResearch.WordTrace tailWord_908673 prefixEnd_908673 466586006763028546408595 := by
  unfold tailWord_908673
  simp only [CollatzResearch.WordTrace]
  refine ⟨33142027037040384838282673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22094684691360256558855115 33142027037040384838282673)
  ·
    refine ⟨24856520277780288628712005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33142027037040384838282673 24856520277780288628712005)
    ·
      refine ⟨4660597552083804117883501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24856520277780288628712005 4660597552083804117883501)
      ·
        refine ⟨1747724082031426544206313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4660597552083804117883501 1747724082031426544206313)
        ·
          refine ⟨1310793061523569908154735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1747724082031426544206313 1310793061523569908154735)
          ·
            refine ⟨1966189592285354862232103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310793061523569908154735 1966189592285354862232103)
            ·
              refine ⟨2949284388428032293348155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966189592285354862232103 2949284388428032293348155)
              ·
                refine ⟨4423926582642048440022233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949284388428032293348155 4423926582642048440022233)
                ·
                  refine ⟨3317944936981536330016675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4423926582642048440022233 3317944936981536330016675)
                  ·
                    refine ⟨4976917405472304495025013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3317944936981536330016675 4976917405472304495025013)
                    ·
                      refine ⟨466586006763028546408595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4976917405472304495025013 466586006763028546408595)
                      ·
                        rfl

theorem cell23_908673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_908673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908673 prefixEnd_908673 := by exact prefixLift 908673
  have htrace : WordTrace (prefixWord ++ tailWord_908673) baseStart_908673 baseEnd_908673 := by
    simpa [prefixWord, tailWord_908673, baseEnd_908673] using wordTrace_append hprefix tailTrace_908673
  have hstable : (prefixWord ++ tailWord_908673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908673).length < 2 ^ (prefixWord ++ tailWord_908673).sum := by decide
  have hdescent : baseEnd_908673 < baseStart_908673 := by decide
  rcases family_descends (prefixWord ++ tailWord_908673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908699 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5]
def baseStart_908699 : Nat := 118140960795 + 908699 * 2 ^ 59
def prefixEnd_908699 : Nat := 4983230072969 + 3 ^ 40 * 908699 * 2
def baseEnd_908699 : Nat := 466599357260045444683475

theorem tailTrace_908699 : CollatzResearch.WordTrace tailWord_908699 prefixEnd_908699 466599357260045444683475 := by
  unfold tailWord_908699
  simp only [CollatzResearch.WordTrace]
  refine ⟨33142975334946191278729151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22095316889964127519152767 33142975334946191278729151)
  ·
    refine ⟨49714463002419286918093727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33142975334946191278729151 49714463002419286918093727)
    ·
      refine ⟨74571694503628930377140591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49714463002419286918093727 74571694503628930377140591)
      ·
        refine ⟨111857541755443395565710887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74571694503628930377140591 111857541755443395565710887)
        ·
          refine ⟨167786312633165093348566331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111857541755443395565710887 167786312633165093348566331)
          ·
            refine ⟨251679468949747640022849497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167786312633165093348566331 251679468949747640022849497)
            ·
              refine ⟨188759601712310730017137123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251679468949747640022849497 188759601712310730017137123)
              ·
                refine ⟨283139402568466095025705685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188759601712310730017137123 283139402568466095025705685)
                ·
                  refine ⟨6636079747698424102164977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 283139402568466095025705685 6636079747698424102164977)
                  ·
                    refine ⟨4977059810773818076623733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6636079747698424102164977 4977059810773818076623733)
                    ·
                      refine ⟨466599357260045444683475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4977059810773818076623733 466599357260045444683475)
                      ·
                        rfl

theorem cell23_908699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_908699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908699 prefixEnd_908699 := by exact prefixLift 908699
  have htrace : WordTrace (prefixWord ++ tailWord_908699) baseStart_908699 baseEnd_908699 := by
    simpa [prefixWord, tailWord_908699, baseEnd_908699] using wordTrace_append hprefix tailTrace_908699
  have hstable : (prefixWord ++ tailWord_908699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908699).length < 2 ^ (prefixWord ++ tailWord_908699).sum := by decide
  have hdescent : baseEnd_908699 < baseStart_908699 := by decide
  rcases family_descends (prefixWord ++ tailWord_908699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908719 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 2, 8]
def baseStart_908719 : Nat := 118140960795 + 908719 * 2 ^ 59
def prefixEnd_908719 : Nat := 4983230072969 + 3 ^ 40 * 908719 * 2
def baseEnd_908719 : Nat := 155536542291045122144461

theorem tailTrace_908719 : CollatzResearch.WordTrace tailWord_908719 prefixEnd_908719 155536542291045122144461 := by
  unfold tailWord_908719
  simp only [CollatzResearch.WordTrace]
  refine ⟨33143704794873734694457211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22095803196582489796304807 33143704794873734694457211)
  ·
    refine ⟨49715557192310602041685817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33143704794873734694457211 49715557192310602041685817)
    ·
      refine ⟨37286667894232951531264363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49715557192310602041685817 37286667894232951531264363)
      ·
        refine ⟨55930001841349427296896545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37286667894232951531264363 55930001841349427296896545)
        ·
          refine ⟨41947501381012070472672409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55930001841349427296896545 41947501381012070472672409)
          ·
            refine ⟨31460626035759052854504307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41947501381012070472672409 31460626035759052854504307)
            ·
              refine ⟨47190939053638579281756461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31460626035759052854504307 47190939053638579281756461)
              ·
                refine ⟨17696602145114467230658673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47190939053638579281756461 17696602145114467230658673)
                ·
                  refine ⟨13272451608835850422994005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17696602145114467230658673 13272451608835850422994005)
                  ·
                    refine ⟨155536542291045122144461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13272451608835850422994005 155536542291045122144461)
                    ·
                      rfl

theorem cell23_908719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_908719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908719 prefixEnd_908719 := by exact prefixLift 908719
  have htrace : WordTrace (prefixWord ++ tailWord_908719) baseStart_908719 baseEnd_908719 := by
    simpa [prefixWord, tailWord_908719, baseEnd_908719] using wordTrace_append hprefix tailTrace_908719
  have hstable : (prefixWord ++ tailWord_908719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908719).length < 2 ^ (prefixWord ++ tailWord_908719).sum := by decide
  have hdescent : baseEnd_908719 < baseStart_908719 := by decide
  rcases family_descends (prefixWord ++ tailWord_908719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908743 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_908743 : Nat := 118140960795 + 908743 * 2 ^ 59
def prefixEnd_908743 : Nat := 4983230072969 + 3 ^ 40 * 908743 * 2
def baseEnd_908743 : Nat := 466621950408843272533273

theorem tailTrace_908743 : CollatzResearch.WordTrace tailWord_908743 prefixEnd_908743 466621950408843272533273 := by
  unfold tailWord_908743
  simp only [CollatzResearch.WordTrace]
  refine ⟨33144580146786786793330883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22096386764524524528887255 33144580146786786793330883)
  ·
    refine ⟨49716870220180180189996325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33144580146786786793330883 49716870220180180189996325)
    ·
      refine ⟨9321913166283783785624311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49716870220180180189996325 9321913166283783785624311)
      ·
        refine ⟨13982869749425675678436467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321913166283783785624311 13982869749425675678436467)
        ·
          refine ⟨20974304624138513517654701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13982869749425675678436467 20974304624138513517654701)
          ·
            refine ⟨7865364234051942569120513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20974304624138513517654701 7865364234051942569120513)
            ·
              refine ⟨5899023175538956926840385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865364234051942569120513 5899023175538956926840385)
              ·
                refine ⟨4424267381654217695130289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5899023175538956926840385 4424267381654217695130289)
                ·
                  refine ⟨3318200536240663271347717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4424267381654217695130289 3318200536240663271347717)
                  ·
                    refine ⟨622162600545124363377697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3318200536240663271347717 622162600545124363377697)
                    ·
                      refine ⟨466621950408843272533273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622162600545124363377697 466621950408843272533273)
                      ·
                        rfl

theorem cell23_908743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_908743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908743 prefixEnd_908743 := by exact prefixLift 908743
  have htrace : WordTrace (prefixWord ++ tailWord_908743) baseStart_908743 baseEnd_908743 := by
    simpa [prefixWord, tailWord_908743, baseEnd_908743] using wordTrace_append hprefix tailTrace_908743
  have hstable : (prefixWord ++ tailWord_908743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908743).length < 2 ^ (prefixWord ++ tailWord_908743).sum := by decide
  have hdescent : baseEnd_908743 < baseStart_908743 := by decide
  rcases family_descends (prefixWord ++ tailWord_908743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908793 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 3]
def baseStart_908793 : Nat := 118140960795 + 908793 * 2 ^ 59
def prefixEnd_908793 : Nat := 4983230072969 + 3 ^ 40 * 908793 * 2
def baseEnd_908793 : Nat := 466647624441568076908043

theorem tailTrace_908793 : CollatzResearch.WordTrace tailWord_908793 prefixEnd_908793 466647624441568076908043 := by
  unfold tailWord_908793
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146403796605645332651033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22097602531070430221767355 33146403796605645332651033)
  ·
    refine ⟨24859802847454233999488275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33146403796605645332651033 24859802847454233999488275)
    ·
      refine ⟨37289704271181350999232413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24859802847454233999488275 37289704271181350999232413)
      ·
        refine ⟨13983639101693006624712155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37289704271181350999232413 13983639101693006624712155)
        ·
          refine ⟨20975458652539509937068233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13983639101693006624712155 20975458652539509937068233)
          ·
            refine ⟨15731593989404632452801175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20975458652539509937068233 15731593989404632452801175)
            ·
              refine ⟨23597390984106948679201763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15731593989404632452801175 23597390984106948679201763)
              ·
                refine ⟨35396086476160423018802645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23597390984106948679201763 35396086476160423018802645)
                ·
                  refine ⟨829595776785009914503187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 35396086476160423018802645 829595776785009914503187)
                  ·
                    refine ⟨1244393665177514871754781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829595776785009914503187 1244393665177514871754781)
                    ·
                      refine ⟨466647624441568076908043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244393665177514871754781 466647624441568076908043)
                      ·
                        rfl

theorem cell23_908793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_908793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908793 prefixEnd_908793 := by exact prefixLift 908793
  have htrace : WordTrace (prefixWord ++ tailWord_908793) baseStart_908793 baseEnd_908793 := by
    simpa [prefixWord, tailWord_908793, baseEnd_908793] using wordTrace_append hprefix tailTrace_908793
  have hstable : (prefixWord ++ tailWord_908793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908793).length < 2 ^ (prefixWord ++ tailWord_908793).sum := by decide
  have hdescent : baseEnd_908793 < baseStart_908793 := by decide
  rcases family_descends (prefixWord ++ tailWord_908793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908810 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_908810 : Nat := 118140960795 + 908810 * 2 ^ 59
def prefixEnd_908810 : Nat := 4983230072969 + 3 ^ 40 * 908810 * 2
def baseEnd_908810 : Nat := 466656353612694510395465

theorem tailTrace_908810 : CollatzResearch.WordTrace tailWord_908810 prefixEnd_908810 466656353612694510395465 := by
  unfold tailWord_908810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286755959386014309004971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22098015891696038157346589 8286755959386014309004971)
  ·
    refine ⟨12430133939079021463507457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8286755959386014309004971 12430133939079021463507457)
    ·
      refine ⟨9322600454309266097630593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12430133939079021463507457 9322600454309266097630593)
      ·
        refine ⟨6991950340731949573222945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9322600454309266097630593 6991950340731949573222945)
        ·
          refine ⟨5243962755548962179917209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6991950340731949573222945 5243962755548962179917209)
          ·
            refine ⟨3932972066661721634937907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5243962755548962179917209 3932972066661721634937907)
            ·
              refine ⟨5899458099992582452406861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932972066661721634937907 5899458099992582452406861)
              ·
                refine ⟨2212296787497218419652573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5899458099992582452406861 2212296787497218419652573)
                ·
                  refine ⟨829611295311456907369715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2212296787497218419652573 829611295311456907369715)
                  ·
                    refine ⟨1244416942967185361054573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829611295311456907369715 1244416942967185361054573)
                    ·
                      refine ⟨466656353612694510395465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244416942967185361054573 466656353612694510395465)
                      ·
                        rfl

theorem cell23_908810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_908810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908810 prefixEnd_908810 := by exact prefixLift 908810
  have htrace : WordTrace (prefixWord ++ tailWord_908810) baseStart_908810 baseEnd_908810 := by
    simpa [prefixWord, tailWord_908810, baseEnd_908810] using wordTrace_append hprefix tailTrace_908810
  have hstable : (prefixWord ++ tailWord_908810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908810).length < 2 ^ (prefixWord ++ tailWord_908810).sum := by decide
  have hdescent : baseEnd_908810 < baseStart_908810 := by decide
  rcases family_descends (prefixWord ++ tailWord_908810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908853 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_908853 : Nat := 118140960795 + 908853 * 2 ^ 59
def prefixEnd_908853 : Nat := 4983230072969 + 3 ^ 40 * 908853 * 2
def baseEnd_908853 : Nat := 466678433280837842157767

theorem tailTrace_908853 : CollatzResearch.WordTrace tailWord_908853 prefixEnd_908853 466678433280837842157767 := by
  unfold tailWord_908853
  simp only [CollatzResearch.WordTrace]
  refine ⟨33148592176388275579835213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22099061450925517053223475 33148592176388275579835213)
  ·
    refine ⟨12430722066145603342438205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33148592176388275579835213 12430722066145603342438205)
    ·
      refine ⟨4661520774804601253414327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12430722066145603342438205 4661520774804601253414327)
      ·
        refine ⟨6992281162206901880121491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661520774804601253414327 6992281162206901880121491)
        ·
          refine ⟨10488421743310352820182237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992281162206901880121491 10488421743310352820182237)
          ·
            refine ⟨3933158153741382307568339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10488421743310352820182237 3933158153741382307568339)
            ·
              refine ⟨5899737230612073461352509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933158153741382307568339 5899737230612073461352509)
              ·
                refine ⟨2212401461479527548007191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5899737230612073461352509 2212401461479527548007191)
                ·
                  refine ⟨3318602192219291322010787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212401461479527548007191 3318602192219291322010787)
                  ·
                    refine ⟨4977903288328936983016181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3318602192219291322010787 4977903288328936983016181)
                    ·
                      refine ⟨466678433280837842157767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4977903288328936983016181 466678433280837842157767)
                      ·
                        rfl

theorem cell23_908853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_908853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908853 prefixEnd_908853 := by exact prefixLift 908853
  have htrace : WordTrace (prefixWord ++ tailWord_908853) baseStart_908853 baseEnd_908853 := by
    simpa [prefixWord, tailWord_908853, baseEnd_908853] using wordTrace_append hprefix tailTrace_908853
  have hstable : (prefixWord ++ tailWord_908853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908853).length < 2 ^ (prefixWord ++ tailWord_908853).sum := by decide
  have hdescent : baseEnd_908853 < baseStart_908853 := by decide
  rcases family_descends (prefixWord ++ tailWord_908853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908854 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_908854 : Nat := 118140960795 + 908854 * 2 ^ 59
def prefixEnd_908854 : Nat := 4983230072969 + 3 ^ 40 * 908854 * 2
def baseEnd_908854 : Nat := 466678946761492338245263

theorem tailTrace_908854 : CollatzResearch.WordTrace tailWord_908854 prefixEnd_908854 466678946761492338245263 := by
  unfold tailWord_908854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071789290586540796913851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22099085766256435167081077 2071789290586540796913851)
  ·
    refine ⟨3107683935879811195370777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2071789290586540796913851 3107683935879811195370777)
    ·
      refine ⟨2330762951909858396528083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3107683935879811195370777 2330762951909858396528083)
      ·
        refine ⟨3496144427864787594792125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330762951909858396528083 3496144427864787594792125)
        ·
          refine ⟨1311054160449295348047047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3496144427864787594792125 1311054160449295348047047)
          ·
            refine ⟨1966581240673943022070571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311054160449295348047047 1966581240673943022070571)
            ·
              refine ⟨2949871861010914533105857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966581240673943022070571 2949871861010914533105857)
              ·
                refine ⟨2212403895758185899829393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949871861010914533105857 2212403895758185899829393)
                ·
                  refine ⟨1659302921818639424872045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2212403895758185899829393 1659302921818639424872045)
                  ·
                    refine ⟨622238595681989784327017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659302921818639424872045 622238595681989784327017)
                    ·
                      refine ⟨466678946761492338245263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622238595681989784327017 466678946761492338245263)
                      ·
                        rfl

theorem cell23_908854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_908854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908854 prefixEnd_908854 := by exact prefixLift 908854
  have htrace : WordTrace (prefixWord ++ tailWord_908854) baseStart_908854 baseEnd_908854 := by
    simpa [prefixWord, tailWord_908854, baseEnd_908854] using wordTrace_append hprefix tailTrace_908854
  have hstable : (prefixWord ++ tailWord_908854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908854).length < 2 ^ (prefixWord ++ tailWord_908854).sum := by decide
  have hdescent : baseEnd_908854 < baseStart_908854 := by decide
  rcases family_descends (prefixWord ++ tailWord_908854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908856 : List Nat := [2, 1, 2, 1, 4, 2, 11]
def baseStart_908856 : Nat := 118140960795 + 908856 * 2 ^ 59
def prefixEnd_908856 : Nat := 4983230072969 + 3 ^ 40 * 908856 * 2
def baseEnd_908856 : Nat := 5761481157071621363213

theorem tailTrace_908856 : CollatzResearch.WordTrace tailWord_908856 prefixEnd_908856 5761481157071621363213 := by
  unfold tailWord_908856
  simp only [CollatzResearch.WordTrace]
  refine ⟨16574350797688703546097211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22099134396918271394796281 16574350797688703546097211)
  ·
    refine ⟨24861526196533055319145817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16574350797688703546097211 24861526196533055319145817)
    ·
      refine ⟨18646144647399791489359363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24861526196533055319145817 18646144647399791489359363)
      ·
        refine ⟨27969216971099687234039045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18646144647399791489359363 27969216971099687234039045)
        ·
          refine ⟨5244228182081191356382321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27969216971099687234039045 5244228182081191356382321)
          ·
            refine ⟨3933171136560893517286741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5244228182081191356382321 3933171136560893517286741)
            ·
              refine ⟨5761481157071621363213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3933171136560893517286741 5761481157071621363213)
              ·
                rfl

theorem cell23_908856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 11].length) (baseStart_908856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908856 prefixEnd_908856 := by exact prefixLift 908856
  have htrace : WordTrace (prefixWord ++ tailWord_908856) baseStart_908856 baseEnd_908856 := by
    simpa [prefixWord, tailWord_908856, baseEnd_908856] using wordTrace_append hprefix tailTrace_908856
  have hstable : (prefixWord ++ tailWord_908856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908856).length < 2 ^ (prefixWord ++ tailWord_908856).sum := by decide
  have hdescent : baseEnd_908856 < baseStart_908856 := by decide
  rcases family_descends (prefixWord ++ tailWord_908856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908861 : List Nat := [1, 4, 1, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_908861 : Nat := 118140960795 + 908861 * 2 ^ 59
def prefixEnd_908861 : Nat := 4983230072969 + 3 ^ 40 * 908861 * 2
def baseEnd_908861 : Nat := 466682541126073810857731

theorem tailTrace_908861 : CollatzResearch.WordTrace tailWord_908861 prefixEnd_908861 466682541126073810857731 := by
  unfold tailWord_908861
  simp only [CollatzResearch.WordTrace]
  refine ⟨33148883960359292946126437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22099255973572861964084291 33148883960359292946126437)
  ·
    refine ⟨6215415742567367427398707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33148883960359292946126437 6215415742567367427398707)
    ·
      refine ⟨9323123613851051141098061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215415742567367427398707 9323123613851051141098061)
      ·
        refine ⟨3496171355194144177911773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9323123613851051141098061 3496171355194144177911773)
        ·
          refine ⟨1311064258197804066716915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3496171355194144177911773 1311064258197804066716915)
          ·
            refine ⟨1966596387296706100075373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311064258197804066716915 1966596387296706100075373)
            ·
              refine ⟨737473645236264787528265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1966596387296706100075373 737473645236264787528265)
              ·
                refine ⟨553105233927198590646199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737473645236264787528265 553105233927198590646199)
                ·
                  refine ⟨829657850890797885969299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553105233927198590646199 829657850890797885969299)
                  ·
                    refine ⟨1244486776336196828953949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829657850890797885969299 1244486776336196828953949)
                    ·
                      refine ⟨466682541126073810857731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244486776336196828953949 466682541126073810857731)
                      ·
                        rfl

theorem cell23_908861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_908861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908861 prefixEnd_908861 := by exact prefixLift 908861
  have htrace : WordTrace (prefixWord ++ tailWord_908861) baseStart_908861 baseEnd_908861 := by
    simpa [prefixWord, tailWord_908861, baseEnd_908861] using wordTrace_append hprefix tailTrace_908861
  have hstable : (prefixWord ++ tailWord_908861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908861).length < 2 ^ (prefixWord ++ tailWord_908861).sum := by decide
  have hdescent : baseEnd_908861 < baseStart_908861 := by decide
  rcases family_descends (prefixWord ++ tailWord_908861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908887 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_908887 : Nat := 118140960795 + 908887 * 2 ^ 59
def prefixEnd_908887 : Nat := 4983230072969 + 3 ^ 40 * 908887 * 2
def baseEnd_908887 : Nat := 466695891623090709132611

theorem tailTrace_908887 : CollatzResearch.WordTrace tailWord_908887 prefixEnd_908887 466695891623090709132611 := by
  unfold tailWord_908887
  simp only [CollatzResearch.WordTrace]
  refine ⟨33149832258265099386572915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22099888172176732924381943 33149832258265099386572915)
  ·
    refine ⟨49724748387397649079859373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33149832258265099386572915 49724748387397649079859373)
    ·
      refine ⟨18646780645274118404947265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49724748387397649079859373 18646780645274118404947265)
      ·
        refine ⟨13985085483955588803710449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18646780645274118404947265 13985085483955588803710449)
        ·
          refine ⟨10488814112966691602782837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13985085483955588803710449 10488814112966691602782837)
          ·
            refine ⟨983326323090627337760891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10488814112966691602782837 983326323090627337760891)
            ·
              refine ⟨1474989484635941006641337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983326323090627337760891 1474989484635941006641337)
              ·
                refine ⟨1106242113476955754981003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474989484635941006641337 1106242113476955754981003)
                ·
                  refine ⟨1659363170215433632471505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106242113476955754981003 1659363170215433632471505)
                  ·
                    refine ⟨1244522377661575224353629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1659363170215433632471505 1244522377661575224353629)
                    ·
                      refine ⟨466695891623090709132611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244522377661575224353629 466695891623090709132611)
                      ·
                        rfl

theorem cell23_908887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_908887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908887 prefixEnd_908887 := by exact prefixLift 908887
  have htrace : WordTrace (prefixWord ++ tailWord_908887) baseStart_908887 baseEnd_908887 := by
    simpa [prefixWord, tailWord_908887, baseEnd_908887] using wordTrace_append hprefix tailTrace_908887
  have hstable : (prefixWord ++ tailWord_908887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908887).length < 2 ^ (prefixWord ++ tailWord_908887).sum := by decide
  have hdescent : baseEnd_908887 < baseStart_908887 := by decide
  rcases family_descends (prefixWord ++ tailWord_908887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908900 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_908900 : Nat := 118140960795 + 908900 * 2 ^ 59
def prefixEnd_908900 : Nat := 4983230072969 + 3 ^ 40 * 908900 * 2
def baseEnd_908900 : Nat := 466702566871599158270051

theorem tailTrace_908900 : CollatzResearch.WordTrace tailWord_908900 prefixEnd_908900 466702566871599158270051 := by
  unfold tailWord_908900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575153203609001303398077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22100204271478668404530769 16575153203609001303398077)
  ·
    refine ⟨6215682451353375488774279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16575153203609001303398077 6215682451353375488774279)
    ·
      refine ⟨9323523677030063233161419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215682451353375488774279 9323523677030063233161419)
      ·
        refine ⟨13985285515545094849742129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323523677030063233161419 13985285515545094849742129)
        ·
          refine ⟨10488964136658821137306597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13985285515545094849742129 10488964136658821137306597)
          ·
            refine ⟨1966680775623528963244987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10488964136658821137306597 1966680775623528963244987)
            ·
              refine ⟨2950021163435293444867481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966680775623528963244987 2950021163435293444867481)
              ·
                refine ⟨2212515872576470083650611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950021163435293444867481 2212515872576470083650611)
                ·
                  refine ⟨3318773808864705125475917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212515872576470083650611 3318773808864705125475917)
                  ·
                    refine ⟨1244540178324264422053469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318773808864705125475917 1244540178324264422053469)
                    ·
                      refine ⟨466702566871599158270051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244540178324264422053469 466702566871599158270051)
                      ·
                        rfl

theorem cell23_908900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_908900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908900 prefixEnd_908900 := by exact prefixLift 908900
  have htrace : WordTrace (prefixWord ++ tailWord_908900) baseStart_908900 baseEnd_908900 := by
    simpa [prefixWord, tailWord_908900, baseEnd_908900] using wordTrace_append hprefix tailTrace_908900
  have hstable : (prefixWord ++ tailWord_908900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908900).length < 2 ^ (prefixWord ++ tailWord_908900).sum := by decide
  have hdescent : baseEnd_908900 < baseStart_908900 := by decide
  rcases family_descends (prefixWord ++ tailWord_908900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908904 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_908904 : Nat := 118140960795 + 908904 * 2 ^ 59
def prefixEnd_908904 : Nat := 4983230072969 + 3 ^ 40 * 908904 * 2
def baseEnd_908904 : Nat := 466704620794217142620033

theorem tailTrace_908904 : CollatzResearch.WordTrace tailWord_908904 prefixEnd_908904 466704620794217142620033 := by
  unfold tailWord_908904
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575226149601755644970883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22100301532802340859961177 16575226149601755644970883)
  ·
    refine ⟨24862839224402633467456325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16575226149601755644970883 24862839224402633467456325)
    ·
      refine ⟨4661782354575493775148061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24862839224402633467456325 4661782354575493775148061)
      ·
        refine ⟨1748168382965810165680523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4661782354575493775148061 1748168382965810165680523)
        ·
          refine ⟨2622252574448715248520785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748168382965810165680523 2622252574448715248520785)
          ·
            refine ⟨1966689430836536436390589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622252574448715248520785 1966689430836536436390589)
            ·
              refine ⟨737508536563701163646471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1966689430836536436390589 737508536563701163646471)
              ·
                refine ⟨1106262804845551745469707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737508536563701163646471 1106262804845551745469707)
                ·
                  refine ⟨1659394207268327618204561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106262804845551745469707 1659394207268327618204561)
                  ·
                    refine ⟨1244545655451245713653421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1659394207268327618204561 1244545655451245713653421)
                    ·
                      refine ⟨466704620794217142620033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244545655451245713653421 466704620794217142620033)
                      ·
                        rfl

theorem cell23_908904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_908904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908904 prefixEnd_908904 := by exact prefixLift 908904
  have htrace : WordTrace (prefixWord ++ tailWord_908904) baseStart_908904 baseEnd_908904 := by
    simpa [prefixWord, tailWord_908904, baseEnd_908904] using wordTrace_append hprefix tailTrace_908904
  have hstable : (prefixWord ++ tailWord_908904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908904).length < 2 ^ (prefixWord ++ tailWord_908904).sum := by decide
  have hdescent : baseEnd_908904 < baseStart_908904 := by decide
  rcases family_descends (prefixWord ++ tailWord_908904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908918 : List Nat := [5, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_908918 : Nat := 118140960795 + 908918 * 2 ^ 59
def prefixEnd_908918 : Nat := 4983230072969 + 3 ^ 40 * 908918 * 2
def baseEnd_908918 : Nat := 466711809523380087844969

theorem tailTrace_908918 : CollatzResearch.WordTrace tailWord_908918 prefixEnd_908918 466711809523380087844969 := by
  unfold tailWord_908918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071935182572049480059463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22100641947435194453967605 2071935182572049480059463)
  ·
    refine ⟨3107902773858074220089195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2071935182572049480059463 3107902773858074220089195)
    ·
      refine ⟨4661854160787111330133793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3107902773858074220089195 4661854160787111330133793)
      ·
        refine ⟨3496390620590333497600345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4661854160787111330133793 3496390620590333497600345)
        ·
          refine ⟨2622292965442750123200259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3496390620590333497600345 2622292965442750123200259)
          ·
            refine ⟨3933439448164125184800389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622292965442750123200259 3933439448164125184800389)
            ·
              refine ⟨737519896530773472150073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3933439448164125184800389 737519896530773472150073)
              ·
                refine ⟨553139922398080104112555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737519896530773472150073 553139922398080104112555)
                ·
                  refine ⟨829709883597120156168833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553139922398080104112555 829709883597120156168833)
                  ·
                    refine ⟨622282412697840117126625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 829709883597120156168833 622282412697840117126625)
                    ·
                      refine ⟨466711809523380087844969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622282412697840117126625 466711809523380087844969)
                      ·
                        rfl

theorem cell23_908918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_908918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908918 prefixEnd_908918 := by exact prefixLift 908918
  have htrace : WordTrace (prefixWord ++ tailWord_908918) baseStart_908918 baseEnd_908918 := by
    simpa [prefixWord, tailWord_908918, baseEnd_908918] using wordTrace_append hprefix tailTrace_908918
  have hstable : (prefixWord ++ tailWord_908918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908918).length < 2 ^ (prefixWord ++ tailWord_908918).sum := by decide
  have hdescent : baseEnd_908918 < baseStart_908918 := by decide
  rcases family_descends (prefixWord ++ tailWord_908918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908933 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_908933 : Nat := 118140960795 + 908933 * 2 ^ 59
def prefixEnd_908933 : Nat := 4983230072969 + 3 ^ 40 * 908933 * 2
def baseEnd_908933 : Nat := 155573170577732509719133

theorem tailTrace_908933 : CollatzResearch.WordTrace tailWord_908933 prefixEnd_908933 155573170577732509719133 := by
  unfold tailWord_908933
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151510016098449242747453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22101006677398966161831635 33151510016098449242747453)
  ·
    refine ⟨12431816256036918466030295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33151510016098449242747453 12431816256036918466030295)
    ·
      refine ⟨18647724384055377699045443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12431816256036918466030295 18647724384055377699045443)
      ·
        refine ⟨27971586576083066548568165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18647724384055377699045443 27971586576083066548568165)
        ·
          refine ⟨5244672483015574977856531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27971586576083066548568165 5244672483015574977856531)
          ·
            refine ⟨7867008724523362466784797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244672483015574977856531 7867008724523362466784797)
            ·
              refine ⟨2950128271696260925044299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7867008724523362466784797 2950128271696260925044299)
              ·
                refine ⟨4425192407544391387566449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950128271696260925044299 4425192407544391387566449)
                ·
                  refine ⟨3318894305658293540674837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425192407544391387566449 3318894305658293540674837)
                  ·
                    refine ⟨155573170577732509719133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3318894305658293540674837 155573170577732509719133)
                    ·
                      rfl

theorem cell23_908933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_908933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908933 prefixEnd_908933 := by exact prefixLift 908933
  have htrace : WordTrace (prefixWord ++ tailWord_908933) baseStart_908933 baseEnd_908933 := by
    simpa [prefixWord, tailWord_908933, baseEnd_908933] using wordTrace_append hprefix tailTrace_908933
  have hstable : (prefixWord ++ tailWord_908933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908933).length < 2 ^ (prefixWord ++ tailWord_908933).sum := by decide
  have hdescent : baseEnd_908933 < baseStart_908933 := by decide
  rcases family_descends (prefixWord ++ tailWord_908933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908957 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_908957 : Nat := 118140960795 + 908957 * 2 ^ 59
def prefixEnd_908957 : Nat := 4983230072969 + 3 ^ 40 * 908957 * 2
def baseEnd_908957 : Nat := 466731835268905435257289

theorem tailTrace_908957 : CollatzResearch.WordTrace tailWord_908957 prefixEnd_908957 466731835268905435257289 := by
  unfold tailWord_908957
  simp only [CollatzResearch.WordTrace]
  refine ⟨33152385368011501341621125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22101590245341000894414083 33152385368011501341621125)
  ·
    refine ⟨6216072256502156501553961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33152385368011501341621125 6216072256502156501553961)
    ·
      refine ⟨4662054192376617376165471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6216072256502156501553961 4662054192376617376165471)
      ·
        refine ⟨6993081288564926064248207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662054192376617376165471 6993081288564926064248207)
        ·
          refine ⟨10489621932847389096372311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993081288564926064248207 10489621932847389096372311)
          ·
            refine ⟨15734432899271083644558467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10489621932847389096372311 15734432899271083644558467)
            ·
              refine ⟨23601649348906625466837701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15734432899271083644558467 23601649348906625466837701)
              ·
                refine ⟨4425309252919992275032069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23601649348906625466837701 4425309252919992275032069)
                ·
                  refine ⟨829745484922498551568513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4425309252919992275032069 829745484922498551568513)
                  ·
                    refine ⟨622309113691873913676385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 829745484922498551568513 622309113691873913676385)
                    ·
                      refine ⟨466731835268905435257289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622309113691873913676385 466731835268905435257289)
                      ·
                        rfl

theorem cell23_908957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_908957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908957 prefixEnd_908957 := by exact prefixLift 908957
  have htrace : WordTrace (prefixWord ++ tailWord_908957) baseStart_908957 baseEnd_908957 := by
    simpa [prefixWord, tailWord_908957, baseEnd_908957] using wordTrace_append hprefix tailTrace_908957
  have hstable : (prefixWord ++ tailWord_908957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908957).length < 2 ^ (prefixWord ++ tailWord_908957).sum := by decide
  have hdescent : baseEnd_908957 < baseStart_908957 := by decide
  rcases family_descends (prefixWord ++ tailWord_908957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908961 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_908961 : Nat := 118140960795 + 908961 * 2 ^ 59
def prefixEnd_908961 : Nat := 4983230072969 + 3 ^ 40 * 908961 * 2
def baseEnd_908961 : Nat := 466733889191523419607271

theorem tailTrace_908961 : CollatzResearch.WordTrace tailWord_908961 prefixEnd_908961 466733889191523419607271 := by
  unfold tailWord_908961
  simp only [CollatzResearch.WordTrace]
  refine ⟨33152531259997010024766737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22101687506664673349844491 33152531259997010024766737)
  ·
    refine ⟨24864398444997757518575053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33152531259997010024766737 24864398444997757518575053)
    ·
      refine ⟨9324149416874159069465645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24864398444997757518575053 9324149416874159069465645)
      ·
        refine ⟨3496556031327809651049617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9324149416874159069465645 3496556031327809651049617)
        ·
          refine ⟨2622417023495857238287213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3496556031327809651049617 2622417023495857238287213)
          ·
            refine ⟨983406383810946464357705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2622417023495857238287213 983406383810946464357705)
            ·
              refine ⟨737554787858209848268279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983406383810946464357705 737554787858209848268279)
              ·
                refine ⟨1106332181787314772402419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737554787858209848268279 1106332181787314772402419)
                ·
                  refine ⟨1659498272680972158603629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106332181787314772402419 1659498272680972158603629)
                  ·
                    refine ⟨622311852255364559476361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659498272680972158603629 622311852255364559476361)
                    ·
                      refine ⟨466733889191523419607271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622311852255364559476361 466733889191523419607271)
                      ·
                        rfl

theorem cell23_908961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_908961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_908961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_908961 prefixEnd_908961 := by exact prefixLift 908961
  have htrace : WordTrace (prefixWord ++ tailWord_908961) baseStart_908961 baseEnd_908961 := by
    simpa [prefixWord, tailWord_908961, baseEnd_908961] using wordTrace_append hprefix tailTrace_908961
  have hstable : (prefixWord ++ tailWord_908961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908961).length < 2 ^ (prefixWord ++ tailWord_908961).sum := by decide
  have hdescent : baseEnd_908961 < baseStart_908961 := by decide
  rcases family_descends (prefixWord ++ tailWord_908961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909010 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_909010 : Nat := 118140960795 + 909010 * 2 ^ 59
def prefixEnd_909010 : Nat := 4983230072969 + 3 ^ 40 * 909010 * 2
def baseEnd_909010 : Nat := 155586349914531242631515

theorem tailTrace_909010 : CollatzResearch.WordTrace tailWord_909010 prefixEnd_909010 155586349914531242631515 := by
  unfold tailWord_909010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8288579609204872848325121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22102878957879660928866989 8288579609204872848325121)
  ·
    refine ⟨6216434706903654636243841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8288579609204872848325121 6216434706903654636243841)
    ·
      refine ⟨4662326030177740977182881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6216434706903654636243841 4662326030177740977182881)
      ·
        refine ⟨3496744522633305732887161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4662326030177740977182881 3496744522633305732887161)
        ·
          refine ⟨2622558391974979299665371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3496744522633305732887161 2622558391974979299665371)
          ·
            refine ⟨3933837587962468949498057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622558391974979299665371 3933837587962468949498057)
            ·
              refine ⟨2950378190971851712123543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933837587962468949498057 2950378190971851712123543)
              ·
                refine ⟨4425567286457777568185315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950378190971851712123543 4425567286457777568185315)
                ·
                  refine ⟨6638350929686666352277973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425567286457777568185315 6638350929686666352277973)
                  ·
                    refine ⟨155586349914531242631515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6638350929686666352277973 155586349914531242631515)
                    ·
                      rfl

theorem cell23_909010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_909010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909010 prefixEnd_909010 := by exact prefixLift 909010
  have htrace : WordTrace (prefixWord ++ tailWord_909010) baseStart_909010 baseEnd_909010 := by
    simpa [prefixWord, tailWord_909010, baseEnd_909010] using wordTrace_append hprefix tailTrace_909010
  have hstable : (prefixWord ++ tailWord_909010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909010).length < 2 ^ (prefixWord ++ tailWord_909010).sum := by decide
  have hdescent : baseEnd_909010 < baseStart_909010 := by decide
  rcases family_descends (prefixWord ++ tailWord_909010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909027 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 2, 5]
def baseStart_909027 : Nat := 118140960795 + 909027 * 2 ^ 59
def prefixEnd_909027 : Nat := 4983230072969 + 3 ^ 40 * 909027 * 2
def baseEnd_909027 : Nat := 155589259638240053793989

theorem tailTrace_909027 : CollatzResearch.WordTrace tailWord_909027 prefixEnd_909027 155589259638240053793989 := by
  unfold tailWord_909027
  simp only [CollatzResearch.WordTrace]
  refine ⟨33154938477757903296669335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22103292318505268864446223 33154938477757903296669335)
  ·
    refine ⟨49732407716636854945004003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33154938477757903296669335 49732407716636854945004003)
    ·
      refine ⟨74598611574955282417506005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49732407716636854945004003 74598611574955282417506005)
      ·
        refine ⟨1748404958788014431660297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 74598611574955282417506005 1748404958788014431660297)
        ·
          refine ⟨1311303719091010823745223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748404958788014431660297 1311303719091010823745223)
          ·
            refine ⟨1966955578636516235617835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311303719091010823745223 1966955578636516235617835)
            ·
              refine ⟨2950433367954774353426753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966955578636516235617835 2950433367954774353426753)
              ·
                refine ⟨2212825025966080765070065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950433367954774353426753 2212825025966080765070065)
                ·
                  refine ⟨1659618769474560573802549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2212825025966080765070065 1659618769474560573802549)
                  ·
                    refine ⟨155589259638240053793989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1659618769474560573802549 155589259638240053793989)
                    ·
                      rfl

theorem cell23_909027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 5].length) (baseStart_909027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909027 prefixEnd_909027 := by exact prefixLift 909027
  have htrace : WordTrace (prefixWord ++ tailWord_909027) baseStart_909027 baseEnd_909027 := by
    simpa [prefixWord, tailWord_909027, baseEnd_909027] using wordTrace_append hprefix tailTrace_909027
  have hstable : (prefixWord ++ tailWord_909027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909027).length < 2 ^ (prefixWord ++ tailWord_909027).sum := by decide
  have hdescent : baseEnd_909027 < baseStart_909027 := by decide
  rcases family_descends (prefixWord ++ tailWord_909027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909031 : List Nat := [1, 1, 5, 4, 1, 1, 3, 2, 5]
def baseStart_909031 : Nat := 118140960795 + 909031 * 2 ^ 59
def prefixEnd_909031 : Nat := 4983230072969 + 3 ^ 40 * 909031 * 2
def baseEnd_909031 : Nat := 51863314759704238414661

theorem tailTrace_909031 : CollatzResearch.WordTrace tailWord_909031 prefixEnd_909031 51863314759704238414661 := by
  unfold tailWord_909031
  simp only [CollatzResearch.WordTrace]
  refine ⟨33155084369743411979814947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22103389579828941319876631 33155084369743411979814947)
  ·
    refine ⟨49732626554615117969722421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33155084369743411979814947 49732626554615117969722421)
    ·
      refine ⟨4662433739495167309661477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49732626554615117969722421 4662433739495167309661477)
      ·
        refine ⟨874206326155343870561527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4662433739495167309661477 874206326155343870561527)
        ·
          refine ⟨1311309489233015805842291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874206326155343870561527 1311309489233015805842291)
          ·
            refine ⟨1966964233849523708763437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311309489233015805842291 1966964233849523708763437)
            ·
              refine ⟨737611587693571390786289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1966964233849523708763437 737611587693571390786289)
              ·
                refine ⟨553208690770178543089717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737611587693571390786289 553208690770178543089717)
                ·
                  refine ⟨51863314759704238414661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 553208690770178543089717 51863314759704238414661)
                  ·
                    rfl

theorem cell23_909031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 5].length) (baseStart_909031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909031 prefixEnd_909031 := by exact prefixLift 909031
  have htrace : WordTrace (prefixWord ++ tailWord_909031) baseStart_909031 baseEnd_909031 := by
    simpa [prefixWord, tailWord_909031, baseEnd_909031] using wordTrace_append hprefix tailTrace_909031
  have hstable : (prefixWord ++ tailWord_909031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909031).length < 2 ^ (prefixWord ++ tailWord_909031).sum := by decide
  have hdescent : baseEnd_909031 < baseStart_909031 := by decide
  rcases family_descends (prefixWord ++ tailWord_909031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909040 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 3, 4]
def baseStart_909040 : Nat := 118140960795 + 909040 * 2 ^ 59
def prefixEnd_909040 : Nat := 4983230072969 + 3 ^ 40 * 909040 * 2
def baseEnd_909040 : Nat := 155591484721076203506469

theorem tailTrace_909040 : CollatzResearch.WordTrace tailWord_909040 prefixEnd_909040 155591484721076203506469 := by
  unfold tailWord_909040
  simp only [CollatzResearch.WordTrace]
  refine ⟨16577706313355403258446287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22103608417807204344595049 16577706313355403258446287)
  ·
    refine ⟨24866559470033104887669431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16577706313355403258446287 24866559470033104887669431)
    ·
      refine ⟨37299839205049657331504147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24866559470033104887669431 37299839205049657331504147)
      ·
        refine ⟨55949758807574485997256221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37299839205049657331504147 55949758807574485997256221)
        ·
          refine ⟨20981159552840432248971083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55949758807574485997256221 20981159552840432248971083)
          ·
            refine ⟨31471739329260648373456625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20981159552840432248971083 31471739329260648373456625)
            ·
              refine ⟨23603804496945486280092469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31471739329260648373456625 23603804496945486280092469)
              ·
                refine ⟨2212856671588639338758669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23603804496945486280092469 2212856671588639338758669)
                ·
                  refine ⟨829821251845739752034501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2212856671588639338758669 829821251845739752034501)
                  ·
                    refine ⟨155591484721076203506469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 829821251845739752034501 155591484721076203506469)
                    ·
                      rfl

theorem cell23_909040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_909040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909040 prefixEnd_909040 := by exact prefixLift 909040
  have htrace : WordTrace (prefixWord ++ tailWord_909040) baseStart_909040 baseEnd_909040 := by
    simpa [prefixWord, tailWord_909040, baseEnd_909040] using wordTrace_append hprefix tailTrace_909040
  have hstable : (prefixWord ++ tailWord_909040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909040).length < 2 ^ (prefixWord ++ tailWord_909040).sum := by decide
  have hdescent : baseEnd_909040 < baseStart_909040 := by decide
  rcases family_descends (prefixWord ++ tailWord_909040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909043 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6]
def baseStart_909043 : Nat := 118140960795 + 909043 * 2 ^ 59
def prefixEnd_909043 : Nat := 4983230072969 + 3 ^ 40 * 909043 * 2
def baseEnd_909043 : Nat := 466775994605192098781893

theorem tailTrace_909043 : CollatzResearch.WordTrace tailWord_909043 prefixEnd_909043 466775994605192098781893 := by
  unfold tailWord_909043
  simp only [CollatzResearch.WordTrace]
  refine ⟨33155522045699938029251783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22103681363799958686167855 33155522045699938029251783)
  ·
    refine ⟨49733283068549907043877675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33155522045699938029251783 49733283068549907043877675)
    ·
      refine ⟨74599924602824860565816513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49733283068549907043877675 74599924602824860565816513)
      ·
        refine ⟨55949943452118645424362385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74599924602824860565816513 55949943452118645424362385)
        ·
          refine ⟨41962457589088984068271789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55949943452118645424362385 41962457589088984068271789)
          ·
            refine ⟨15735921595908369025601921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41962457589088984068271789 15735921595908369025601921)
            ·
              refine ⟨11801941196931276769201441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15735921595908369025601921 11801941196931276769201441)
              ·
                refine ⟨8851455897698457576901081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801941196931276769201441 8851455897698457576901081)
                ·
                  refine ⟨6638591923273843182675811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8851455897698457576901081 6638591923273843182675811)
                  ·
                    refine ⟨9957887884910764774013717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6638591923273843182675811 9957887884910764774013717)
                    ·
                      refine ⟨466775994605192098781893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9957887884910764774013717 466775994605192098781893)
                      ·
                        rfl

theorem cell23_909043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_909043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909043 prefixEnd_909043 := by exact prefixLift 909043
  have htrace : WordTrace (prefixWord ++ tailWord_909043) baseStart_909043 baseEnd_909043 := by
    simpa [prefixWord, tailWord_909043, baseEnd_909043] using wordTrace_append hprefix tailTrace_909043
  have hstable : (prefixWord ++ tailWord_909043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909043).length < 2 ^ (prefixWord ++ tailWord_909043).sum := by decide
  have hdescent : baseEnd_909043 < baseStart_909043 := by decide
  rcases family_descends (prefixWord ++ tailWord_909043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909050 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_909050 : Nat := 118140960795 + 909050 * 2 ^ 59
def prefixEnd_909050 : Nat := 4983230072969 + 3 ^ 40 * 909050 * 2
def baseEnd_909050 : Nat := 466779588969773571394361

theorem tailTrace_909050 : CollatzResearch.WordTrace tailWord_909050 prefixEnd_909050 466779588969773571394361 := by
  unfold tailWord_909050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8288944339168644556189151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22103851571116385483171069 8288944339168644556189151)
  ·
    refine ⟨12433416508752966834283727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8288944339168644556189151 12433416508752966834283727)
    ·
      refine ⟨18650124763129450251425591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12433416508752966834283727 18650124763129450251425591)
      ·
        refine ⟨27975187144694175377138387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18650124763129450251425591 27975187144694175377138387)
        ·
          refine ⟨41962780717041263065707581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27975187144694175377138387 41962780717041263065707581)
          ·
            refine ⟨15736042768890473649640343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41962780717041263065707581 15736042768890473649640343)
            ·
              refine ⟨23604064153335710474460515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15736042768890473649640343 23604064153335710474460515)
              ·
                refine ⟨35406096230003565711690773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23604064153335710474460515 35406096230003565711690773)
                ·
                  refine ⟨1659660760781417142735505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35406096230003565711690773 1659660760781417142735505)
                  ·
                    refine ⟨1244745570586062857051629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1659660760781417142735505 1244745570586062857051629)
                    ·
                      refine ⟨466779588969773571394361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244745570586062857051629 466779588969773571394361)
                      ·
                        rfl

theorem cell23_909050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_909050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909050 prefixEnd_909050 := by exact prefixLift 909050
  have htrace : WordTrace (prefixWord ++ tailWord_909050) baseStart_909050 baseEnd_909050 := by
    simpa [prefixWord, tailWord_909050, baseEnd_909050] using wordTrace_append hprefix tailTrace_909050
  have hstable : (prefixWord ++ tailWord_909050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909050).length < 2 ^ (prefixWord ++ tailWord_909050).sum := by decide
  have hdescent : baseEnd_909050 < baseStart_909050 := by decide
  rcases family_descends (prefixWord ++ tailWord_909050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909053 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 10]
def baseStart_909053 : Nat := 118140960795 + 909053 * 2 ^ 59
def prefixEnd_909053 : Nat := 4983230072969 + 3 ^ 40 * 909053 * 2
def baseEnd_909053 : Nat := 51864569934637451072983

theorem tailTrace_909053 : CollatzResearch.WordTrace tailWord_909053 prefixEnd_909053 51864569934637451072983 := by
  unfold tailWord_909053
  simp only [CollatzResearch.WordTrace]
  refine ⟨33155886775663709737115813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22103924517109139824743875 33155886775663709737115813)
  ·
    refine ⟨6216728770436945575709215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33155886775663709737115813 6216728770436945575709215)
    ·
      refine ⟨9325093155655418363563823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6216728770436945575709215 9325093155655418363563823)
      ·
        refine ⟨13987639733483127545345735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9325093155655418363563823 13987639733483127545345735)
        ·
          refine ⟨20981459600224691318018603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13987639733483127545345735 20981459600224691318018603)
          ·
            refine ⟨31472189400337036977027905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20981459600224691318018603 31472189400337036977027905)
            ·
              refine ⟨23604142050252777732770929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31472189400337036977027905 23604142050252777732770929)
              ·
                refine ⟨17703106537689583299578197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23604142050252777732770929 17703106537689583299578197)
                ·
                  refine ⟨51864569934637451072983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 17703106537689583299578197 51864569934637451072983)
                  ·
                    rfl

theorem cell23_909053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_909053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909053 prefixEnd_909053 := by exact prefixLift 909053
  have htrace : WordTrace (prefixWord ++ tailWord_909053) baseStart_909053 baseEnd_909053 := by
    simpa [prefixWord, tailWord_909053, baseEnd_909053] using wordTrace_append hprefix tailTrace_909053
  have hstable : (prefixWord ++ tailWord_909053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909053).length < 2 ^ (prefixWord ++ tailWord_909053).sum := by decide
  have hdescent : baseEnd_909053 < baseStart_909053 := by decide
  rcases family_descends (prefixWord ++ tailWord_909053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909073 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_909073 : Nat := 118140960795 + 909073 * 2 ^ 59
def prefixEnd_909073 : Nat := 4983230072969 + 3 ^ 40 * 909073 * 2
def baseEnd_909073 : Nat := 466791399024826981406755

theorem tailTrace_909073 : CollatzResearch.WordTrace tailWord_909073 prefixEnd_909073 466791399024826981406755 := by
  unfold tailWord_909073
  simp only [CollatzResearch.WordTrace]
  refine ⟨33156616235591253152843873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22104410823727502101895915 33156616235591253152843873)
  ·
    refine ⟨24867462176693439864632905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33156616235591253152843873 24867462176693439864632905)
    ·
      refine ⟨18650596632520079898474679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24867462176693439864632905 18650596632520079898474679)
      ·
        refine ⟨27975894948780119847712019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18650596632520079898474679 27975894948780119847712019)
        ·
          refine ⟨41963842423170179771568029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27975894948780119847712019 41963842423170179771568029)
          ·
            refine ⟨15736440908688817414338011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41963842423170179771568029 15736440908688817414338011)
            ·
              refine ⟨23604661363033226121507017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15736440908688817414338011 23604661363033226121507017)
              ·
                refine ⟨17703496022274919591130263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23604661363033226121507017 17703496022274919591130263)
                ·
                  refine ⟨26555244033412379386695395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17703496022274919591130263 26555244033412379386695395)
                  ·
                    refine ⟨39832866050118569080043093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26555244033412379386695395 39832866050118569080043093)
                    ·
                      refine ⟨466791399024826981406755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39832866050118569080043093 466791399024826981406755)
                      ·
                        rfl

theorem cell23_909073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_909073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909073 prefixEnd_909073 := by exact prefixLift 909073
  have htrace : WordTrace (prefixWord ++ tailWord_909073) baseStart_909073 baseEnd_909073 := by
    simpa [prefixWord, tailWord_909073, baseEnd_909073] using wordTrace_append hprefix tailTrace_909073
  have hstable : (prefixWord ++ tailWord_909073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909073).length < 2 ^ (prefixWord ++ tailWord_909073).sum := by decide
  have hdescent : baseEnd_909073 < baseStart_909073 := by decide
  rcases family_descends (prefixWord ++ tailWord_909073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909090 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_909090 : Nat := 118140960795 + 909090 * 2 ^ 59
def prefixEnd_909090 : Nat := 4983230072969 + 3 ^ 40 * 909090 * 2
def baseEnd_909090 : Nat := 466800128195953414894177

theorem tailTrace_909090 : CollatzResearch.WordTrace tailWord_909090 prefixEnd_909090 466800128195953414894177 := by
  unfold tailWord_909090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289309069132416264053181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22104824184353110037475149 8289309069132416264053181)
  ·
    refine ⟨3108490900924656099019943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8289309069132416264053181 3108490900924656099019943)
    ·
      refine ⟨4662736351386984148529915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108490900924656099019943 4662736351386984148529915)
      ·
        refine ⟨6994104527080476222794873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662736351386984148529915 6994104527080476222794873)
        ·
          refine ⟨5245578395310357167096155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6994104527080476222794873 5245578395310357167096155)
          ·
            refine ⟨7868367592965535750644233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245578395310357167096155 7868367592965535750644233)
            ·
              refine ⟨5901275694724151812983175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7868367592965535750644233 5901275694724151812983175)
              ·
                refine ⟨8851913542086227719474763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5901275694724151812983175 8851913542086227719474763)
                ·
                  refine ⟨13277870313129341579212145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851913542086227719474763 13277870313129341579212145)
                  ·
                    refine ⟨9958402734847006184409109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13277870313129341579212145 9958402734847006184409109)
                    ·
                      refine ⟨466800128195953414894177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9958402734847006184409109 466800128195953414894177)
                      ·
                        rfl

theorem cell23_909090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_909090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909090 prefixEnd_909090 := by exact prefixLift 909090
  have htrace : WordTrace (prefixWord ++ tailWord_909090) baseStart_909090 baseEnd_909090 := by
    simpa [prefixWord, tailWord_909090, baseEnd_909090] using wordTrace_append hprefix tailTrace_909090
  have hstable : (prefixWord ++ tailWord_909090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909090).length < 2 ^ (prefixWord ++ tailWord_909090).sum := by decide
  have hdescent : baseEnd_909090 < baseStart_909090 := by decide
  rcases family_descends (prefixWord ++ tailWord_909090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909100 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_909100 : Nat := 118140960795 + 909100 * 2 ^ 59
def prefixEnd_909100 : Nat := 4983230072969 + 3 ^ 40 * 909100 * 2
def baseEnd_909100 : Nat := 155601754334166125256377

theorem tailTrace_909100 : CollatzResearch.WordTrace tailWord_909100 prefixEnd_909100 155601754334166125256377 := by
  unfold tailWord_909100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578800503246718382038377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22105067337662291176051169 16578800503246718382038377)
  ·
    refine ⟨12434100377435038786528783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16578800503246718382038377 12434100377435038786528783)
    ·
      refine ⟨18651150566152558179793175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434100377435038786528783 18651150566152558179793175)
      ·
        refine ⟨27976725849228837269689763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651150566152558179793175 27976725849228837269689763)
        ·
          refine ⟨41965088773843255904534645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27976725849228837269689763 41965088773843255904534645)
          ·
            refine ⟨3934227072547805241050123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41965088773843255904534645 3934227072547805241050123)
            ·
              refine ⟨5901340608821707861575185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934227072547805241050123 5901340608821707861575185)
              ·
                refine ⟨4426005456616280896181389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901340608821707861575185 4426005456616280896181389)
                ·
                  refine ⟨1659752046231105336068021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4426005456616280896181389 1659752046231105336068021)
                  ·
                    refine ⟨155601754334166125256377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1659752046231105336068021 155601754334166125256377)
                    ·
                      rfl

theorem cell23_909100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_909100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909100 prefixEnd_909100 := by exact prefixLift 909100
  have htrace : WordTrace (prefixWord ++ tailWord_909100) baseStart_909100 baseEnd_909100 := by
    simpa [prefixWord, tailWord_909100, baseEnd_909100] using wordTrace_append hprefix tailTrace_909100
  have hstable : (prefixWord ++ tailWord_909100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909100).length < 2 ^ (prefixWord ++ tailWord_909100).sum := by decide
  have hdescent : baseEnd_909100 < baseStart_909100 := by decide
  rcases family_descends (prefixWord ++ tailWord_909100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909114 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_909114 : Nat := 118140960795 + 909114 * 2 ^ 59
def prefixEnd_909114 : Nat := 4983230072969 + 3 ^ 40 * 909114 * 2
def baseEnd_909114 : Nat := 466812451731661320994067

theorem tailTrace_909114 : CollatzResearch.WordTrace tailWord_909114 prefixEnd_909114 466812451731661320994067 := by
  unfold tailWord_909114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289527907110679288771599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22105407752295144770057597 8289527907110679288771599)
  ·
    refine ⟨12434291860666018933157399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8289527907110679288771599 12434291860666018933157399)
    ·
      refine ⟨18651437790999028399736099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434291860666018933157399 18651437790999028399736099)
      ·
        refine ⟨27977156686498542599604149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651437790999028399736099 27977156686498542599604149)
        ·
          refine ⟨2622858439359238368712889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27977156686498542599604149 2622858439359238368712889)
          ·
            refine ⟨1967143829519428776534667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622858439359238368712889 1967143829519428776534667)
            ·
              refine ⟨2950715744279143164802001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967143829519428776534667 2950715744279143164802001)
              ·
                refine ⟨2213036808209357373601501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950715744279143164802001 2213036808209357373601501)
                ·
                  refine ⟨829888803078509015100563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2213036808209357373601501 829888803078509015100563)
                  ·
                    refine ⟨1244833204617763522650845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829888803078509015100563 1244833204617763522650845)
                    ·
                      refine ⟨466812451731661320994067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1244833204617763522650845 466812451731661320994067)
                      ·
                        rfl

theorem cell23_909114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_909114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909114 prefixEnd_909114 := by exact prefixLift 909114
  have htrace : WordTrace (prefixWord ++ tailWord_909114) baseStart_909114 baseEnd_909114 := by
    simpa [prefixWord, tailWord_909114, baseEnd_909114] using wordTrace_append hprefix tailTrace_909114
  have hstable : (prefixWord ++ tailWord_909114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909114).length < 2 ^ (prefixWord ++ tailWord_909114).sum := by decide
  have hdescent : baseEnd_909114 < baseStart_909114 := by decide
  rcases family_descends (prefixWord ++ tailWord_909114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909117 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_909117 : Nat := 118140960795 + 909117 * 2 ^ 59
def prefixEnd_909117 : Nat := 4983230072969 + 3 ^ 40 * 909117 * 2
def baseEnd_909117 : Nat := 155604664057874936418851

theorem tailTrace_909117 : CollatzResearch.WordTrace tailWord_909117 prefixEnd_909117 155604664057874936418851 := by
  unfold tailWord_909117
  simp only [CollatzResearch.WordTrace]
  refine ⟨33158221047431848667445605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22105480698287899111630403 33158221047431848667445605)
  ·
    refine ⟨6217166446393471625146051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33158221047431848667445605 6217166446393471625146051)
    ·
      refine ⟨9325749669590207437719077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6217166446393471625146051 9325749669590207437719077)
      ·
        refine ⟨1748578063048163894572327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9325749669590207437719077 1748578063048163894572327)
        ·
          refine ⟨2622867094572245841858491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748578063048163894572327 2622867094572245841858491)
          ·
            refine ⟨3934300641858368762787737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622867094572245841858491 3934300641858368762787737)
            ·
              refine ⟨2950725481393776572090803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934300641858368762787737 2950725481393776572090803)
              ·
                refine ⟨4426088222090664858136205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950725481393776572090803 4426088222090664858136205)
                ·
                  refine ⟨1659783083283999321801077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4426088222090664858136205 1659783083283999321801077)
                  ·
                    refine ⟨155604664057874936418851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1659783083283999321801077 155604664057874936418851)
                    ·
                      rfl

theorem cell23_909117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_909117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909117 prefixEnd_909117 := by exact prefixLift 909117
  have htrace : WordTrace (prefixWord ++ tailWord_909117) baseStart_909117 baseEnd_909117 := by
    simpa [prefixWord, tailWord_909117, baseEnd_909117] using wordTrace_append hprefix tailTrace_909117
  have hstable : (prefixWord ++ tailWord_909117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909117).length < 2 ^ (prefixWord ++ tailWord_909117).sum := by decide
  have hdescent : baseEnd_909117 < baseStart_909117 := by decide
  rcases family_descends (prefixWord ++ tailWord_909117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909130 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_909130 : Nat := 118140960795 + 909130 * 2 ^ 59
def prefixEnd_909130 : Nat := 4983230072969 + 3 ^ 40 * 909130 * 2
def baseEnd_909130 : Nat := 155606889140711086131331

theorem tailTrace_909130 : CollatzResearch.WordTrace tailWord_909130 prefixEnd_909130 155606889140711086131331 := by
  unfold tailWord_909130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289673799096187971917211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22105796797589834591779229 8289673799096187971917211)
  ·
    refine ⟨12434510698644281957875817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8289673799096187971917211 12434510698644281957875817)
    ·
      refine ⟨9325883023983211468406863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12434510698644281957875817 9325883023983211468406863)
      ·
        refine ⟨13988824535974817202610295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9325883023983211468406863 13988824535974817202610295)
        ·
          refine ⟨20983236803962225803915443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13988824535974817202610295 20983236803962225803915443)
          ·
            refine ⟨31474855205943338705873165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20983236803962225803915443 31474855205943338705873165)
            ·
              refine ⟨11803070702228752014702437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31474855205943338705873165 11803070702228752014702437)
              ·
                refine ⟨2213075756667891002756707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11803070702228752014702437 2213075756667891002756707)
                ·
                  refine ⟨3319613635001836504135061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213075756667891002756707 3319613635001836504135061)
                  ·
                    refine ⟨155606889140711086131331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3319613635001836504135061 155606889140711086131331)
                    ·
                      rfl

theorem cell23_909130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_909130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909130 prefixEnd_909130 := by exact prefixLift 909130
  have htrace : WordTrace (prefixWord ++ tailWord_909130) baseStart_909130 baseEnd_909130 := by
    simpa [prefixWord, tailWord_909130, baseEnd_909130] using wordTrace_append hprefix tailTrace_909130
  have hstable : (prefixWord ++ tailWord_909130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909130).length < 2 ^ (prefixWord ++ tailWord_909130).sum := by decide
  have hdescent : baseEnd_909130 < baseStart_909130 := by decide
  rcases family_descends (prefixWord ++ tailWord_909130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909160 : List Nat := [2, 1, 4, 2, 1, 1, 2, 10]
def baseStart_909160 : Nat := 118140960795 + 909160 * 2 ^ 59
def prefixEnd_909160 : Nat := 4983230072969 + 3 ^ 40 * 909160 * 2
def baseEnd_909160 : Nat := 17290224883028449667365

theorem tailTrace_909160 : CollatzResearch.WordTrace tailWord_909160 prefixEnd_909160 17290224883028449667365 := by
  unfold tailWord_909160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579894693138033505630467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22106526257517378007507289 16579894693138033505630467)
  ·
    refine ⟨24869842039707050258445701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16579894693138033505630467 24869842039707050258445701)
    ·
      refine ⟨4663095382445071923458569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24869842039707050258445701 4663095382445071923458569)
      ·
        refine ⟨3497321536833803942593927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4663095382445071923458569 3497321536833803942593927)
        ·
          refine ⟨5245982305250705913890891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497321536833803942593927 5245982305250705913890891)
          ·
            refine ⟨7868973457876058870836337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245982305250705913890891 7868973457876058870836337)
            ·
              refine ⟨5901730093407044153127253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7868973457876058870836337 5901730093407044153127253)
              ·
                refine ⟨17290224883028449667365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5901730093407044153127253 17290224883028449667365)
                ·
                  rfl

theorem cell23_909160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 10].length) (baseStart_909160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909160 prefixEnd_909160 := by exact prefixLift 909160
  have htrace : WordTrace (prefixWord ++ tailWord_909160) baseStart_909160 baseEnd_909160 := by
    simpa [prefixWord, tailWord_909160, baseEnd_909160] using wordTrace_append hprefix tailTrace_909160
  have hstable : (prefixWord ++ tailWord_909160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909160).length < 2 ^ (prefixWord ++ tailWord_909160).sum := by decide
  have hdescent : baseEnd_909160 < baseStart_909160 := by decide
  rcases family_descends (prefixWord ++ tailWord_909160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909188 : List Nat := [2, 3, 2, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_909188 : Nat := 118140960795 + 909188 * 2 ^ 59
def prefixEnd_909188 : Nat := 4983230072969 + 3 ^ 40 * 909188 * 2
def baseEnd_909188 : Nat := 466850449300094031468727

theorem tailTrace_909188 : CollatzResearch.WordTrace tailWord_909188 prefixEnd_909188 466850449300094031468727 := by
  unfold tailWord_909188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580405315087313896640109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22107207086783085195520145 16580405315087313896640109)
  ·
    refine ⟨6217651993157742711240041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16580405315087313896640109 6217651993157742711240041)
    ·
      refine ⟨4663238994868307033430031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6217651993157742711240041 4663238994868307033430031)
      ·
        refine ⟨6994858492302460550145047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663238994868307033430031 6994858492302460550145047)
        ·
          refine ⟨10492287738453690825217571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994858492302460550145047 10492287738453690825217571)
          ·
            refine ⟨15738431607680536237826357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492287738453690825217571 15738431607680536237826357)
            ·
              refine ⟨1475477963220050272296221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15738431607680536237826357 1475477963220050272296221)
              ·
                refine ⟨553304236207518852111083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1475477963220050272296221 553304236207518852111083)
                ·
                  refine ⟨829956354311278278166625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553304236207518852111083 829956354311278278166625)
                  ·
                    refine ⟨622467265733458708624969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 829956354311278278166625 622467265733458708624969)
                    ·
                      refine ⟨466850449300094031468727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622467265733458708624969 466850449300094031468727)
                      ·
                        rfl

theorem cell23_909188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_909188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909188 prefixEnd_909188 := by exact prefixLift 909188
  have htrace : WordTrace (prefixWord ++ tailWord_909188) baseStart_909188 baseEnd_909188 := by
    simpa [prefixWord, tailWord_909188, baseEnd_909188] using wordTrace_append hprefix tailTrace_909188
  have hstable : (prefixWord ++ tailWord_909188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909188).length < 2 ^ (prefixWord ++ tailWord_909188).sum := by decide
  have hdescent : baseEnd_909188 < baseStart_909188 := by decide
  rcases family_descends (prefixWord ++ tailWord_909188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909194 : List Nat := [3, 1, 2, 4, 3, 1, 9]
def baseStart_909194 : Nat := 118140960795 + 909194 * 2 ^ 59
def prefixEnd_909194 : Nat := 4983230072969 + 3 ^ 40 * 909194 * 2
def baseEnd_909194 : Nat := 5763623829432358123379

theorem tailTrace_909194 : CollatzResearch.WordTrace tailWord_909194 prefixEnd_909194 5763623829432358123379 := by
  unfold tailWord_909194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290257367038222704499659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22107352978768593878665757 8290257367038222704499659)
  ·
    refine ⟨12435386050557334056749489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8290257367038222704499659 12435386050557334056749489)
    ·
      refine ⟨9326539537918000542562117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12435386050557334056749489 9326539537918000542562117)
      ·
        refine ⟨1748726163359625101730397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9326539537918000542562117 1748726163359625101730397)
        ·
          refine ⟨655772311259859413148899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1748726163359625101730397 655772311259859413148899)
          ·
            refine ⟨983658466889789119723349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655772311259859413148899 983658466889789119723349)
            ·
              refine ⟨5763623829432358123379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 983658466889789119723349 5763623829432358123379)
              ·
                rfl

theorem cell23_909194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 9].length) (baseStart_909194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909194 prefixEnd_909194 := by exact prefixLift 909194
  have htrace : WordTrace (prefixWord ++ tailWord_909194) baseStart_909194 baseEnd_909194 := by
    simpa [prefixWord, tailWord_909194, baseEnd_909194] using wordTrace_append hprefix tailTrace_909194
  have hstable : (prefixWord ++ tailWord_909194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909194).length < 2 ^ (prefixWord ++ tailWord_909194).sum := by decide
  have hdescent : baseEnd_909194 < baseStart_909194 := by decide
  rcases family_descends (prefixWord ++ tailWord_909194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909274 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_909274 : Nat := 118140960795 + 909274 * 2 ^ 59
def prefixEnd_909274 : Nat := 4983230072969 + 3 ^ 40 * 909274 * 2
def baseEnd_909274 : Nat := 466894608636380694993331

theorem tailTrace_909274 : CollatzResearch.WordTrace tailWord_909274 prefixEnd_909274 466894608636380694993331 := by
  unfold tailWord_909274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290986826965766120227719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22109298205242042987273917 8290986826965766120227719)
  ·
    refine ⟨12436480240448649180341579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8290986826965766120227719 12436480240448649180341579)
    ·
      refine ⟨18654720360672973770512369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12436480240448649180341579 18654720360672973770512369)
      ·
        refine ⟨13991040270504730327884277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18654720360672973770512369 13991040270504730327884277)
        ·
          refine ⟨1311660025359818468239151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13991040270504730327884277 1311660025359818468239151)
          ·
            refine ⟨1967490038039727702358727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311660025359818468239151 1967490038039727702358727)
            ·
              refine ⟨2951235057059591553538091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967490038039727702358727 2951235057059591553538091)
              ·
                refine ⟨4426852585589387330307137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951235057059591553538091 4426852585589387330307137)
                ·
                  refine ⟨3320139439192040497730353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4426852585589387330307137 3320139439192040497730353)
                  ·
                    refine ⟨2490104579394030373297765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320139439192040497730353 2490104579394030373297765)
                    ·
                      refine ⟨466894608636380694993331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2490104579394030373297765 466894608636380694993331)
                      ·
                        rfl

theorem cell23_909274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_909274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909274 prefixEnd_909274 := by exact prefixLift 909274
  have htrace : WordTrace (prefixWord ++ tailWord_909274) baseStart_909274 baseEnd_909274 := by
    simpa [prefixWord, tailWord_909274, baseEnd_909274] using wordTrace_append hprefix tailTrace_909274
  have hstable : (prefixWord ++ tailWord_909274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909274).length < 2 ^ (prefixWord ++ tailWord_909274).sum := by decide
  have hdescent : baseEnd_909274 < baseStart_909274 := by decide
  rcases family_descends (prefixWord ++ tailWord_909274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909347 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4]
def baseStart_909347 : Nat := 118140960795 + 909347 * 2 ^ 59
def prefixEnd_909347 : Nat := 4983230072969 + 3 ^ 40 * 909347 * 2
def baseEnd_909347 : Nat := 466932092724158909380495

theorem tailTrace_909347 : CollatzResearch.WordTrace tailWord_909347 prefixEnd_909347 466932092724158909380495 := by
  unfold tailWord_909347
  simp only [CollatzResearch.WordTrace]
  refine ⟨33166609836598597948318295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22111073224399065298878863 33166609836598597948318295)
  ·
    refine ⟨49749914754897896922477443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33166609836598597948318295 49749914754897896922477443)
    ·
      refine ⟨74624872132346845383716165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49749914754897896922477443 74624872132346845383716165)
      ·
        refine ⟨13992163524815033509446781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74624872132346845383716165 13992163524815033509446781)
        ·
          refine ⟨5247061321805637566042543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13992163524815033509446781 5247061321805637566042543)
          ·
            refine ⟨7870591982708456349063815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247061321805637566042543 7870591982708456349063815)
            ·
              refine ⟨11805887974062684523595723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7870591982708456349063815 11805887974062684523595723)
              ·
                refine ⟨17708831961094026785393585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11805887974062684523595723 17708831961094026785393585)
                ·
                  refine ⟨13281623970820520089045189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17708831961094026785393585 13281623970820520089045189)
                  ·
                    refine ⟨2490304494528847516695973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13281623970820520089045189 2490304494528847516695973)
                    ·
                      refine ⟨466932092724158909380495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2490304494528847516695973 466932092724158909380495)
                      ·
                        rfl

theorem cell23_909347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_909347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909347 prefixEnd_909347 := by exact prefixLift 909347
  have htrace : WordTrace (prefixWord ++ tailWord_909347) baseStart_909347 baseEnd_909347 := by
    simpa [prefixWord, tailWord_909347, baseEnd_909347] using wordTrace_append hprefix tailTrace_909347
  have hstable : (prefixWord ++ tailWord_909347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909347).length < 2 ^ (prefixWord ++ tailWord_909347).sum := by decide
  have hdescent : baseEnd_909347 < baseStart_909347 := by decide
  rcases family_descends (prefixWord ++ tailWord_909347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909387 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 5, 5]
def baseStart_909387 : Nat := 118140960795 + 909387 * 2 ^ 59
def prefixEnd_909387 : Nat := 4983230072969 + 3 ^ 40 * 909387 * 2
def baseEnd_909387 : Nat := 155650877316779584293437

theorem tailTrace_909387 : CollatzResearch.WordTrace tailWord_909387 prefixEnd_909387 155650877316779584293437 := by
  unfold tailWord_909387
  simp only [CollatzResearch.WordTrace]
  refine ⟨33168068756453684779774415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22112045837635789853182943 33168068756453684779774415)
  ·
    refine ⟨49752103134680527169661623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33168068756453684779774415 49752103134680527169661623)
    ·
      refine ⟨74628154702020790754492435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49752103134680527169661623 74628154702020790754492435)
      ·
        refine ⟨111942232053031186131738653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74628154702020790754492435 111942232053031186131738653)
        ·
          refine ⟨41978337019886694799401995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111942232053031186131738653 41978337019886694799401995)
          ·
            refine ⟨62967505529830042199102993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41978337019886694799401995 62967505529830042199102993)
            ·
              refine ⟨47225629147372531649327245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62967505529830042199102993 47225629147372531649327245)
              ·
                refine ⟨17709610930264699368497717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47225629147372531649327245 17709610930264699368497717)
                ·
                  refine ⟨1660276024712315565796661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17709610930264699368497717 1660276024712315565796661)
                  ·
                    refine ⟨155650877316779584293437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1660276024712315565796661 155650877316779584293437)
                    ·
                      rfl

theorem cell23_909387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 5].length) (baseStart_909387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909387 prefixEnd_909387 := by exact prefixLift 909387
  have htrace : WordTrace (prefixWord ++ tailWord_909387) baseStart_909387 baseEnd_909387 := by
    simpa [prefixWord, tailWord_909387, baseEnd_909387] using wordTrace_append hprefix tailTrace_909387
  have hstable : (prefixWord ++ tailWord_909387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909387).length < 2 ^ (prefixWord ++ tailWord_909387).sum := by decide
  have hdescent : baseEnd_909387 < baseStart_909387 := by decide
  rcases family_descends (prefixWord ++ tailWord_909387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909411 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 2, 3, 2]
def baseStart_909411 : Nat := 118140960795 + 909411 * 2 ^ 59
def prefixEnd_909411 : Nat := 4983230072969 + 3 ^ 40 * 909411 * 2
def baseEnd_909411 : Nat := 466964955486046658980201

theorem tailTrace_909411 : CollatzResearch.WordTrace tailWord_909411 prefixEnd_909411 466964955486046658980201 := by
  unfold tailWord_909411
  simp only [CollatzResearch.WordTrace]
  refine ⟨33168944108366736878648087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22112629405577824585765391 33168944108366736878648087)
  ·
    refine ⟨49753416162550105317972131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33168944108366736878648087 49753416162550105317972131)
    ·
      refine ⟨74630124243825157976958197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49753416162550105317972131 74630124243825157976958197)
      ·
        refine ⟨6996574147858608560339831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74630124243825157976958197 6996574147858608560339831)
        ·
          refine ⟨10494861221787912840509747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6996574147858608560339831 10494861221787912840509747)
          ·
            refine ⟨15742291832681869260764621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10494861221787912840509747 15742291832681869260764621)
            ·
              refine ⟨5903359437255700972786733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15742291832681869260764621 5903359437255700972786733)
              ·
                refine ⟨2213759788970887864795025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5903359437255700972786733 2213759788970887864795025)
                ·
                  refine ⟨1660319841728165898596269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2213759788970887864795025 1660319841728165898596269)
                  ·
                    refine ⟨622619940648062211973601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660319841728165898596269 622619940648062211973601)
                    ·
                      refine ⟨466964955486046658980201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622619940648062211973601 466964955486046658980201)
                      ·
                        rfl

theorem cell23_909411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_909411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909411 prefixEnd_909411 := by exact prefixLift 909411
  have htrace : WordTrace (prefixWord ++ tailWord_909411) baseStart_909411 baseEnd_909411 := by
    simpa [prefixWord, tailWord_909411, baseEnd_909411] using wordTrace_append hprefix tailTrace_909411
  have hstable : (prefixWord ++ tailWord_909411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909411).length < 2 ^ (prefixWord ++ tailWord_909411).sum := by decide
  have hdescent : baseEnd_909411 < baseStart_909411 := by decide
  rcases family_descends (prefixWord ++ tailWord_909411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909444 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_909444 : Nat := 118140960795 + 909444 * 2 ^ 59
def prefixEnd_909444 : Nat := 4983230072969 + 3 ^ 40 * 909444 * 2
def baseEnd_909444 : Nat := 466981900347645029867549

theorem tailTrace_909444 : CollatzResearch.WordTrace tailWord_909444 prefixEnd_909444 466981900347645029867549 := by
  unfold tailWord_909444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16585073858623591757299693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22113431811498122343066257 16585073858623591757299693)
  ·
    refine ⟨6219402696983846908987385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16585073858623591757299693 6219402696983846908987385)
    ·
      refine ⟨4664552022737885181740539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6219402696983846908987385 4664552022737885181740539)
      ·
        refine ⟨6996828034106827772610809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4664552022737885181740539 6996828034106827772610809)
        ·
          refine ⟨5247621025580120829458107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6996828034106827772610809 5247621025580120829458107)
          ·
            refine ⟨7871431538370181244187161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247621025580120829458107 7871431538370181244187161)
            ·
              refine ⟨5903573653777635933140371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7871431538370181244187161 5903573653777635933140371)
              ·
                refine ⟨8855360480666453899710557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903573653777635933140371 8855360480666453899710557)
                ·
                  refine ⟨3320760180249920212391459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8855360480666453899710557 3320760180249920212391459)
                  ·
                    refine ⟨4981140270374880318587189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3320760180249920212391459 4981140270374880318587189)
                    ·
                      refine ⟨466981900347645029867549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4981140270374880318587189 466981900347645029867549)
                      ·
                        rfl

theorem cell23_909444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_909444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909444 prefixEnd_909444 := by exact prefixLift 909444
  have htrace : WordTrace (prefixWord ++ tailWord_909444) baseStart_909444 baseEnd_909444 := by
    simpa [prefixWord, tailWord_909444, baseEnd_909444] using wordTrace_append hprefix tailTrace_909444
  have hstable : (prefixWord ++ tailWord_909444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909444).length < 2 ^ (prefixWord ++ tailWord_909444).sum := by decide
  have hdescent : baseEnd_909444 < baseStart_909444 := by decide
  rcases family_descends (prefixWord ++ tailWord_909444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909457 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_909457 : Nat := 118140960795 + 909457 * 2 ^ 59
def prefixEnd_909457 : Nat := 4983230072969 + 3 ^ 40 * 909457 * 2
def baseEnd_909457 : Nat := 466988575596153479004989

theorem tailTrace_909457 : CollatzResearch.WordTrace tailWord_909457 prefixEnd_909457 466988575596153479004989 := by
  unfold tailWord_909457
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170621866200086734822625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22113747910800057823215083 33170621866200086734822625)
  ·
    refine ⟨24877966399650065051116969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33170621866200086734822625 24877966399650065051116969)
    ·
      refine ⟨18658474799737548788337727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24877966399650065051116969 18658474799737548788337727)
      ·
        refine ⟨27987712199606323182506591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18658474799737548788337727 27987712199606323182506591)
        ·
          refine ⟨41981568299409484773759887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27987712199606323182506591 41981568299409484773759887)
          ·
            refine ⟨62972352449114227160639831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41981568299409484773759887 62972352449114227160639831)
            ·
              refine ⟨94458528673671340740959747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62972352449114227160639831 94458528673671340740959747)
              ·
                refine ⟨141687793010507011111439621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94458528673671340740959747 141687793010507011111439621)
                ·
                  refine ⟨26566461189470064583394929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141687793010507011111439621 26566461189470064583394929)
                  ·
                    refine ⟨19924845892102548437546197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26566461189470064583394929 19924845892102548437546197)
                    ·
                      refine ⟨466988575596153479004989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19924845892102548437546197 466988575596153479004989)
                      ·
                        rfl

theorem cell23_909457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_909457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909457 prefixEnd_909457 := by exact prefixLift 909457
  have htrace : WordTrace (prefixWord ++ tailWord_909457) baseStart_909457 baseEnd_909457 := by
    simpa [prefixWord, tailWord_909457, baseEnd_909457] using wordTrace_append hprefix tailTrace_909457
  have hstable : (prefixWord ++ tailWord_909457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909457).length < 2 ^ (prefixWord ++ tailWord_909457).sum := by decide
  have hdescent : baseEnd_909457 < baseStart_909457 := by decide
  rcases family_descends (prefixWord ++ tailWord_909457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909461 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_909461 : Nat := 118140960795 + 909461 * 2 ^ 59
def prefixEnd_909461 : Nat := 4983230072969 + 3 ^ 40 * 909461 * 2
def baseEnd_909461 : Nat := 466990629518771463354971

theorem tailTrace_909461 : CollatzResearch.WordTrace tailWord_909461 prefixEnd_909461 466990629518771463354971 := by
  unfold tailWord_909461
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170767758185595417968237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22113845172123730278645491 33170767758185595417968237)
  ·
    refine ⟨12439037909319598281738089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33170767758185595417968237 12439037909319598281738089)
    ·
      refine ⟨9329278431989698711303567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12439037909319598281738089 9329278431989698711303567)
      ·
        refine ⟨13993917647984548066955351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329278431989698711303567 13993917647984548066955351)
        ·
          refine ⟨20990876471976822100433027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13993917647984548066955351 20990876471976822100433027)
          ·
            refine ⟨31486314707965233150649541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20990876471976822100433027 31486314707965233150649541)
            ·
              refine ⟨5903684007743481215746789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31486314707965233150649541 5903684007743481215746789)
              ·
                refine ⟨1106940751451902727952523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5903684007743481215746789 1106940751451902727952523)
                ·
                  refine ⟨1660411127177854091928785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106940751451902727952523 1660411127177854091928785)
                  ·
                    refine ⟨1245308345383390568946589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1660411127177854091928785 1245308345383390568946589)
                    ·
                      refine ⟨466990629518771463354971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1245308345383390568946589 466990629518771463354971)
                      ·
                        rfl

theorem cell23_909461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_909461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909461 prefixEnd_909461 := by exact prefixLift 909461
  have htrace : WordTrace (prefixWord ++ tailWord_909461) baseStart_909461 baseEnd_909461 := by
    simpa [prefixWord, tailWord_909461, baseEnd_909461] using wordTrace_append hprefix tailTrace_909461
  have hstable : (prefixWord ++ tailWord_909461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909461).length < 2 ^ (prefixWord ++ tailWord_909461).sum := by decide
  have hdescent : baseEnd_909461 < baseStart_909461 := by decide
  rcases family_descends (prefixWord ++ tailWord_909461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909467 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6]
def baseStart_909467 : Nat := 118140960795 + 909467 * 2 ^ 59
def prefixEnd_909467 : Nat := 4983230072969 + 3 ^ 40 * 909467 * 2
def baseEnd_909467 : Nat := 466993710402698439879943

theorem tailTrace_909467 : CollatzResearch.WordTrace tailWord_909467 prefixEnd_909467 466993710402698439879943 := by
  unfold tailWord_909467
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170986596163858442686655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22113991064109238961791103 33170986596163858442686655)
  ·
    refine ⟨49756479894245787664029983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33170986596163858442686655 49756479894245787664029983)
    ·
      refine ⟨74634719841368681496044975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49756479894245787664029983 74634719841368681496044975)
      ·
        refine ⟨111952079762053022244067463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74634719841368681496044975 111952079762053022244067463)
        ·
          refine ⟨167928119643079533366101195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111952079762053022244067463 167928119643079533366101195)
          ·
            refine ⟨251892179464619300049151793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167928119643079533366101195 251892179464619300049151793)
            ·
              refine ⟨188919134598464475036863845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251892179464619300049151793 188919134598464475036863845)
              ·
                refine ⟨35422337737212089069411971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188919134598464475036863845 35422337737212089069411971)
                ·
                  refine ⟨53133506605818133604117957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35422337737212089069411971 53133506605818133604117957)
                  ·
                    refine ⟨9962532488590900050772117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53133506605818133604117957 9962532488590900050772117)
                    ·
                      refine ⟨466993710402698439879943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9962532488590900050772117 466993710402698439879943)
                      ·
                        rfl

theorem cell23_909467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_909467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909467 prefixEnd_909467 := by exact prefixLift 909467
  have htrace : WordTrace (prefixWord ++ tailWord_909467) baseStart_909467 baseEnd_909467 := by
    simpa [prefixWord, tailWord_909467, baseEnd_909467] using wordTrace_append hprefix tailTrace_909467
  have hstable : (prefixWord ++ tailWord_909467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909467).length < 2 ^ (prefixWord ++ tailWord_909467).sum := by decide
  have hdescent : baseEnd_909467 < baseStart_909467 := by decide
  rcases family_descends (prefixWord ++ tailWord_909467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909471 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_909471 : Nat := 118140960795 + 909471 * 2 ^ 59
def prefixEnd_909471 : Nat := 4983230072969 + 3 ^ 40 * 909471 * 2
def baseEnd_909471 : Nat := 466995764325316424229925

theorem tailTrace_909471 : CollatzResearch.WordTrace tailWord_909471 prefixEnd_909471 466995764325316424229925 := by
  unfold tailWord_909471
  simp only [CollatzResearch.WordTrace]
  refine ⟨33171132488149367125832267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22114088325432911417221511 33171132488149367125832267)
  ·
    refine ⟨49756698732224050688748401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33171132488149367125832267 49756698732224050688748401)
    ·
      refine ⟨37317524049168038016561301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49756698732224050688748401 37317524049168038016561301)
      ·
        refine ⟨1749258939804751782026311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37317524049168038016561301 1749258939804751782026311)
        ·
          refine ⟨2623888409707127673039467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749258939804751782026311 2623888409707127673039467)
          ·
            refine ⟨3935832614560691509559201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623888409707127673039467 3935832614560691509559201)
            ·
              refine ⟨2951874460920518632169401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3935832614560691509559201 2951874460920518632169401)
              ·
                refine ⟨2213905845690388974127051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2951874460920518632169401 2213905845690388974127051)
                ·
                  refine ⟨3320858768535583461190577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213905845690388974127051 3320858768535583461190577)
                  ·
                    refine ⟨2490644076401687595892933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320858768535583461190577 2490644076401687595892933)
                    ·
                      refine ⟨466995764325316424229925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2490644076401687595892933 466995764325316424229925)
                      ·
                        rfl

theorem cell23_909471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_909471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909471 prefixEnd_909471 := by exact prefixLift 909471
  have htrace : WordTrace (prefixWord ++ tailWord_909471) baseStart_909471 baseEnd_909471 := by
    simpa [prefixWord, tailWord_909471, baseEnd_909471] using wordTrace_append hprefix tailTrace_909471
  have hstable : (prefixWord ++ tailWord_909471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909471).length < 2 ^ (prefixWord ++ tailWord_909471).sum := by decide
  have hdescent : baseEnd_909471 < baseStart_909471 := by decide
  rcases family_descends (prefixWord ++ tailWord_909471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909485 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_909485 : Nat := 118140960795 + 909485 * 2 ^ 59
def prefixEnd_909485 : Nat := 4983230072969 + 3 ^ 40 * 909485 * 2
def baseEnd_909485 : Nat := 155667651018159789818287

theorem tailTrace_909485 : CollatzResearch.WordTrace tailWord_909485 prefixEnd_909485 155667651018159789818287 := by
  unfold tailWord_909485
  simp only [CollatzResearch.WordTrace]
  refine ⟨33171643110098647516841909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22114428740065765011227939 33171643110098647516841909)
  ·
    refine ⟨3109841541571748204703929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33171643110098647516841909 3109841541571748204703929)
    ·
      refine ⟨2332381156178811153527947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3109841541571748204703929 2332381156178811153527947)
      ·
        refine ⟨3498571734268216730291921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332381156178811153527947 3498571734268216730291921)
        ·
          refine ⟨2623928800701162547718941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3498571734268216730291921 2623928800701162547718941)
          ·
            refine ⟨983973300262935955394603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2623928800701162547718941 983973300262935955394603)
            ·
              refine ⟨1475959950394403933091905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983973300262935955394603 1475959950394403933091905)
              ·
                refine ⟨1106969962795802949818929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475959950394403933091905 1106969962795802949818929)
                ·
                  refine ⟨830227472096852212364197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1106969962795802949818929 830227472096852212364197)
                  ·
                    refine ⟨155667651018159789818287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830227472096852212364197 155667651018159789818287)
                    ·
                      rfl

theorem cell23_909485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_909485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909485 prefixEnd_909485 := by exact prefixLift 909485
  have htrace : WordTrace (prefixWord ++ tailWord_909485) baseStart_909485 baseEnd_909485 := by
    simpa [prefixWord, tailWord_909485, baseEnd_909485] using wordTrace_append hprefix tailTrace_909485
  have hstable : (prefixWord ++ tailWord_909485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909485).length < 2 ^ (prefixWord ++ tailWord_909485).sum := by decide
  have hdescent : baseEnd_909485 < baseStart_909485 := by decide
  rcases family_descends (prefixWord ++ tailWord_909485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909505 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_909505 : Nat := 118140960795 + 909505 * 2 ^ 59
def prefixEnd_909505 : Nat := 4983230072969 + 3 ^ 40 * 909505 * 2
def baseEnd_909505 : Nat := 467013222667569291204769

theorem tailTrace_909505 : CollatzResearch.WordTrace tailWord_909505 prefixEnd_909505 467013222667569291204769 := by
  unfold tailWord_909505
  simp only [CollatzResearch.WordTrace]
  refine ⟨33172372570026190932569969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22114915046684127288379979 33172372570026190932569969)
  ·
    refine ⟨24879279427519643199427477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33172372570026190932569969 24879279427519643199427477)
    ·
      refine ⟨1166216223164983274973163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24879279427519643199427477 1166216223164983274973163)
      ·
        refine ⟨1749324334747474912459745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166216223164983274973163 1749324334747474912459745)
        ·
          refine ⟨1311993251060606184344809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749324334747474912459745 1311993251060606184344809)
          ·
            refine ⟨983994938295454638258607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1311993251060606184344809 983994938295454638258607)
            ·
              refine ⟨1475992407443181957387911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983994938295454638258607 1475992407443181957387911)
              ·
                refine ⟨2213988611164772936081867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475992407443181957387911 2213988611164772936081867)
                ·
                  refine ⟨3320982916747159404122801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213988611164772936081867 3320982916747159404122801)
                  ·
                    refine ⟨2490737187560369553092101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320982916747159404122801 2490737187560369553092101)
                    ·
                      refine ⟨467013222667569291204769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2490737187560369553092101 467013222667569291204769)
                      ·
                        rfl

theorem cell23_909505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_909505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909505 prefixEnd_909505 := by exact prefixLift 909505
  have htrace : WordTrace (prefixWord ++ tailWord_909505) baseStart_909505 baseEnd_909505 := by
    simpa [prefixWord, tailWord_909505, baseEnd_909505] using wordTrace_append hprefix tailTrace_909505
  have hstable : (prefixWord ++ tailWord_909505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909505).length < 2 ^ (prefixWord ++ tailWord_909505).sum := by decide
  have hdescent : baseEnd_909505 < baseStart_909505 := by decide
  rcases family_descends (prefixWord ++ tailWord_909505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909508 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_909508 : Nat := 118140960795 + 909508 * 2 ^ 59
def prefixEnd_909508 : Nat := 4983230072969 + 3 ^ 40 * 909508 * 2
def baseEnd_909508 : Nat := 467014763109532779467255

theorem tailTrace_909508 : CollatzResearch.WordTrace tailWord_909508 prefixEnd_909508 467014763109532779467255 := by
  unfold tailWord_909508
  simp only [CollatzResearch.WordTrace]
  refine ⟨16586240994507661222464589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22114987992676881629952785 16586240994507661222464589)
  ·
    refine ⟨6219840372940372958424221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16586240994507661222464589 6219840372940372958424221)
    ·
      refine ⟨2332440139852639859409083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6219840372940372958424221 2332440139852639859409083)
      ·
        refine ⟨3498660209778959789113625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332440139852639859409083 3498660209778959789113625)
        ·
          refine ⟨2623995157334219841835219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3498660209778959789113625 2623995157334219841835219)
          ·
            refine ⟨3935992736001329762752829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623995157334219841835219 3935992736001329762752829)
            ·
              refine ⟨1475997276000498661032311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3935992736001329762752829 1475997276000498661032311)
              ·
                refine ⟨2213995914000747991548467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475997276000498661032311 2213995914000747991548467)
                ·
                  refine ⟨3320993871001121987322701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213995914000747991548467 3320993871001121987322701)
                  ·
                    refine ⟨1245372701625420745246013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320993871001121987322701 1245372701625420745246013)
                    ·
                      refine ⟨467014763109532779467255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1245372701625420745246013 467014763109532779467255)
                      ·
                        rfl

theorem cell23_909508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_909508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909508 prefixEnd_909508 := by exact prefixLift 909508
  have htrace : WordTrace (prefixWord ++ tailWord_909508) baseStart_909508 baseEnd_909508 := by
    simpa [prefixWord, tailWord_909508, baseEnd_909508] using wordTrace_append hprefix tailTrace_909508
  have hstable : (prefixWord ++ tailWord_909508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909508).length < 2 ^ (prefixWord ++ tailWord_909508).sum := by decide
  have hdescent : baseEnd_909508 < baseStart_909508 := by decide
  rcases family_descends (prefixWord ++ tailWord_909508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909526 : List Nat := [5, 2, 1, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_909526 : Nat := 118140960795 + 909526 * 2 ^ 59
def prefixEnd_909526 : Nat := 4983230072969 + 3 ^ 40 * 909526 * 2
def baseEnd_909526 : Nat := 467024005761313709042173

theorem tailTrace_909526 : CollatzResearch.WordTrace tailWord_909526 prefixEnd_909526 467024005761313709042173 := by
  unfold tailWord_909526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073321156434381969942777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22115425668633407679389621 2073321156434381969942777)
  ·
    refine ⟨1554990867325786477457083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2073321156434381969942777 1554990867325786477457083)
    ·
      refine ⟨2332486300988679716185625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1554990867325786477457083 2332486300988679716185625)
      ·
        refine ⟨1749364725741509787139219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2332486300988679716185625 1749364725741509787139219)
        ·
          refine ⟨2624047088612264680708829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749364725741509787139219 2624047088612264680708829)
          ·
            refine ⟨984017658229599255265811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2624047088612264680708829 984017658229599255265811)
            ·
              refine ⟨1476026487344398882898717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984017658229599255265811 1476026487344398882898717)
              ·
                refine ⟨553509932754149581087019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1476026487344398882898717 553509932754149581087019)
                ·
                  refine ⟨830264899131224371630529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553509932754149581087019 830264899131224371630529)
                  ·
                    refine ⟨622698674348418278722897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 830264899131224371630529 622698674348418278722897)
                    ·
                      refine ⟨467024005761313709042173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622698674348418278722897 467024005761313709042173)
                      ·
                        rfl

theorem cell23_909526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_909526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909526 prefixEnd_909526 := by exact prefixLift 909526
  have htrace : WordTrace (prefixWord ++ tailWord_909526) baseStart_909526 baseEnd_909526 := by
    simpa [prefixWord, tailWord_909526, baseEnd_909526] using wordTrace_append hprefix tailTrace_909526
  have hstable : (prefixWord ++ tailWord_909526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909526).length < 2 ^ (prefixWord ++ tailWord_909526).sum := by decide
  have hdescent : baseEnd_909526 < baseStart_909526 := by decide
  rcases family_descends (prefixWord ++ tailWord_909526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909548 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 4, 2, 2]
def baseStart_909548 : Nat := 118140960795 + 909548 * 2 ^ 59
def prefixEnd_909548 : Nat := 4983230072969 + 3 ^ 40 * 909548 * 2
def baseEnd_909548 : Nat := 467035302335712622967071

theorem tailTrace_909548 : CollatzResearch.WordTrace tailWord_909548 prefixEnd_909548 467035302335712622967071 := by
  unfold tailWord_909548
  simp only [CollatzResearch.WordTrace]
  refine ⟨16586970454435204638192649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22115960605913606184256865 16586970454435204638192649)
  ·
    refine ⟨12440227840826403478644487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16586970454435204638192649 12440227840826403478644487)
    ·
      refine ⟨18660341761239605217966731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12440227840826403478644487 18660341761239605217966731)
      ·
        refine ⟨27990512641859407826950097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18660341761239605217966731 27990512641859407826950097)
        ·
          refine ⟨20992884481394555870212573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27990512641859407826950097 20992884481394555870212573)
          ·
            refine ⟨7872331680522958451329715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20992884481394555870212573 7872331680522958451329715)
            ·
              refine ⟨11808497520784437676994573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7872331680522958451329715 11808497520784437676994573)
              ·
                refine ⟨4428186570294164128872965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11808497520784437676994573 4428186570294164128872965)
                ·
                  refine ⟨830284981930155774163681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4428186570294164128872965 830284981930155774163681)
                  ·
                    refine ⟨622713736447616830622761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 830284981930155774163681 622713736447616830622761)
                    ·
                      refine ⟨467035302335712622967071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622713736447616830622761 467035302335712622967071)
                      ·
                        rfl

theorem cell23_909548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_909548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909548 prefixEnd_909548 := by exact prefixLift 909548
  have htrace : WordTrace (prefixWord ++ tailWord_909548) baseStart_909548 baseEnd_909548 := by
    simpa [prefixWord, tailWord_909548, baseEnd_909548] using wordTrace_append hprefix tailTrace_909548
  have hstable : (prefixWord ++ tailWord_909548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909548).length < 2 ^ (prefixWord ++ tailWord_909548).sum := by decide
  have hdescent : baseEnd_909548 < baseStart_909548 := by decide
  rcases family_descends (prefixWord ++ tailWord_909548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909601 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 2, 5]
def baseStart_909601 : Nat := 118140960795 + 909601 * 2 ^ 59
def prefixEnd_909601 : Nat := 4983230072969 + 3 ^ 40 * 909601 * 2
def baseEnd_909601 : Nat := 155687505603466971868109

theorem tailTrace_909601 : CollatzResearch.WordTrace tailWord_909601 prefixEnd_909601 155687505603466971868109 := by
  unfold tailWord_909601
  simp only [CollatzResearch.WordTrace]
  refine ⟨33175873977678399328064657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22117249318452266218709771 33175873977678399328064657)
  ·
    refine ⟨24881905483258799496048493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33175873977678399328064657 24881905483258799496048493)
    ·
      refine ⟨9330714556222049811018185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24881905483258799496048493 9330714556222049811018185)
      ·
        refine ⟨6998035917166537358263639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9330714556222049811018185 6998035917166537358263639)
        ·
          refine ⟨10497053875749806037395459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998035917166537358263639 10497053875749806037395459)
          ·
            refine ⟨15745580813624709056093189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497053875749806037395459 15745580813624709056093189)
            ·
              refine ⟨2952296402554632948017473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15745580813624709056093189 2952296402554632948017473)
              ·
                refine ⟨2214222301915974711013105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952296402554632948017473 2214222301915974711013105)
                ·
                  refine ⟨1660666726436981033259829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2214222301915974711013105 1660666726436981033259829)
                  ·
                    refine ⟨155687505603466971868109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1660666726436981033259829 155687505603466971868109)
                    ·
                      rfl

theorem cell23_909601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_909601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909601 prefixEnd_909601 := by exact prefixLift 909601
  have htrace : WordTrace (prefixWord ++ tailWord_909601) baseStart_909601 baseEnd_909601 := by
    simpa [prefixWord, tailWord_909601, baseEnd_909601] using wordTrace_append hprefix tailTrace_909601
  have hstable : (prefixWord ++ tailWord_909601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909601).length < 2 ^ (prefixWord ++ tailWord_909601).sum := by decide
  have hdescent : baseEnd_909601 < baseStart_909601 := by decide
  rcases family_descends (prefixWord ++ tailWord_909601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909621 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_909621 : Nat := 118140960795 + 909621 * 2 ^ 59
def prefixEnd_909621 : Nat := 4983230072969 + 3 ^ 40 * 909621 * 2
def baseEnd_909621 : Nat := 467072786423490837354235

theorem tailTrace_909621 : CollatzResearch.WordTrace tailWord_909621 prefixEnd_909621 467072786423490837354235 := by
  unfold tailWord_909621
  simp only [CollatzResearch.WordTrace]
  refine ⟨33176603437605942743792717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22117735625070628495861811 33176603437605942743792717)
  ·
    refine ⟨12441226289102228528922269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33176603437605942743792717 12441226289102228528922269)
    ·
      refine ⟨4665459858413335698345851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12441226289102228528922269 4665459858413335698345851)
      ·
        refine ⟨6998189787620003547518777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665459858413335698345851 6998189787620003547518777)
        ·
          refine ⟨5248642340715002660639083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6998189787620003547518777 5248642340715002660639083)
          ·
            refine ⟨7872963511072503990958625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248642340715002660639083 7872963511072503990958625)
            ·
              refine ⟨5904722633304377993218969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7872963511072503990958625 5904722633304377993218969)
              ·
                refine ⟨4428541974978283494914227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904722633304377993218969 4428541974978283494914227)
                ·
                  refine ⟨6642812962467425242371341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428541974978283494914227 6642812962467425242371341)
                  ·
                    refine ⟨2491054860925284465889253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6642812962467425242371341 2491054860925284465889253)
                    ·
                      refine ⟨467072786423490837354235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2491054860925284465889253 467072786423490837354235)
                      ·
                        rfl

theorem cell23_909621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_909621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909621 prefixEnd_909621 := by exact prefixLift 909621
  have htrace : WordTrace (prefixWord ++ tailWord_909621) baseStart_909621 baseEnd_909621 := by
    simpa [prefixWord, tailWord_909621, baseEnd_909621] using wordTrace_append hprefix tailTrace_909621
  have hstable : (prefixWord ++ tailWord_909621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909621).length < 2 ^ (prefixWord ++ tailWord_909621).sum := by decide
  have hdescent : baseEnd_909621 < baseStart_909621 := by decide
  rcases family_descends (prefixWord ++ tailWord_909621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909699 : List Nat := [1, 1, 1, 3, 7, 1, 1, 3, 1, 4]
def baseStart_909699 : Nat := 118140960795 + 909699 * 2 ^ 59
def prefixEnd_909699 : Nat := 4983230072969 + 3 ^ 40 * 909699 * 2
def baseEnd_909699 : Nat := 155704279304847177392959

theorem tailTrace_909699 : CollatzResearch.WordTrace tailWord_909699 prefixEnd_909699 155704279304847177392959 := by
  unfold tailWord_909699
  simp only [CollatzResearch.WordTrace]
  refine ⟨33179448331323362065132151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22119632220882241376754767 33179448331323362065132151)
  ·
    refine ⟨49769172496985043097698227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33179448331323362065132151 49769172496985043097698227)
    ·
      refine ⟨74653758745477564646547341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49769172496985043097698227 74653758745477564646547341)
      ·
        refine ⟨27995159529554086742455253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74653758745477564646547341 27995159529554086742455253)
        ·
          refine ⟨656136551473923908026295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27995159529554086742455253 656136551473923908026295)
          ·
            refine ⟨984204827210885862039443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656136551473923908026295 984204827210885862039443)
            ·
              refine ⟨1476307240816328793059165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984204827210885862039443 1476307240816328793059165)
              ·
                refine ⟨553615215306123297397187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1476307240816328793059165 553615215306123297397187)
                ·
                  refine ⟨830422822959184946095781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553615215306123297397187 830422822959184946095781)
                  ·
                    refine ⟨155704279304847177392959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830422822959184946095781 155704279304847177392959)
                    ·
                      rfl

theorem cell23_909699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 4].length) (baseStart_909699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909699 prefixEnd_909699 := by exact prefixLift 909699
  have htrace : WordTrace (prefixWord ++ tailWord_909699) baseStart_909699 baseEnd_909699 := by
    simpa [prefixWord, tailWord_909699, baseEnd_909699] using wordTrace_append hprefix tailTrace_909699
  have hstable : (prefixWord ++ tailWord_909699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909699).length < 2 ^ (prefixWord ++ tailWord_909699).sum := by decide
  have hdescent : baseEnd_909699 < baseStart_909699 := by decide
  rcases family_descends (prefixWord ++ tailWord_909699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909708 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_909708 : Nat := 118140960795 + 909708 * 2 ^ 59
def prefixEnd_909708 : Nat := 4983230072969 + 3 ^ 40 * 909708 * 2
def baseEnd_909708 : Nat := 155705819746810665655445

theorem tailTrace_909708 : CollatzResearch.WordTrace tailWord_909708 prefixEnd_909708 155705819746810665655445 := by
  unfold tailWord_909708
  simp only [CollatzResearch.WordTrace]
  refine ⟨16589888294145378301104889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22119851058860504401473185 16589888294145378301104889)
  ·
    refine ⟨12442416220609033725828667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16589888294145378301104889 12442416220609033725828667)
    ·
      refine ⟨18663624330913550588743001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12442416220609033725828667 18663624330913550588743001)
      ·
        refine ⟨13997718248185162941557251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18663624330913550588743001 13997718248185162941557251)
        ·
          refine ⟨20996577372277744412335877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13997718248185162941557251 20996577372277744412335877)
          ·
            refine ⟨3936858257302077077312977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20996577372277744412335877 3936858257302077077312977)
            ·
              refine ⟨2952643692976557807984733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3936858257302077077312977 2952643692976557807984733)
              ·
                refine ⟨1107241384866209177994275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2952643692976557807984733 1107241384866209177994275)
                ·
                  refine ⟨1660862077299313766991413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107241384866209177994275 1660862077299313766991413)
                  ·
                    refine ⟨155705819746810665655445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1660862077299313766991413 155705819746810665655445)
                    ·
                      rfl

theorem cell23_909708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_909708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909708 prefixEnd_909708 := by exact prefixLift 909708
  have htrace : WordTrace (prefixWord ++ tailWord_909708) baseStart_909708 baseEnd_909708 := by
    simpa [prefixWord, tailWord_909708, baseEnd_909708] using wordTrace_append hprefix tailTrace_909708
  have hstable : (prefixWord ++ tailWord_909708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909708).length < 2 ^ (prefixWord ++ tailWord_909708).sum := by decide
  have hdescent : baseEnd_909708 < baseStart_909708 := by decide
  rcases family_descends (prefixWord ++ tailWord_909708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909722 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_909722 : Nat := 118140960795 + 909722 * 2 ^ 59
def prefixEnd_909722 : Nat := 4983230072969 + 3 ^ 40 * 909722 * 2
def baseEnd_909722 : Nat := 467124647969594942191271

theorem tailTrace_909722 : CollatzResearch.WordTrace tailWord_909722 prefixEnd_909722 467124647969594942191271 := by
  unfold tailWord_909722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295071802560009248304855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22120191473493357995479613 8295071802560009248304855)
  ·
    refine ⟨12442607703840013872457283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8295071802560009248304855 12442607703840013872457283)
    ·
      refine ⟨18663911555760020808685925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12442607703840013872457283 18663911555760020808685925)
      ·
        refine ⟨3499483416705003901628611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18663911555760020808685925 3499483416705003901628611)
        ·
          refine ⟨5249225125057505852442917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499483416705003901628611 5249225125057505852442917)
          ·
            refine ⟨984229710948282347333047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5249225125057505852442917 984229710948282347333047)
            ·
              refine ⟨1476344566422423520999571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984229710948282347333047 1476344566422423520999571)
              ·
                refine ⟨2214516849633635281499357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476344566422423520999571 2214516849633635281499357)
                ·
                  refine ⟨830443818612613230562259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2214516849633635281499357 830443818612613230562259)
                  ·
                    refine ⟨1245665727918919845843389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 830443818612613230562259 1245665727918919845843389)
                    ·
                      refine ⟨467124647969594942191271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1245665727918919845843389 467124647969594942191271)
                      ·
                        rfl

theorem cell23_909722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_909722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909722 prefixEnd_909722 := by exact prefixLift 909722
  have htrace : WordTrace (prefixWord ++ tailWord_909722) baseStart_909722 baseEnd_909722 := by
    simpa [prefixWord, tailWord_909722, baseEnd_909722] using wordTrace_append hprefix tailTrace_909722
  have hstable : (prefixWord ++ tailWord_909722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909722).length < 2 ^ (prefixWord ++ tailWord_909722).sum := by decide
  have hdescent : baseEnd_909722 < baseStart_909722 := by decide
  rcases family_descends (prefixWord ++ tailWord_909722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909729 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 6]
def baseStart_909729 : Nat := 118140960795 + 909729 * 2 ^ 59
def prefixEnd_909729 : Nat := 4983230072969 + 3 ^ 40 * 909729 * 2
def baseEnd_909729 : Nat := 51903138037130712755971

theorem tailTrace_909729 : CollatzResearch.WordTrace tailWord_909729 prefixEnd_909729 51903138037130712755971 := by
  unfold tailWord_909729
  simp only [CollatzResearch.WordTrace]
  refine ⟨33180542521214677188724241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22120361680809784792482827 33180542521214677188724241)
  ·
    refine ⟨24885406890911007891543181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33180542521214677188724241 24885406890911007891543181)
    ·
      refine ⟨9332027584091627959328693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24885406890911007891543181 9332027584091627959328693)
      ·
        refine ⟨874877586008590121187065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9332027584091627959328693 874877586008590121187065)
        ·
          refine ⟨656158189506442590890299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874877586008590121187065 656158189506442590890299)
          ·
            refine ⟨984237284259663886335449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656158189506442590890299 984237284259663886335449)
            ·
              refine ⟨738177963194747914751587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984237284259663886335449 738177963194747914751587)
              ·
                refine ⟨1107266944792121872127381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738177963194747914751587 1107266944792121872127381)
                ·
                  refine ⟨51903138037130712755971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1107266944792121872127381 51903138037130712755971)
                  ·
                    rfl

theorem cell23_909729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 6].length) (baseStart_909729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909729 prefixEnd_909729 := by exact prefixLift 909729
  have htrace : WordTrace (prefixWord ++ tailWord_909729) baseStart_909729 baseEnd_909729 := by
    simpa [prefixWord, tailWord_909729, baseEnd_909729] using wordTrace_append hprefix tailTrace_909729
  have hstable : (prefixWord ++ tailWord_909729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909729).length < 2 ^ (prefixWord ++ tailWord_909729).sum := by decide
  have hdescent : baseEnd_909729 < baseStart_909729 := by decide
  rcases family_descends (prefixWord ++ tailWord_909729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909745 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_909745 : Nat := 118140960795 + 909745 * 2 ^ 59
def prefixEnd_909745 : Nat := 4983230072969 + 3 ^ 40 * 909745 * 2
def baseEnd_909745 : Nat := 467136458024648352203665

theorem tailTrace_909745 : CollatzResearch.WordTrace tailWord_909745 prefixEnd_909745 467136458024648352203665 := by
  unfold tailWord_909745
  simp only [CollatzResearch.WordTrace]
  refine ⟨33181126089156711921306689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22120750726104474614204459 33181126089156711921306689)
  ·
    refine ⟨24885844566867533940980017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33181126089156711921306689 24885844566867533940980017)
    ·
      refine ⟨18664383425150650455735013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24885844566867533940980017 18664383425150650455735013)
      ·
        refine ⟨3499571892215746960450315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18664383425150650455735013 3499571892215746960450315)
        ·
          refine ⟨5249357838323620440675473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499571892215746960450315 5249357838323620440675473)
          ·
            refine ⟨3937018378742715330506605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5249357838323620440675473 3937018378742715330506605)
            ·
              refine ⟨1476381892028518248939977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3937018378742715330506605 1476381892028518248939977)
              ·
                refine ⟨1107286419021388686704983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476381892028518248939977 1107286419021388686704983)
                ·
                  refine ⟨1660929628532083030057475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107286419021388686704983 1660929628532083030057475)
                  ·
                    refine ⟨2491394442798124545086213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1660929628532083030057475 2491394442798124545086213)
                    ·
                      refine ⟨467136458024648352203665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2491394442798124545086213 467136458024648352203665)
                      ·
                        rfl

theorem cell23_909745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_909745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909745 prefixEnd_909745 := by exact prefixLift 909745
  have htrace : WordTrace (prefixWord ++ tailWord_909745) baseStart_909745 baseEnd_909745 := by
    simpa [prefixWord, tailWord_909745, baseEnd_909745] using wordTrace_append hprefix tailTrace_909745
  have hstable : (prefixWord ++ tailWord_909745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909745).length < 2 ^ (prefixWord ++ tailWord_909745).sum := by decide
  have hdescent : baseEnd_909745 < baseStart_909745 := by decide
  rcases family_descends (prefixWord ++ tailWord_909745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909751 : List Nat := [1, 1, 3, 1, 3, 3, 2, 9]
def baseStart_909751 : Nat := 118140960795 + 909751 * 2 ^ 59
def prefixEnd_909751 : Nat := 4983230072969 + 3 ^ 40 * 909751 * 2
def baseEnd_909751 : Nat := 17301464404021308471431

theorem tailTrace_909751 : CollatzResearch.WordTrace tailWord_909751 prefixEnd_909751 17301464404021308471431 := by
  unfold tailWord_909751
  simp only [CollatzResearch.WordTrace]
  refine ⟨33181344927134974946025107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22120896618089983297350071 33181344927134974946025107)
  ·
    refine ⟨49772017390702462419037661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33181344927134974946025107 49772017390702462419037661)
    ·
      refine ⟨18664506521513423407139123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49772017390702462419037661 18664506521513423407139123)
      ·
        refine ⟨27996759782270135110708685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18664506521513423407139123 27996759782270135110708685)
        ·
          refine ⟨10498784918351300666515757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27996759782270135110708685 10498784918351300666515757)
          ·
            refine ⟨3937044344381737749943409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10498784918351300666515757 3937044344381737749943409)
            ·
              refine ⟨2952783258286303312457557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3937044344381737749943409 2952783258286303312457557)
              ·
                refine ⟨17301464404021308471431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2952783258286303312457557 17301464404021308471431)
                ·
                  rfl

theorem cell23_909751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 9].length) (baseStart_909751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909751 prefixEnd_909751 := by exact prefixLift 909751
  have htrace : WordTrace (prefixWord ++ tailWord_909751) baseStart_909751 baseEnd_909751 := by
    simpa [prefixWord, tailWord_909751, baseEnd_909751] using wordTrace_append hprefix tailTrace_909751
  have hstable : (prefixWord ++ tailWord_909751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909751).length < 2 ^ (prefixWord ++ tailWord_909751).sum := by decide
  have hdescent : baseEnd_909751 < baseStart_909751 := by decide
  rcases family_descends (prefixWord ++ tailWord_909751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909758 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_909758 : Nat := 118140960795 + 909758 * 2 ^ 59
def prefixEnd_909758 : Nat := 4983230072969 + 3 ^ 40 * 909758 * 2
def baseEnd_909758 : Nat := 467143133273156801341105

theorem tailTrace_909758 : CollatzResearch.WordTrace tailWord_909758 prefixEnd_909758 467143133273156801341105 := by
  unfold tailWord_909758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4147700029763701892691241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22121066825406410094353285 4147700029763701892691241)
  ·
    refine ⟨3110775022322776419518431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4147700029763701892691241 3110775022322776419518431)
    ·
      refine ⟨4666162533484164629277647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110775022322776419518431 4666162533484164629277647)
      ·
        refine ⟨6999243800226246943916471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4666162533484164629277647 6999243800226246943916471)
        ·
          refine ⟨10498865700339370415874707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999243800226246943916471 10498865700339370415874707)
          ·
            refine ⟨15748298550509055623812061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10498865700339370415874707 15748298550509055623812061)
            ·
              refine ⟨5905611956440895858929523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15748298550509055623812061 5905611956440895858929523)
              ·
                refine ⟨8858417934661343788394285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905611956440895858929523 8858417934661343788394285)
                ·
                  refine ⟨3321906725498003920647857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8858417934661343788394285 3321906725498003920647857)
                  ·
                    refine ⟨2491430044123502940485893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3321906725498003920647857 2491430044123502940485893)
                    ·
                      refine ⟨467143133273156801341105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2491430044123502940485893 467143133273156801341105)
                      ·
                        rfl

theorem cell23_909758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_909758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909758 prefixEnd_909758 := by exact prefixLift 909758
  have htrace : WordTrace (prefixWord ++ tailWord_909758) baseStart_909758 baseEnd_909758 := by
    simpa [prefixWord, tailWord_909758, baseEnd_909758] using wordTrace_append hprefix tailTrace_909758
  have hstable : (prefixWord ++ tailWord_909758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909758).length < 2 ^ (prefixWord ++ tailWord_909758).sum := by decide
  have hdescent : baseEnd_909758 < baseStart_909758 := by decide
  rcases family_descends (prefixWord ++ tailWord_909758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909772 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_909772 : Nat := 118140960795 + 909772 * 2 ^ 59
def prefixEnd_909772 : Nat := 4983230072969 + 3 ^ 40 * 909772 * 2
def baseEnd_909772 : Nat := 155716774000773248855347

theorem tailTrace_909772 : CollatzResearch.WordTrace tailWord_909772 prefixEnd_909772 155716774000773248855347 := by
  unfold tailWord_909772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16591055430029447766269785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22121407240039263688359713 16591055430029447766269785)
  ·
    refine ⟨12443291572522085824702339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16591055430029447766269785 12443291572522085824702339)
    ·
      refine ⟨18664937358783128737053509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443291572522085824702339 18664937358783128737053509)
      ·
        refine ⟨3499675754771836638197533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18664937358783128737053509 3499675754771836638197533)
        ·
          refine ⟨1312378408039438739324075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3499675754771836638197533 1312378408039438739324075)
          ·
            refine ⟨1968567612059158108986113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312378408039438739324075 1968567612059158108986113)
            ·
              refine ⟨1476425709044368581739585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968567612059158108986113 1476425709044368581739585)
              ·
                refine ⟨1107319281783276436304689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476425709044368581739585 1107319281783276436304689)
                ·
                  refine ⟨830489461337457327228517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107319281783276436304689 830489461337457327228517)
                  ·
                    refine ⟨155716774000773248855347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830489461337457327228517 155716774000773248855347)
                    ·
                      rfl

theorem cell23_909772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_909772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909772 prefixEnd_909772 := by exact prefixLift 909772
  have htrace : WordTrace (prefixWord ++ tailWord_909772) baseStart_909772 baseEnd_909772 := by
    simpa [prefixWord, tailWord_909772, baseEnd_909772] using wordTrace_append hprefix tailTrace_909772
  have hstable : (prefixWord ++ tailWord_909772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909772).length < 2 ^ (prefixWord ++ tailWord_909772).sum := by decide
  have hdescent : baseEnd_909772 < baseStart_909772 := by decide
  rcases family_descends (prefixWord ++ tailWord_909772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909811 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 1, 8]
def baseStart_909811 : Nat := 118140960795 + 909811 * 2 ^ 59
def prefixEnd_909811 : Nat := 4983230072969 + 3 ^ 40 * 909811 * 2
def baseEnd_909811 : Nat := 155723449249281697992787

theorem tailTrace_909811 : CollatzResearch.WordTrace tailWord_909811 prefixEnd_909811 155723449249281697992787 := by
  unfold tailWord_909811
  simp only [CollatzResearch.WordTrace]
  refine ⟨33183533306917605193209287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22122355537945070128806191 33183533306917605193209287)
  ·
    refine ⟨49775299960376407789813931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33183533306917605193209287 49775299960376407789813931)
    ·
      refine ⟨74662949940564611684720897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49775299960376407789813931 74662949940564611684720897)
      ·
        refine ⟨55997212455423458763540673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74662949940564611684720897 55997212455423458763540673)
        ·
          refine ⟨41997909341567594072655505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55997212455423458763540673 41997909341567594072655505)
          ·
            refine ⟨31498432006175695554491629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41997909341567594072655505 31498432006175695554491629)
            ·
              refine ⟨11811912002315885832934361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31498432006175695554491629 11811912002315885832934361)
              ·
                refine ⟨8858934001736914374700771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11811912002315885832934361 8858934001736914374700771)
                ·
                  refine ⟨13288401002605371562051157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8858934001736914374700771 13288401002605371562051157)
                  ·
                    refine ⟨155723449249281697992787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13288401002605371562051157 155723449249281697992787)
                    ·
                      rfl

theorem cell23_909811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 8].length) (baseStart_909811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909811 prefixEnd_909811 := by exact prefixLift 909811
  have htrace : WordTrace (prefixWord ++ tailWord_909811) baseStart_909811 baseEnd_909811 := by
    simpa [prefixWord, tailWord_909811, baseEnd_909811] using wordTrace_append hprefix tailTrace_909811
  have hstable : (prefixWord ++ tailWord_909811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909811).length < 2 ^ (prefixWord ++ tailWord_909811).sum := by decide
  have hdescent : baseEnd_909811 < baseStart_909811 := by decide
  rcases family_descends (prefixWord ++ tailWord_909811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909813 : List Nat := [1, 3, 5, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_909813 : Nat := 118140960795 + 909813 * 2 ^ 59
def prefixEnd_909813 : Nat := 4983230072969 + 3 ^ 40 * 909813 * 2
def baseEnd_909813 : Nat := 467171374709154086153353

theorem tailTrace_909813 : CollatzResearch.WordTrace tailWord_909813 prefixEnd_909813 467171374709154086153353 := by
  unfold tailWord_909813
  simp only [CollatzResearch.WordTrace]
  refine ⟨33183606252910359534782093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22122404168606906356521395 33183606252910359534782093)
  ·
    refine ⟨12443852344841384825543285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33183606252910359534782093 12443852344841384825543285)
    ·
      refine ⟨1166611157328879827394683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12443852344841384825543285 1166611157328879827394683)
      ·
        refine ⟨1749916735993319741092025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166611157328879827394683 1749916735993319741092025)
        ·
          refine ⟨1312437551994989805819019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749916735993319741092025 1312437551994989805819019)
          ·
            refine ⟨1968656327992484708728529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312437551994989805819019 1968656327992484708728529)
            ·
              refine ⟨1476492245994363531546397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968656327992484708728529 1476492245994363531546397)
              ·
                refine ⟨553684592247886324329899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1476492245994363531546397 553684592247886324329899)
                ·
                  refine ⟨830526888371829486494849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553684592247886324329899 830526888371829486494849)
                  ·
                    refine ⟨622895166278872114871137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 830526888371829486494849 622895166278872114871137)
                    ·
                      refine ⟨467171374709154086153353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622895166278872114871137 467171374709154086153353)
                      ·
                        rfl

theorem cell23_909813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_909813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909813 prefixEnd_909813 := by exact prefixLift 909813
  have htrace : WordTrace (prefixWord ++ tailWord_909813) baseStart_909813 baseEnd_909813 := by
    simpa [prefixWord, tailWord_909813, baseEnd_909813] using wordTrace_append hprefix tailTrace_909813
  have hstable : (prefixWord ++ tailWord_909813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909813).length < 2 ^ (prefixWord ++ tailWord_909813).sum := by decide
  have hdescent : baseEnd_909813 < baseStart_909813 := by decide
  rcases family_descends (prefixWord ++ tailWord_909813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909830 : List Nat := [6, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_909830 : Nat := 118140960795 + 909830 * 2 ^ 59
def prefixEnd_909830 : Nat := 4983230072969 + 3 ^ 40 * 909830 * 2
def baseEnd_909830 : Nat := 467180103880280519640775

theorem tailTrace_909830 : CollatzResearch.WordTrace tailWord_909830 prefixEnd_909830 467180103880280519640775 := by
  unfold tailWord_909830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037007071682774107442217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22122817529232514292100629 1037007071682774107442217)
  ·
    refine ⟨777755303762080580581663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1037007071682774107442217 777755303762080580581663)
    ·
      refine ⟨1166632955643120870872495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777755303762080580581663 1166632955643120870872495)
      ·
        refine ⟨1749949433464681306308743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166632955643120870872495 1749949433464681306308743)
        ·
          refine ⟨2624924150197021959463115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749949433464681306308743 2624924150197021959463115)
          ·
            refine ⟨3937386225295532939194673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624924150197021959463115 3937386225295532939194673)
            ·
              refine ⟨2953039668971649704396005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3937386225295532939194673 2953039668971649704396005)
              ·
                refine ⟨553694937932184319574251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2953039668971649704396005 553694937932184319574251)
                ·
                  refine ⟨830542406898276479361377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553694937932184319574251 830542406898276479361377)
                  ·
                    refine ⟨622906805173707359521033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 830542406898276479361377 622906805173707359521033)
                    ·
                      refine ⟨467180103880280519640775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622906805173707359521033 467180103880280519640775)
                      ·
                        rfl

theorem cell23_909830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_909830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909830 prefixEnd_909830 := by exact prefixLift 909830
  have htrace : WordTrace (prefixWord ++ tailWord_909830) baseStart_909830 baseEnd_909830 := by
    simpa [prefixWord, tailWord_909830, baseEnd_909830] using wordTrace_append hprefix tailTrace_909830
  have hstable : (prefixWord ++ tailWord_909830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909830).length < 2 ^ (prefixWord ++ tailWord_909830).sum := by decide
  have hdescent : baseEnd_909830 < baseStart_909830 := by decide
  rcases family_descends (prefixWord ++ tailWord_909830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909851 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9]
def baseStart_909851 : Nat := 118140960795 + 909851 * 2 ^ 59
def prefixEnd_909851 : Nat := 4983230072969 + 3 ^ 40 * 909851 * 2
def baseEnd_909851 : Nat := 467190886974024937478177

theorem tailTrace_909851 : CollatzResearch.WordTrace tailWord_909851 prefixEnd_909851 467190886974024937478177 := by
  unfold tailWord_909851
  simp only [CollatzResearch.WordTrace]
  refine ⟨33184992226772692024665407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22123328151181794683110271 33184992226772692024665407)
  ·
    refine ⟨49777488340159038036998111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33184992226772692024665407 49777488340159038036998111)
    ·
      refine ⟨74666232510238557055497167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49777488340159038036998111 74666232510238557055497167)
      ·
        refine ⟨111999348765357835583245751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74666232510238557055497167 111999348765357835583245751)
        ·
          refine ⟨167999023148036753374868627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111999348765357835583245751 167999023148036753374868627)
          ·
            refine ⟨251998534722055130062302941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167999023148036753374868627 251998534722055130062302941)
            ·
              refine ⟨94499450520770673773363603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251998534722055130062302941 94499450520770673773363603)
              ·
                refine ⟨141749175781156010660045405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94499450520770673773363603 141749175781156010660045405)
                ·
                  refine ⟨53155940917933503997517027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141749175781156010660045405 53155940917933503997517027)
                  ·
                    refine ⟨79733911376900255996275541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53155940917933503997517027 79733911376900255996275541)
                    ·
                      refine ⟨467190886974024937478177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 79733911376900255996275541 467190886974024937478177)
                      ·
                        rfl

theorem cell23_909851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_909851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909851 prefixEnd_909851 := by exact prefixLift 909851
  have htrace : WordTrace (prefixWord ++ tailWord_909851) baseStart_909851 baseEnd_909851 := by
    simpa [prefixWord, tailWord_909851, baseEnd_909851] using wordTrace_append hprefix tailTrace_909851
  have hstable : (prefixWord ++ tailWord_909851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909851).length < 2 ^ (prefixWord ++ tailWord_909851).sum := by decide
  have hdescent : baseEnd_909851 < baseStart_909851 := by decide
  rcases family_descends (prefixWord ++ tailWord_909851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909852 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_909852 : Nat := 118140960795 + 909852 * 2 ^ 59
def prefixEnd_909852 : Nat := 4983230072969 + 3 ^ 40 * 909852 * 2
def baseEnd_909852 : Nat := 467191400454679433565673

theorem tailTrace_909852 : CollatzResearch.WordTrace tailWord_909852 prefixEnd_909852 467191400454679433565673 := by
  unfold tailWord_909852
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592514349884534597725905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22123352466512712796967873 16592514349884534597725905)
  ·
    refine ⟨12444385762413400948294429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16592514349884534597725905 12444385762413400948294429)
    ·
      refine ⟨4666644660905025355610411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12444385762413400948294429 4666644660905025355610411)
      ·
        refine ⟨6999966991357538033415617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4666644660905025355610411 6999966991357538033415617)
        ·
          refine ⟨5249975243518153525061713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6999966991357538033415617 5249975243518153525061713)
          ·
            refine ⟨3937481432638615143796285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5249975243518153525061713 3937481432638615143796285)
            ·
              refine ⟨1476555537239480678923607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3937481432638615143796285 1476555537239480678923607)
              ·
                refine ⟨2214833305859221018385411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476555537239480678923607 2214833305859221018385411)
                ·
                  refine ⟨3322249958788831527578117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214833305859221018385411 3322249958788831527578117)
                  ·
                    refine ⟨622921867272905911420897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3322249958788831527578117 622921867272905911420897)
                    ·
                      refine ⟨467191400454679433565673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 622921867272905911420897 467191400454679433565673)
                      ·
                        rfl

theorem cell23_909852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_909852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909852 prefixEnd_909852 := by exact prefixLift 909852
  have htrace : WordTrace (prefixWord ++ tailWord_909852) baseStart_909852 baseEnd_909852 := by
    simpa [prefixWord, tailWord_909852, baseEnd_909852] using wordTrace_append hprefix tailTrace_909852
  have hstable : (prefixWord ++ tailWord_909852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909852).length < 2 ^ (prefixWord ++ tailWord_909852).sum := by decide
  have hdescent : baseEnd_909852 < baseStart_909852 := by decide
  rcases family_descends (prefixWord ++ tailWord_909852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909868 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_909868 : Nat := 118140960795 + 909868 * 2 ^ 59
def prefixEnd_909868 : Nat := 4983230072969 + 3 ^ 40 * 909868 * 2
def baseEnd_909868 : Nat := 467199616145151370965599

theorem tailTrace_909868 : CollatzResearch.WordTrace tailWord_909868 prefixEnd_909868 467199616145151370965599 := by
  unfold tailWord_909868
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592806133855551964017129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22123741511807402618689505 16592806133855551964017129)
  ·
    refine ⟨12444604600391663973012847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16592806133855551964017129 12444604600391663973012847)
    ·
      refine ⟨18666906900587495959519271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12444604600391663973012847 18666906900587495959519271)
      ·
        refine ⟨28000360350881243939278907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18666906900587495959519271 28000360350881243939278907)
        ·
          refine ⟨42000540526321865908918361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28000360350881243939278907 42000540526321865908918361)
          ·
            refine ⟨31500405394741399431688771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42000540526321865908918361 31500405394741399431688771)
            ·
              refine ⟨47250608092112099147533157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31500405394741399431688771 47250608092112099147533157)
              ·
                refine ⟨8859489017271018590162467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47250608092112099147533157 8859489017271018590162467)
                ·
                  refine ⟨13289233525906527885243701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8859489017271018590162467 13289233525906527885243701)
                  ·
                    refine ⟨1245865643053736989241597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13289233525906527885243701 1245865643053736989241597)
                    ·
                      refine ⟨467199616145151370965599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1245865643053736989241597 467199616145151370965599)
                      ·
                        rfl

theorem cell23_909868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_909868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909868 prefixEnd_909868 := by exact prefixLift 909868
  have htrace : WordTrace (prefixWord ++ tailWord_909868) baseStart_909868 baseEnd_909868 := by
    simpa [prefixWord, tailWord_909868, baseEnd_909868] using wordTrace_append hprefix tailTrace_909868
  have hstable : (prefixWord ++ tailWord_909868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909868).length < 2 ^ (prefixWord ++ tailWord_909868).sum := by decide
  have hdescent : baseEnd_909868 < baseStart_909868 := by decide
  rcases family_descends (prefixWord ++ tailWord_909868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909888 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 4, 5]
def baseStart_909888 : Nat := 118140960795 + 909888 * 2 ^ 59
def prefixEnd_909888 : Nat := 4983230072969 + 3 ^ 40 * 909888 * 2
def baseEnd_909888 : Nat := 155736628586080430905169

theorem tailTrace_909888 : CollatzResearch.WordTrace tailWord_909888 prefixEnd_909888 155736628586080430905169 := by
  unfold tailWord_909888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16593170863819323671881159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22124227818425764895841545 16593170863819323671881159)
  ·
    refine ⟨24889756295728985507821739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16593170863819323671881159 24889756295728985507821739)
    ·
      refine ⟨37334634443593478261732609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24889756295728985507821739 37334634443593478261732609)
      ·
        refine ⟨28000975832695108696299457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37334634443593478261732609 28000975832695108696299457)
        ·
          refine ⟨21000731874521331522224593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28000975832695108696299457 21000731874521331522224593)
          ·
            refine ⟨15750548905890998641668445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21000731874521331522224593 15750548905890998641668445)
            ·
              refine ⟨5906455839709124490625667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15750548905890998641668445 5906455839709124490625667)
              ·
                refine ⟨8859683759563686735938501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906455839709124490625667 8859683759563686735938501)
                ·
                  refine ⟨1661190704918191262988469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8859683759563686735938501 1661190704918191262988469)
                  ·
                    refine ⟨155736628586080430905169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1661190704918191262988469 155736628586080430905169)
                    ·
                      rfl

theorem cell23_909888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_909888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909888 prefixEnd_909888 := by exact prefixLift 909888
  have htrace : WordTrace (prefixWord ++ tailWord_909888) baseStart_909888 baseEnd_909888 := by
    simpa [prefixWord, tailWord_909888, baseEnd_909888] using wordTrace_append hprefix tailTrace_909888
  have hstable : (prefixWord ++ tailWord_909888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909888).length < 2 ^ (prefixWord ++ tailWord_909888).sum := by decide
  have hdescent : baseEnd_909888 < baseStart_909888 := by decide
  rcases family_descends (prefixWord ++ tailWord_909888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
