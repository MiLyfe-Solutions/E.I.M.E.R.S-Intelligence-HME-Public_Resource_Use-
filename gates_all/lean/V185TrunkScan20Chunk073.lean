import V185TrunkScan20Chunk072

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_444629 : List Nat := [1, 3, 2, 4, 3, 7]
def baseStart_444629 : Nat := 118140960795 + 444629 * 2 ^ 59
def prefixEnd_444629 : Nat := 4983230072969 + 3 ^ 40 * 444629 * 2
def baseEnd_444629 : Nat := 7516325594338966936385

theorem tailTrace_444629 : CollatzResearch.WordTrace tailWord_444629 prefixEnd_444629 7516325594338966936385 := by
  unfold tailWord_444629
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216951906192544432688941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10811301270795029621792627 16216951906192544432688941)
  ·
    refine ⟨6081356964822204162258353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16216951906192544432688941 6081356964822204162258353)
    ·
      refine ⟨4561017723616653121693765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6081356964822204162258353 4561017723616653121693765)
      ·
        refine ⟨855190823178122460317581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4561017723616653121693765 855190823178122460317581)
        ·
          refine ⟨320696558691795922619093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 855190823178122460317581 320696558691795922619093)
          ·
            refine ⟨7516325594338966936385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 320696558691795922619093 7516325594338966936385)
            ·
              rfl

theorem cell20_444629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 7].length) (baseStart_444629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444629 prefixEnd_444629 := by exact prefixLift 444629
  have htrace : WordTrace (prefixWord ++ tailWord_444629) baseStart_444629 baseEnd_444629 := by
    simpa [prefixWord, tailWord_444629, baseEnd_444629] using wordTrace_append hprefix tailTrace_444629
  have hstable : (prefixWord ++ tailWord_444629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444629).length < 2 ^ (prefixWord ++ tailWord_444629).sum := by decide
  have hdescent : baseEnd_444629 < baseStart_444629 := by decide
  rcases family_descends (prefixWord ++ tailWord_444629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444642 : List Nat := [3, 3, 4, 1, 1, 2, 1, 5]
def baseStart_444642 : Nat := 118140960795 + 444642 * 2 ^ 59
def prefixEnd_444642 : Nat := 4983230072969 + 3 ^ 40 * 444642 * 2
def baseEnd_444642 : Nat := 67648908200460613283003

theorem tailTrace_444642 : CollatzResearch.WordTrace tailWord_444642 prefixEnd_444642 67648908200460613283003 := by
  unfold tailWord_444642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4054356513786361913228045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10811617370096965101941453 4054356513786361913228045)
  ·
    refine ⟨1520383692669885717460517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4054356513786361913228045 1520383692669885717460517)
    ·
      refine ⟨285071942375603572023847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1520383692669885717460517 285071942375603572023847)
      ·
        refine ⟨427607913563405358035771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285071942375603572023847 427607913563405358035771)
        ·
          refine ⟨641411870345108037053657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427607913563405358035771 641411870345108037053657)
          ·
            refine ⟨481058902758831027790243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641411870345108037053657 481058902758831027790243)
            ·
              refine ⟨721588354138246541685365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481058902758831027790243 721588354138246541685365)
              ·
                refine ⟨67648908200460613283003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 721588354138246541685365 67648908200460613283003)
                ·
                  rfl

theorem cell20_444642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_444642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444642 prefixEnd_444642 := by exact prefixLift 444642
  have htrace : WordTrace (prefixWord ++ tailWord_444642) baseStart_444642 baseEnd_444642 := by
    simpa [prefixWord, tailWord_444642, baseEnd_444642] using wordTrace_append hprefix tailTrace_444642
  have hstable : (prefixWord ++ tailWord_444642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444642).length < 2 ^ (prefixWord ++ tailWord_444642).sum := by decide
  have hdescent : baseEnd_444642 < baseStart_444642 := by decide
  rcases family_descends (prefixWord ++ tailWord_444642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444698 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_444698 : Nat := 118140960795 + 444698 * 2 ^ 59
def prefixEnd_444698 : Nat := 4983230072969 + 3 ^ 40 * 444698 * 2
def baseEnd_444698 : Nat := 202972284527294533982113

theorem tailTrace_444698 : CollatzResearch.WordTrace tailWord_444698 prefixEnd_444698 202972284527294533982113 := by
  unfold tailWord_444698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4054867135735642304237687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10812979028628379477967165 4054867135735642304237687)
  ·
    refine ⟨6082300703603463456356531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4054867135735642304237687 6082300703603463456356531)
    ·
      refine ⟨9123451055405195184534797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082300703603463456356531 9123451055405195184534797)
      ·
        refine ⟨3421294145776948194200549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9123451055405195184534797 3421294145776948194200549)
        ·
          refine ⟨641492652333177786412603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3421294145776948194200549 641492652333177786412603)
          ·
            refine ⟨962238978499766679618905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641492652333177786412603 962238978499766679618905)
            ·
              refine ⟨721679233874825009714179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962238978499766679618905 721679233874825009714179)
              ·
                refine ⟨1082518850812237514571269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721679233874825009714179 1082518850812237514571269)
                ·
                  refine ⟨202972284527294533982113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082518850812237514571269 202972284527294533982113)
                  ·
                    rfl

theorem cell20_444698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_444698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444698 prefixEnd_444698 := by exact prefixLift 444698
  have htrace : WordTrace (prefixWord ++ tailWord_444698) baseStart_444698 baseEnd_444698 := by
    simpa [prefixWord, tailWord_444698, baseEnd_444698] using wordTrace_append hprefix tailTrace_444698
  have hstable : (prefixWord ++ tailWord_444698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444698).length < 2 ^ (prefixWord ++ tailWord_444698).sum := by decide
  have hdescent : baseEnd_444698 < baseStart_444698 := by decide
  rcases family_descends (prefixWord ++ tailWord_444698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444718 : List Nat := [4, 1, 3, 3, 2, 1, 2, 4]
def baseStart_444718 : Nat := 118140960795 + 444718 * 2 ^ 59
def prefixEnd_444718 : Nat := 4983230072969 + 3 ^ 40 * 444718 * 2
def baseEnd_444718 : Nat := 67660471024087784438455

theorem tailTrace_444718 : CollatzResearch.WordTrace tailWord_444718 prefixEnd_444718 67660471024087784438455 := by
  unfold tailWord_444718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027524750358764079084851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10813465335246741755119205 2027524750358764079084851)
  ·
    refine ⟨3041287125538146118627277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2027524750358764079084851 3041287125538146118627277)
    ·
      refine ⟨1140482672076804794485229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3041287125538146118627277 1140482672076804794485229)
      ·
        refine ⟨427681002028801797931961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1140482672076804794485229 427681002028801797931961)
        ·
          refine ⟨320760751521601348448971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427681002028801797931961 320760751521601348448971)
          ·
            refine ⟨481141127282402022673457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320760751521601348448971 481141127282402022673457)
            ·
              refine ⟨360855845461801517005093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481141127282402022673457 360855845461801517005093)
              ·
                refine ⟨67660471024087784438455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360855845461801517005093 67660471024087784438455)
                ·
                  rfl

theorem cell20_444718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_444718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444718 prefixEnd_444718 := by exact prefixLift 444718
  have htrace : WordTrace (prefixWord ++ tailWord_444718) baseStart_444718 baseEnd_444718 := by
    simpa [prefixWord, tailWord_444718, baseEnd_444718] using wordTrace_append hprefix tailTrace_444718
  have hstable : (prefixWord ++ tailWord_444718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444718).length < 2 ^ (prefixWord ++ tailWord_444718).sum := by decide
  have hdescent : baseEnd_444718 < baseStart_444718 := by decide
  rcases family_descends (prefixWord ++ tailWord_444718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444722 : List Nat := [3, 2, 1, 1, 5, 2, 2, 4]
def baseStart_444722 : Nat := 118140960795 + 444722 * 2 ^ 59
def prefixEnd_444722 : Nat := 4983230072969 + 3 ^ 40 * 444722 * 2
def baseEnd_444722 : Nat := 67661079593752372394005

theorem tailTrace_444722 : CollatzResearch.WordTrace tailWord_444722 prefixEnd_444722 67661079593752372394005 := by
  unfold tailWord_444722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055085973713905328956105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10813562596570414210549613 4055085973713905328956105)
  ·
    refine ⟨3041314480285428996717079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4055085973713905328956105 3041314480285428996717079)
    ·
      refine ⟨4561971720428143495075619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3041314480285428996717079 4561971720428143495075619)
      ·
        refine ⟨6842957580642215242613429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561971720428143495075619 6842957580642215242613429)
        ·
          refine ⟨641527273185207678995009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6842957580642215242613429 641527273185207678995009)
          ·
            refine ⟨481145454888905759246257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641527273185207678995009 481145454888905759246257)
            ·
              refine ⟨360859091166679319434693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481145454888905759246257 360859091166679319434693)
              ·
                refine ⟨67661079593752372394005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360859091166679319434693 67661079593752372394005)
                ·
                  rfl

theorem cell20_444722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_444722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444722 prefixEnd_444722 := by exact prefixLift 444722
  have htrace : WordTrace (prefixWord ++ tailWord_444722) baseStart_444722 baseEnd_444722 := by
    simpa [prefixWord, tailWord_444722, baseEnd_444722] using wordTrace_append hprefix tailTrace_444722
  have hstable : (prefixWord ++ tailWord_444722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444722).length < 2 ^ (prefixWord ++ tailWord_444722).sum := by decide
  have hdescent : baseEnd_444722 < baseStart_444722 := by decide
  rcases family_descends (prefixWord ++ tailWord_444722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444753 : List Nat := [1, 2, 2, 1, 4, 3, 3, 2, 2]
def baseStart_444753 : Nat := 118140960795 + 444753 * 2 ^ 59
def prefixEnd_444753 : Nat := 4983230072969 + 3 ^ 40 * 444753 * 2
def baseEnd_444753 : Nat := 202997388025958787148555

theorem tailTrace_444753 : CollatzResearch.WordTrace tailWord_444753 prefixEnd_444753 202997388025958787148555 := by
  unfold tailWord_444753
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221474557743313610202913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10814316371828875740135275 16221474557743313610202913)
  ·
    refine ⟨12166105918307485207652185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16221474557743313610202913 12166105918307485207652185)
    ·
      refine ⟨9124579438730613905739139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12166105918307485207652185 9124579438730613905739139)
      ·
        refine ⟨13686869158095920858608709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9124579438730613905739139 13686869158095920858608709)
        ·
          refine ⟨2566287967142985160989133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13686869158095920858608709 2566287967142985160989133)
          ·
            refine ⟨962357987678619435370925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2566287967142985160989133 962357987678619435370925)
            ·
              refine ⟨360884245379482288264097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 962357987678619435370925 360884245379482288264097)
              ·
                refine ⟨270663184034611716198073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360884245379482288264097 270663184034611716198073)
                ·
                  refine ⟨202997388025958787148555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270663184034611716198073 202997388025958787148555)
                  ·
                    rfl

theorem cell20_444753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_444753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444753 prefixEnd_444753 := by exact prefixLift 444753
  have htrace : WordTrace (prefixWord ++ tailWord_444753) baseStart_444753 baseEnd_444753 := by
    simpa [prefixWord, tailWord_444753, baseEnd_444753] using wordTrace_append hprefix tailTrace_444753
  have hstable : (prefixWord ++ tailWord_444753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444753).length < 2 ^ (prefixWord ++ tailWord_444753).sum := by decide
  have hdescent : baseEnd_444753 < baseStart_444753 := by decide
  rcases family_descends (prefixWord ++ tailWord_444753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444812 : List Nat := [2, 2, 1, 2, 1, 5, 1, 4, 2]
def baseStart_444812 : Nat := 118140960795 + 444812 * 2 ^ 59
def prefixEnd_444812 : Nat := 4983230072969 + 3 ^ 40 * 444812 * 2
def baseEnd_444812 : Nat := 203024317233616804181647

theorem tailTrace_444812 : CollatzResearch.WordTrace tailWord_444812 prefixEnd_444812 203024317233616804181647 := by
  unfold tailWord_444812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8111813232264783343300345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10815750976353044457733793 8111813232264783343300345)
  ·
    refine ⟨6083859924198587507475259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8111813232264783343300345 6083859924198587507475259)
    ·
      refine ⟨9125789886297881261212889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083859924198587507475259 9125789886297881261212889)
      ·
        refine ⟨6844342414723410945909667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9125789886297881261212889 6844342414723410945909667)
        ·
          refine ⟨10266513622085116418864501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844342414723410945909667 10266513622085116418864501)
          ·
            refine ⟨962485652070479664268547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10266513622085116418864501 962485652070479664268547)
            ·
              refine ⟨1443728478105719496402821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962485652070479664268547 1443728478105719496402821)
              ·
                refine ⟨270699089644822405575529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1443728478105719496402821 270699089644822405575529)
                ·
                  refine ⟨203024317233616804181647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270699089644822405575529 203024317233616804181647)
                  ·
                    rfl

theorem cell20_444812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_444812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444812 prefixEnd_444812 := by exact prefixLift 444812
  have htrace : WordTrace (prefixWord ++ tailWord_444812) baseStart_444812 baseEnd_444812 := by
    simpa [prefixWord, tailWord_444812, baseEnd_444812] using wordTrace_append hprefix tailTrace_444812
  have hstable : (prefixWord ++ tailWord_444812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444812).length < 2 ^ (prefixWord ++ tailWord_444812).sum := by decide
  have hdescent : baseEnd_444812 < baseStart_444812 := by decide
  rcases family_descends (prefixWord ++ tailWord_444812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444826 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_444826 : Nat := 118140960795 + 444826 * 2 ^ 59
def prefixEnd_444826 : Nat := 4983230072969 + 3 ^ 40 * 444826 * 2
def baseEnd_444826 : Nat := 203030707215094977714923

theorem tailTrace_444826 : CollatzResearch.WordTrace tailWord_444826 prefixEnd_444826 203030707215094977714923 := by
  unfold tailWord_444826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4056034271619711769402583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10816091390985898051740221 4056034271619711769402583)
  ·
    refine ⟨6084051407429567654103875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4056034271619711769402583 6084051407429567654103875)
    ·
      refine ⟨9126077111144351481155813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6084051407429567654103875 9126077111144351481155813)
      ·
        refine ⟨1711139458339565902716715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9126077111144351481155813 1711139458339565902716715)
        ·
          refine ⟨2566709187509348854075073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711139458339565902716715 2566709187509348854075073)
          ·
            refine ⟨1925031890632011640556305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566709187509348854075073 1925031890632011640556305)
            ·
              refine ⟨1443773917974008730417229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1925031890632011640556305 1443773917974008730417229)
              ·
                refine ⟨541415219240253273906461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1443773917974008730417229 541415219240253273906461)
                ·
                  refine ⟨203030707215094977714923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541415219240253273906461 203030707215094977714923)
                  ·
                    rfl

theorem cell20_444826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_444826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444826 prefixEnd_444826 := by exact prefixLift 444826
  have htrace : WordTrace (prefixWord ++ tailWord_444826) baseStart_444826 baseEnd_444826 := by
    simpa [prefixWord, tailWord_444826, baseEnd_444826] using wordTrace_append hprefix tailTrace_444826
  have hstable : (prefixWord ++ tailWord_444826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444826).length < 2 ^ (prefixWord ++ tailWord_444826).sum := by decide
  have hdescent : baseEnd_444826 < baseStart_444826 := by decide
  rcases family_descends (prefixWord ++ tailWord_444826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444850 : List Nat := [3, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_444850 : Nat := 118140960795 + 444850 * 2 ^ 59
def prefixEnd_444850 : Nat := 4983230072969 + 3 ^ 40 * 444850 * 2
def baseEnd_444850 : Nat := 203041661469057560914825

theorem tailTrace_444850 : CollatzResearch.WordTrace tailWord_444850 prefixEnd_444850 203041661469057560914825 := by
  unfold tailWord_444850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4056253109597974794121001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10816674958927932784322669 4056253109597974794121001)
  ·
    refine ⟨3042189832198481095590751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4056253109597974794121001 3042189832198481095590751)
    ·
      refine ⟨4563284748297721643386127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042189832198481095590751 4563284748297721643386127)
      ·
        refine ⟨6844927122446582465079191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4563284748297721643386127 6844927122446582465079191)
        ·
          refine ⟨10267390683669873697618787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844927122446582465079191 10267390683669873697618787)
          ·
            refine ⟨15401086025504810546428181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10267390683669873697618787 15401086025504810546428181)
            ·
              refine ⟨721925907445537994363821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15401086025504810546428181 721925907445537994363821)
              ·
                refine ⟨270722215292076747886433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721925907445537994363821 270722215292076747886433)
                ·
                  refine ⟨203041661469057560914825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270722215292076747886433 203041661469057560914825)
                  ·
                    rfl

theorem cell20_444850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_444850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444850 prefixEnd_444850 := by exact prefixLift 444850
  have htrace : WordTrace (prefixWord ++ tailWord_444850) baseStart_444850 baseEnd_444850 := by
    simpa [prefixWord, tailWord_444850, baseEnd_444850] using wordTrace_append hprefix tailTrace_444850
  have hstable : (prefixWord ++ tailWord_444850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444850).length < 2 ^ (prefixWord ++ tailWord_444850).sum := by decide
  have hdescent : baseEnd_444850 < baseStart_444850 := by decide
  rcases family_descends (prefixWord ++ tailWord_444850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444871 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_444871 : Nat := 118140960795 + 444871 * 2 ^ 59
def prefixEnd_444871 : Nat := 4983230072969 + 3 ^ 40 * 444871 * 2
def baseEnd_444871 : Nat := 203051246441274821214739

theorem tailTrace_444871 : CollatzResearch.WordTrace tailWord_444871 prefixEnd_444871 203051246441274821214739 := by
  unfold tailWord_444871
  simp only [CollatzResearch.WordTrace]
  refine ⟨16225778371315819762998467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10817185580877213175332311 16225778371315819762998467)
  ·
    refine ⟨24338667556973729644497701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16225778371315819762998467 24338667556973729644497701)
    ·
      refine ⟨4563500166932574308343319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24338667556973729644497701 4563500166932574308343319)
      ·
        refine ⟨6845250250398861462514979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4563500166932574308343319 6845250250398861462514979)
        ·
          refine ⟨10267875375598292193772469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6845250250398861462514979 10267875375598292193772469)
          ·
            refine ⟨962613316462339893166169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10267875375598292193772469 962613316462339893166169)
            ·
              refine ⟨721959987346754919874627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962613316462339893166169 721959987346754919874627)
              ·
                refine ⟨1082939981020132379811941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721959987346754919874627 1082939981020132379811941)
                ·
                  refine ⟨203051246441274821214739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082939981020132379811941 203051246441274821214739)
                  ·
                    rfl

theorem cell20_444871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_444871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444871 prefixEnd_444871 := by exact prefixLift 444871
  have htrace : WordTrace (prefixWord ++ tailWord_444871) baseStart_444871 baseEnd_444871 := by
    simpa [prefixWord, tailWord_444871, baseEnd_444871] using wordTrace_append hprefix tailTrace_444871
  have hstable : (prefixWord ++ tailWord_444871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444871).length < 2 ^ (prefixWord ++ tailWord_444871).sum := by decide
  have hdescent : baseEnd_444871 < baseStart_444871 := by decide
  rcases family_descends (prefixWord ++ tailWord_444871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444895 : List Nat := [1, 1, 2, 3, 3, 4, 2, 4]
def baseStart_444895 : Nat := 118140960795 + 444895 * 2 ^ 59
def prefixEnd_444895 : Nat := 4983230072969 + 3 ^ 40 * 444895 * 2
def baseEnd_444895 : Nat := 67687400231745801471547

theorem tailTrace_444895 : CollatzResearch.WordTrace tailWord_444895 prefixEnd_444895 67687400231745801471547 := by
  unfold tailWord_444895
  simp only [CollatzResearch.WordTrace]
  refine ⟨16226653723228871861872139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10817769148819247907914759 16226653723228871861872139)
  ·
    refine ⟨24339980584843307792808209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16226653723228871861872139 24339980584843307792808209)
    ·
      refine ⟨18254985438632480844606157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24339980584843307792808209 18254985438632480844606157)
      ·
        refine ⟨6845619539487180316727309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18254985438632480844606157 6845619539487180316727309)
        ·
          refine ⟨2567107327307692618772741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6845619539487180316727309 2567107327307692618772741)
          ·
            refine ⟨481332623870192366019889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2567107327307692618772741 481332623870192366019889)
            ·
              refine ⟨360999467902644274514917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481332623870192366019889 360999467902644274514917)
              ·
                refine ⟨67687400231745801471547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360999467902644274514917 67687400231745801471547)
                ·
                  rfl

theorem cell20_444895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_444895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444895 prefixEnd_444895 := by exact prefixLift 444895
  have htrace : WordTrace (prefixWord ++ tailWord_444895) baseStart_444895 baseEnd_444895 := by
    simpa [prefixWord, tailWord_444895, baseEnd_444895] using wordTrace_append hprefix tailTrace_444895
  have hstable : (prefixWord ++ tailWord_444895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444895).length < 2 ^ (prefixWord ++ tailWord_444895).sum := by decide
  have hdescent : baseEnd_444895 < baseStart_444895 := by decide
  rcases family_descends (prefixWord ++ tailWord_444895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444940 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_444940 : Nat := 118140960795 + 444940 * 2 ^ 59
def prefixEnd_444940 : Nat := 4983230072969 + 3 ^ 40 * 444940 * 2
def baseEnd_444940 : Nat := 203082739921417247914457

theorem tailTrace_444940 : CollatzResearch.WordTrace tailWord_444940 prefixEnd_444940 203082739921417247914457 := by
  unfold tailWord_444940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114147504032922273630137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10818863338710563031506849 8114147504032922273630137)
  ·
    refine ⟨6085610628024691705222603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8114147504032922273630137 6085610628024691705222603)
    ·
      refine ⟨9128415942037037557833905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6085610628024691705222603 9128415942037037557833905)
      ·
        refine ⟨6846311956527778168375429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9128415942037037557833905 6846311956527778168375429)
        ·
          refine ⟨1283683491848958406570393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6846311956527778168375429 1283683491848958406570393)
          ·
            refine ⟨962762618886718804927795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283683491848958406570393 962762618886718804927795)
            ·
              refine ⟨1444143928330078207391693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962762618886718804927795 1444143928330078207391693)
              ·
                refine ⟨541553973123779327771885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444143928330078207391693 541553973123779327771885)
                ·
                  refine ⟨203082739921417247914457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541553973123779327771885 203082739921417247914457)
                  ·
                    rfl

theorem cell20_444940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_444940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444940 prefixEnd_444940 := by exact prefixLift 444940
  have htrace : WordTrace (prefixWord ++ tailWord_444940) baseStart_444940 baseEnd_444940 := by
    simpa [prefixWord, tailWord_444940, baseEnd_444940] using wordTrace_append hprefix tailTrace_444940
  have hstable : (prefixWord ++ tailWord_444940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444940).length < 2 ^ (prefixWord ++ tailWord_444940).sum := by decide
  have hdescent : baseEnd_444940 < baseStart_444940 := by decide
  rcases family_descends (prefixWord ++ tailWord_444940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444973 : List Nat := [1, 5, 4, 1, 2, 1, 2, 2, 2]
def baseStart_444973 : Nat := 118140960795 + 444973 * 2 ^ 59
def prefixEnd_444973 : Nat := 4983230072969 + 3 ^ 40 * 444973 * 2
def baseEnd_444973 : Nat := 203097802020615799814323

theorem tailTrace_444973 : CollatzResearch.WordTrace tailWord_444973 prefixEnd_444973 203097802020615799814323 := by
  unfold tailWord_444973
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229498616946291183211573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10819665744630860788807715 16229498616946291183211573)
  ·
    refine ⟨1521515495338714798426085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16229498616946291183211573 1521515495338714798426085)
    ·
      refine ⟨285284155376009024704891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1521515495338714798426085 285284155376009024704891)
      ·
        refine ⟨427926233064013537057337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285284155376009024704891 427926233064013537057337)
        ·
          refine ⟨320944674798010152793003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427926233064013537057337 320944674798010152793003)
          ·
            refine ⟨481417012197015229189505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320944674798010152793003 481417012197015229189505)
            ·
              refine ⟨361062759147761421892129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481417012197015229189505 361062759147761421892129)
              ·
                refine ⟨270797069360821066419097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361062759147761421892129 270797069360821066419097)
                ·
                  refine ⟨203097802020615799814323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270797069360821066419097 203097802020615799814323)
                  ·
                    rfl

theorem cell20_444973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_444973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444973 prefixEnd_444973 := by exact prefixLift 444973
  have htrace : WordTrace (prefixWord ++ tailWord_444973) baseStart_444973 baseEnd_444973 := by
    simpa [prefixWord, tailWord_444973, baseEnd_444973] using wordTrace_append hprefix tailTrace_444973
  have hstable : (prefixWord ++ tailWord_444973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444973).length < 2 ^ (prefixWord ++ tailWord_444973).sum := by decide
  have hdescent : baseEnd_444973 < baseStart_444973 := by decide
  rcases family_descends (prefixWord ++ tailWord_444973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445006 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_445006 : Nat := 118140960795 + 445006 * 2 ^ 59
def prefixEnd_445006 : Nat := 4983230072969 + 3 ^ 40 * 445006 * 2
def baseEnd_445006 : Nat := 203112864119814351714187

theorem tailTrace_445006 : CollatzResearch.WordTrace tailWord_445006 prefixEnd_445006 203112864119814351714187 := by
  unfold tailWord_445006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028837778228342227395359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10820468150551158546108581 2028837778228342227395359)
  ·
    refine ⟨3043256667342513341093039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2028837778228342227395359 3043256667342513341093039)
    ·
      refine ⟨4564885001013770011639559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043256667342513341093039 4564885001013770011639559)
      ·
        refine ⟨6847327501520655017459339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564885001013770011639559 6847327501520655017459339)
        ·
          refine ⟨10270991252280982526189009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6847327501520655017459339 10270991252280982526189009)
          ·
            refine ⟨7703243439210736894641757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10270991252280982526189009 7703243439210736894641757)
            ·
              refine ⟨2888716289704026335490659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7703243439210736894641757 2888716289704026335490659)
              ·
                refine ⟨4333074434556039503235989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888716289704026335490659 4333074434556039503235989)
                ·
                  refine ⟨203112864119814351714187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4333074434556039503235989 203112864119814351714187)
                  ·
                    rfl

theorem cell20_445006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_445006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445006 prefixEnd_445006 := by exact prefixLift 445006
  have htrace : WordTrace (prefixWord ++ tailWord_445006) baseStart_445006 baseEnd_445006 := by
    simpa [prefixWord, tailWord_445006, baseEnd_445006] using wordTrace_append hprefix tailTrace_445006
  have hstable : (prefixWord ++ tailWord_445006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445006).length < 2 ^ (prefixWord ++ tailWord_445006).sum := by decide
  have hdescent : baseEnd_445006 < baseStart_445006 := by decide
  rcases family_descends (prefixWord ++ tailWord_445006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445013 : List Nat := [1, 3, 2, 2, 1, 1, 2, 8]
def baseStart_445013 : Nat := 118140960795 + 445013 * 2 ^ 59
def prefixEnd_445013 : Nat := 4983230072969 + 3 ^ 40 * 445013 * 2
def baseEnd_445013 : Nat := 67705353036851146160275

theorem tailTrace_445013 : CollatzResearch.WordTrace tailWord_445013 prefixEnd_445013 67705353036851146160275 := by
  unfold tailWord_445013
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230957536801378014667693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10820638357867585343111795 16230957536801378014667693)
  ·
    refine ⟨6086609076300516755500385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16230957536801378014667693 6086609076300516755500385)
    ·
      refine ⟨4564956807225387566625289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6086609076300516755500385 4564956807225387566625289)
      ·
        refine ⟨3423717605419040674968967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564956807225387566625289 3423717605419040674968967)
        ·
          refine ⟨5135576408128561012453451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423717605419040674968967 5135576408128561012453451)
          ·
            refine ⟨7703364612192841518680177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135576408128561012453451 7703364612192841518680177)
            ·
              refine ⟨5777523459144631139010133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7703364612192841518680177 5777523459144631139010133)
              ·
                refine ⟨67705353036851146160275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5777523459144631139010133 67705353036851146160275)
                ·
                  rfl

theorem cell20_445013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_445013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445013 prefixEnd_445013 := by exact prefixLift 445013
  have htrace : WordTrace (prefixWord ++ tailWord_445013) baseStart_445013 baseEnd_445013 := by
    simpa [prefixWord, tailWord_445013, baseEnd_445013] using wordTrace_append hprefix tailTrace_445013
  have hstable : (prefixWord ++ tailWord_445013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445013).length < 2 ^ (prefixWord ++ tailWord_445013).sum := by decide
  have hdescent : baseEnd_445013 < baseStart_445013 := by decide
  rcases family_descends (prefixWord ++ tailWord_445013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445095 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 4]
def baseStart_445095 : Nat := 118140960795 + 445095 * 2 ^ 59
def prefixEnd_445095 : Nat := 4983230072969 + 3 ^ 40 * 445095 * 2
def baseEnd_445095 : Nat := 203153486144925597747157

theorem tailTrace_445095 : CollatzResearch.WordTrace tailWord_445095 prefixEnd_445095 203153486144925597747157 := by
  unfold tailWord_445095
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233948322504306019152739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10822632215002870679435159 16233948322504306019152739)
  ·
    refine ⟨24350922483756459028729109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16233948322504306019152739 24350922483756459028729109)
    ·
      refine ⟨1141449491426084016971677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24350922483756459028729109 1141449491426084016971677)
      ·
        refine ⟨428043559284781506364379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1141449491426084016971677 428043559284781506364379)
        ·
          refine ⟨642065338927172259546569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428043559284781506364379 642065338927172259546569)
          ·
            refine ⟨481549004195379194659927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642065338927172259546569 481549004195379194659927)
            ·
              refine ⟨722323506293068791989891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481549004195379194659927 722323506293068791989891)
              ·
                refine ⟨1083485259439603187984837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722323506293068791989891 1083485259439603187984837)
                ·
                  refine ⟨203153486144925597747157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083485259439603187984837 203153486144925597747157)
                  ·
                    rfl

theorem cell20_445095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_445095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445095 prefixEnd_445095 := by exact prefixLift 445095
  have htrace : WordTrace (prefixWord ++ tailWord_445095) baseStart_445095 baseEnd_445095 := by
    simpa [prefixWord, tailWord_445095, baseEnd_445095] using wordTrace_append hprefix tailTrace_445095
  have hstable : (prefixWord ++ tailWord_445095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445095).length < 2 ^ (prefixWord ++ tailWord_445095).sum := by decide
  have hdescent : baseEnd_445095 < baseStart_445095 := by decide
  rcases family_descends (prefixWord ++ tailWord_445095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445105 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 3]
def baseStart_445105 : Nat := 118140960795 + 445105 * 2 ^ 59
def prefixEnd_445105 : Nat := 4983230072969 + 3 ^ 40 * 445105 * 2
def baseEnd_445105 : Nat := 203158050417410007413783

theorem tailTrace_445105 : CollatzResearch.WordTrace tailWord_445105 prefixEnd_445105 203158050417410007413783 := by
  unfold tailWord_445105
  simp only [CollatzResearch.WordTrace]
  refine ⟨16234313052468077727016769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10822875368312051818011179 16234313052468077727016769)
  ·
    refine ⟨12175734789351058295262577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16234313052468077727016769 12175734789351058295262577)
    ·
      refine ⟨9131801092013293721446933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12175734789351058295262577 9131801092013293721446933)
      ·
        refine ⟨428053176188123143192825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9131801092013293721446933 428053176188123143192825)
        ·
          refine ⟨321039882141092357394619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428053176188123143192825 321039882141092357394619)
          ·
            refine ⟨481559823211638536091929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321039882141092357394619 481559823211638536091929)
            ·
              refine ⟨361169867408728902068947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481559823211638536091929 361169867408728902068947)
              ·
                refine ⟨541754801113093353103421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361169867408728902068947 541754801113093353103421)
                ·
                  refine ⟨203158050417410007413783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541754801113093353103421 203158050417410007413783)
                  ·
                    rfl

theorem cell20_445105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_445105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445105 prefixEnd_445105 := by exact prefixLift 445105
  have htrace : WordTrace (prefixWord ++ tailWord_445105) baseStart_445105 baseEnd_445105 := by
    simpa [prefixWord, tailWord_445105, baseEnd_445105] using wordTrace_append hprefix tailTrace_445105
  have hstable : (prefixWord ++ tailWord_445105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445105).length < 2 ^ (prefixWord ++ tailWord_445105).sum := by decide
  have hdescent : baseEnd_445105 < baseStart_445105 := by decide
  rcases family_descends (prefixWord ++ tailWord_445105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445109 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 3]
def baseStart_445109 : Nat := 118140960795 + 445109 * 2 ^ 59
def prefixEnd_445109 : Nat := 4983230072969 + 3 ^ 40 * 445109 * 2
def baseEnd_445109 : Nat := 203159876126403771280433

theorem tailTrace_445109 : CollatzResearch.WordTrace tailWord_445109 prefixEnd_445109 203159876126403771280433 := by
  unfold tailWord_445109
  simp only [CollatzResearch.WordTrace]
  refine ⟨16234458944453586410162381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10822972629635724273441587 16234458944453586410162381)
  ·
    refine ⟨6087922104170094903810893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16234458944453586410162381 6087922104170094903810893)
    ·
      refine ⟨2282970789063785588929085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6087922104170094903810893 2282970789063785588929085)
      ·
        refine ⟨856114045898919595848407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2282970789063785588929085 856114045898919595848407)
        ·
          refine ⟨1284171068848379393772611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856114045898919595848407 1284171068848379393772611)
          ·
            refine ⟨1926256603272569090658917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284171068848379393772611 1926256603272569090658917)
            ·
              refine ⟨361173113113606704498547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1926256603272569090658917 361173113113606704498547)
              ·
                refine ⟨541759669670410056747821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361173113113606704498547 541759669670410056747821)
                ·
                  refine ⟨203159876126403771280433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541759669670410056747821 203159876126403771280433)
                  ·
                    rfl

theorem cell20_445109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_445109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445109 prefixEnd_445109 := by exact prefixLift 445109
  have htrace : WordTrace (prefixWord ++ tailWord_445109) baseStart_445109 baseEnd_445109 := by
    simpa [prefixWord, tailWord_445109, baseEnd_445109] using wordTrace_append hprefix tailTrace_445109
  have hstable : (prefixWord ++ tailWord_445109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445109).length < 2 ^ (prefixWord ++ tailWord_445109).sum := by decide
  have hdescent : baseEnd_445109 < baseStart_445109 := by decide
  rcases family_descends (prefixWord ++ tailWord_445109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445137 : List Nat := [1, 2, 2, 1, 2, 3, 2, 5, 2]
def baseStart_445137 : Nat := 118140960795 + 445137 * 2 ^ 59
def prefixEnd_445137 : Nat := 4983230072969 + 3 ^ 40 * 445137 * 2
def baseEnd_445137 : Nat := 203172656089360118346985

theorem tailTrace_445137 : CollatzResearch.WordTrace tailWord_445137 prefixEnd_445137 203172656089360118346985 := by
  unfold tailWord_445137
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235480188352147192181665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10823653458901431461454443 16235480188352147192181665)
  ·
    refine ⟨12176610141264110394136249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16235480188352147192181665 12176610141264110394136249)
    ·
      refine ⟨9132457605948082795602187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12176610141264110394136249 9132457605948082795602187)
      ·
        refine ⟨13698686408922124193403281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132457605948082795602187 13698686408922124193403281)
        ·
          refine ⟨10274014806691593145052461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13698686408922124193403281 10274014806691593145052461)
          ·
            refine ⟨3852755552509347429394673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10274014806691593145052461 3852755552509347429394673)
            ·
              refine ⟨2889566664382010572046005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3852755552509347429394673 2889566664382010572046005)
              ·
                refine ⟨270896874785813491129313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2889566664382010572046005 270896874785813491129313)
                ·
                  refine ⟨203172656089360118346985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270896874785813491129313 203172656089360118346985)
                  ·
                    rfl

theorem cell20_445137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_445137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445137 prefixEnd_445137 := by exact prefixLift 445137
  have htrace : WordTrace (prefixWord ++ tailWord_445137) baseStart_445137 baseEnd_445137 := by
    simpa [prefixWord, tailWord_445137, baseEnd_445137] using wordTrace_append hprefix tailTrace_445137
  have hstable : (prefixWord ++ tailWord_445137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445137).length < 2 ^ (prefixWord ++ tailWord_445137).sum := by decide
  have hdescent : baseEnd_445137 < baseStart_445137 := by decide
  rcases family_descends (prefixWord ++ tailWord_445137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445151 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 3]
def baseStart_445151 : Nat := 118140960795 + 445151 * 2 ^ 59
def prefixEnd_445151 : Nat := 4983230072969 + 3 ^ 40 * 445151 * 2
def baseEnd_445151 : Nat := 203179046070838291880261

theorem tailTrace_445151 : CollatzResearch.WordTrace tailWord_445151 prefixEnd_445151 203179046070838291880261 := by
  unfold tailWord_445151
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235990810301427583191307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10823993873534285055460871 16235990810301427583191307)
  ·
    refine ⟨24353986215452141374786961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16235990810301427583191307 24353986215452141374786961)
    ·
      refine ⟨18265489661589106031090221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24353986215452141374786961 18265489661589106031090221)
      ·
        refine ⟨6849558623095914761658833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18265489661589106031090221 6849558623095914761658833)
        ·
          refine ⟨5137168967321936071244125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6849558623095914761658833 5137168967321936071244125)
          ·
            refine ⟨1926438362745726026716547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5137168967321936071244125 1926438362745726026716547)
            ·
              refine ⟨2889657544118589040074821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926438362745726026716547 2889657544118589040074821)
              ·
                refine ⟨541810789522235445014029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2889657544118589040074821 541810789522235445014029)
                ·
                  refine ⟨203179046070838291880261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541810789522235445014029 203179046070838291880261)
                  ·
                    rfl

theorem cell20_445151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_445151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445151 prefixEnd_445151 := by exact prefixLift 445151
  have htrace : WordTrace (prefixWord ++ tailWord_445151) baseStart_445151 baseEnd_445151 := by
    simpa [prefixWord, tailWord_445151, baseEnd_445151] using wordTrace_append hprefix tailTrace_445151
  have hstable : (prefixWord ++ tailWord_445151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445151).length < 2 ^ (prefixWord ++ tailWord_445151).sum := by decide
  have hdescent : baseEnd_445151 < baseStart_445151 := by decide
  rcases family_descends (prefixWord ++ tailWord_445151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445192 : List Nat := [2, 1, 3, 2, 2, 3, 2, 3, 2]
def baseStart_445192 : Nat := 118140960795 + 445192 * 2 ^ 59
def prefixEnd_445192 : Nat := 4983230072969 + 3 ^ 40 * 445192 * 2
def baseEnd_445192 : Nat := 203197759588024371513427

theorem tailTrace_445192 : CollatzResearch.WordTrace tailWord_445192 prefixEnd_445192 203197759588024371513427 := by
  unfold tailWord_445192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118743101576445792716915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10824990802101927723622553 8118743101576445792716915)
  ·
    refine ⟨12178114652364668689075373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8118743101576445792716915 12178114652364668689075373)
    ·
      refine ⟨4566792994636750758403265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12178114652364668689075373 4566792994636750758403265)
      ·
        refine ⟨3425094745977563068802449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4566792994636750758403265 3425094745977563068802449)
        ·
          refine ⟨2568821059483172301601837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3425094745977563068802449 2568821059483172301601837)
          ·
            refine ⟨963307897306189613100689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2568821059483172301601837 963307897306189613100689)
            ·
              refine ⟨722480922979642209825517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963307897306189613100689 722480922979642209825517)
              ·
                refine ⟨270930346117365828684569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722480922979642209825517 270930346117365828684569)
                ·
                  refine ⟨203197759588024371513427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270930346117365828684569 203197759588024371513427)
                  ·
                    rfl

theorem cell20_445192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_445192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445192 prefixEnd_445192 := by exact prefixLift 445192
  have htrace : WordTrace (prefixWord ++ tailWord_445192) baseStart_445192 baseEnd_445192 := by
    simpa [prefixWord, tailWord_445192, baseEnd_445192] using wordTrace_append hprefix tailTrace_445192
  have hstable : (prefixWord ++ tailWord_445192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445192).length < 2 ^ (prefixWord ++ tailWord_445192).sum := by decide
  have hdescent : baseEnd_445192 < baseStart_445192 := by decide
  rcases family_descends (prefixWord ++ tailWord_445192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445202 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_445202 : Nat := 118140960795 + 445202 * 2 ^ 59
def prefixEnd_445202 : Nat := 4983230072969 + 3 ^ 40 * 445202 * 2
def baseEnd_445202 : Nat := 203202323860508781180053

theorem tailTrace_445202 : CollatzResearch.WordTrace tailWord_445202 prefixEnd_445202 203202323860508781180053 := by
  unfold tailWord_445202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059462733279165823324465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10825233955411108862198573 4059462733279165823324465)
  ·
    refine ⟨3044597049959374367493349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4059462733279165823324465 3044597049959374367493349)
    ·
      refine ⟨570861946867382693905003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3044597049959374367493349 570861946867382693905003)
      ·
        refine ⟨856292920301074040857505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570861946867382693905003 856292920301074040857505)
        ·
          refine ⟨642219690225805530643129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856292920301074040857505 642219690225805530643129)
          ·
            refine ⟨481664767669354147982347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642219690225805530643129 481664767669354147982347)
            ·
              refine ⟨722497151504031221973521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481664767669354147982347 722497151504031221973521)
              ·
                refine ⟨541872863628023416480141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722497151504031221973521 541872863628023416480141)
                ·
                  refine ⟨203202323860508781180053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541872863628023416480141 203202323860508781180053)
                  ·
                    rfl

theorem cell20_445202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_445202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445202 prefixEnd_445202 := by exact prefixLift 445202
  have htrace : WordTrace (prefixWord ++ tailWord_445202) baseStart_445202 baseEnd_445202 := by
    simpa [prefixWord, tailWord_445202, baseEnd_445202] using wordTrace_append hprefix tailTrace_445202
  have hstable : (prefixWord ++ tailWord_445202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445202).length < 2 ^ (prefixWord ++ tailWord_445202).sum := by decide
  have hdescent : baseEnd_445202 < baseStart_445202 := by decide
  rcases family_descends (prefixWord ++ tailWord_445202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445234 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_445234 : Nat := 118140960795 + 445234 * 2 ^ 59
def prefixEnd_445234 : Nat := 4983230072969 + 3 ^ 40 * 445234 * 2
def baseEnd_445234 : Nat := 203216929532458892113255

theorem tailTrace_445234 : CollatzResearch.WordTrace tailWord_445234 prefixEnd_445234 203216929532458892113255 := by
  unfold tailWord_445234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059754517250183189615689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10826012046000488505641837 4059754517250183189615689)
  ·
    refine ⟨3044815887937637392211767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4059754517250183189615689 3044815887937637392211767)
    ·
      refine ⟨4567223831906456088317651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3044815887937637392211767 4567223831906456088317651)
      ·
        refine ⟨6850835747859684132476477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4567223831906456088317651 6850835747859684132476477)
        ·
          refine ⟨2569063405447381549678679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6850835747859684132476477 2569063405447381549678679)
          ·
            refine ⟨3853595108171072324518019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569063405447381549678679 3853595108171072324518019)
            ·
              refine ⟨5780392662256608486777029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853595108171072324518019 5780392662256608486777029)
              ·
                refine ⟨1083823624173114091270693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5780392662256608486777029 1083823624173114091270693)
                ·
                  refine ⟨203216929532458892113255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083823624173114091270693 203216929532458892113255)
                  ·
                    rfl

theorem cell20_445234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_445234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445234 prefixEnd_445234 := by exact prefixLift 445234
  have htrace : WordTrace (prefixWord ++ tailWord_445234) baseStart_445234 baseEnd_445234 := by
    simpa [prefixWord, tailWord_445234, baseEnd_445234] using wordTrace_append hprefix tailTrace_445234
  have hstable : (prefixWord ++ tailWord_445234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445234).length < 2 ^ (prefixWord ++ tailWord_445234).sum := by decide
  have hdescent : baseEnd_445234 < baseStart_445234 := by decide
  rcases family_descends (prefixWord ++ tailWord_445234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445237 : List Nat := [1, 3, 3, 1, 3, 3, 2, 4]
def baseStart_445237 : Nat := 118140960795 + 445237 * 2 ^ 59
def prefixEnd_445237 : Nat := 4983230072969 + 3 ^ 40 * 445237 * 2
def baseEnd_445237 : Nat := 67739432938068071671081

theorem tailTrace_445237 : CollatzResearch.WordTrace tailWord_445237 prefixEnd_445237 67739432938068071671081 := by
  unfold tailWord_445237
  simp only [CollatzResearch.WordTrace]
  refine ⟨16239127487989864270821965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10826084991993242847214643 16239127487989864270821965)
  ·
    refine ⟨6089672807996199101558237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16239127487989864270821965 6089672807996199101558237)
    ·
      refine ⟨2283627302998574663084339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6089672807996199101558237 2283627302998574663084339)
      ·
        refine ⟨3425440954497861994626509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283627302998574663084339 3425440954497861994626509)
        ·
          refine ⟨1284540357936698247984941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3425440954497861994626509 1284540357936698247984941)
          ·
            refine ⟨481702634226261842994353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1284540357936698247984941 481702634226261842994353)
            ·
              refine ⟨361276975669696382245765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481702634226261842994353 361276975669696382245765)
              ·
                refine ⟨67739432938068071671081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361276975669696382245765 67739432938068071671081)
                ·
                  rfl

theorem cell20_445237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_445237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445237 prefixEnd_445237 := by exact prefixLift 445237
  have htrace : WordTrace (prefixWord ++ tailWord_445237) baseStart_445237 baseEnd_445237 := by
    simpa [prefixWord, tailWord_445237, baseEnd_445237] using wordTrace_append hprefix tailTrace_445237
  have hstable : (prefixWord ++ tailWord_445237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445237).length < 2 ^ (prefixWord ++ tailWord_445237).sum := by decide
  have hdescent : baseEnd_445237 < baseStart_445237 := by decide
  rcases family_descends (prefixWord ++ tailWord_445237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445254 : List Nat := [6, 1, 1, 2, 2, 2, 6]
def baseStart_445254 : Nat := 118140960795 + 445254 * 2 ^ 59
def prefixEnd_445254 : Nat := 4983230072969 + 3 ^ 40 * 445254 * 2
def baseEnd_445254 : Nat := 22580673119714190160723

theorem tailTrace_445254 : CollatzResearch.WordTrace tailWord_445254 prefixEnd_445254 22580673119714190160723 := by
  unfold tailWord_445254
  simp only [CollatzResearch.WordTrace]
  refine ⟨507492110279008630443463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10826498352618850782793877 507492110279008630443463)
  ·
    refine ⟨761238165418512945665195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 507492110279008630443463 761238165418512945665195)
    ·
      refine ⟨1141857248127769418497793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761238165418512945665195 1141857248127769418497793)
      ·
        refine ⟨856392936095827063873345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141857248127769418497793 856392936095827063873345)
        ·
          refine ⟨642294702071870297905009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856392936095827063873345 642294702071870297905009)
          ·
            refine ⟨481721026553902723428757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642294702071870297905009 481721026553902723428757)
            ·
              refine ⟨22580673119714190160723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 481721026553902723428757 22580673119714190160723)
              ·
                rfl

theorem cell20_445254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 6].length) (baseStart_445254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445254 prefixEnd_445254 := by exact prefixLift 445254
  have htrace : WordTrace (prefixWord ++ tailWord_445254) baseStart_445254 baseEnd_445254 := by
    simpa [prefixWord, tailWord_445254, baseEnd_445254] using wordTrace_append hprefix tailTrace_445254
  have hstable : (prefixWord ++ tailWord_445254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445254).length < 2 ^ (prefixWord ++ tailWord_445254).sum := by decide
  have hdescent : baseEnd_445254 < baseStart_445254 := by decide
  rcases family_descends (prefixWord ++ tailWord_445254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445268 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_445268 : Nat := 118140960795 + 445268 * 2 ^ 59
def prefixEnd_445268 : Nat := 4983230072969 + 3 ^ 40 * 445268 * 2
def baseEnd_445268 : Nat := 203232448058905884979783

theorem tailTrace_445268 : CollatzResearch.WordTrace tailWord_445268 prefixEnd_445268 203232448058905884979783 := by
  unfold tailWord_445268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8120129075438778282600229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10826838767251704376800305 8120129075438778282600229)
  ·
    refine ⟨1522524201644770927987543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8120129075438778282600229 1522524201644770927987543)
    ·
      refine ⟨2283786302467156391981315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522524201644770927987543 2283786302467156391981315)
      ·
        refine ⟨3425679453700734587971973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283786302467156391981315 3425679453700734587971973)
        ·
          refine ⟨642314897568887735244745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3425679453700734587971973 642314897568887735244745)
          ·
            refine ⟨481736173176665801433559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642314897568887735244745 481736173176665801433559)
            ·
              refine ⟨722604259764998702150339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481736173176665801433559 722604259764998702150339)
              ·
                refine ⟨1083906389647498053225509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722604259764998702150339 1083906389647498053225509)
                ·
                  refine ⟨203232448058905884979783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083906389647498053225509 203232448058905884979783)
                  ·
                    rfl

theorem cell20_445268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_445268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445268 prefixEnd_445268 := by exact prefixLift 445268
  have htrace : WordTrace (prefixWord ++ tailWord_445268) baseStart_445268 baseEnd_445268 := by
    simpa [prefixWord, tailWord_445268, baseEnd_445268] using wordTrace_append hprefix tailTrace_445268
  have hstable : (prefixWord ++ tailWord_445268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445268).length < 2 ^ (prefixWord ++ tailWord_445268).sum := by decide
  have hdescent : baseEnd_445268 < baseStart_445268 := by decide
  rcases family_descends (prefixWord ++ tailWord_445268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445279 : List Nat := [1, 1, 2, 3, 1, 3, 4, 5]
def baseStart_445279 : Nat := 118140960795 + 445279 * 2 ^ 59
def prefixEnd_445279 : Nat := 4983230072969 + 3 ^ 40 * 445279 * 2
def baseEnd_445279 : Nat := 67745822919546245204357

theorem tailTrace_445279 : CollatzResearch.WordTrace tailWord_445279 prefixEnd_445279 67745822919546245204357 := by
  unfold tailWord_445279
  simp only [CollatzResearch.WordTrace]
  refine ⟨16240659353837705443850891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10827106235891803629233927 16240659353837705443850891)
  ·
    refine ⟨24360989030756558165776337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16240659353837705443850891 24360989030756558165776337)
    ·
      refine ⟨18270741773067418624332253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24360989030756558165776337 18270741773067418624332253)
      ·
        refine ⟨6851528164900281984124595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18270741773067418624332253 6851528164900281984124595)
        ·
          refine ⟨10277292247350422976186893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851528164900281984124595 10277292247350422976186893)
          ·
            refine ⟨3853984592756408616070085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10277292247350422976186893 3853984592756408616070085)
            ·
              refine ⟨722622111141826615513141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3853984592756408616070085 722622111141826615513141)
              ·
                refine ⟨67745822919546245204357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 722622111141826615513141 67745822919546245204357)
                ·
                  rfl

theorem cell20_445279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_445279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445279 prefixEnd_445279 := by exact prefixLift 445279
  have htrace : WordTrace (prefixWord ++ tailWord_445279) baseStart_445279 baseEnd_445279 := by
    simpa [prefixWord, tailWord_445279, baseEnd_445279] using wordTrace_append hprefix tailTrace_445279
  have hstable : (prefixWord ++ tailWord_445279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445279).length < 2 ^ (prefixWord ++ tailWord_445279).sum := by decide
  have hdescent : baseEnd_445279 < baseStart_445279 := by decide
  rcases family_descends (prefixWord ++ tailWord_445279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445320 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_445320 : Nat := 118140960795 + 445320 * 2 ^ 59
def prefixEnd_445320 : Nat := 4983230072969 + 3 ^ 40 * 445320 * 2
def baseEnd_445320 : Nat := 203256182275824815246237

theorem tailTrace_445320 : CollatzResearch.WordTrace tailWord_445320 prefixEnd_445320 203256182275824815246237 := by
  unfold tailWord_445320
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121077373344584723046707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10828103164459446297395609 8121077373344584723046707)
  ·
    refine ⟨12181616060016877084570061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8121077373344584723046707 12181616060016877084570061)
    ·
      refine ⟨4568106022506328906713773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12181616060016877084570061 4568106022506328906713773)
      ·
        refine ⟨1713039758439873340017665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4568106022506328906713773 1713039758439873340017665)
        ·
          refine ⟨1284779818829905005013249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1713039758439873340017665 1284779818829905005013249)
          ·
            refine ⟨963584864122428753759937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284779818829905005013249 963584864122428753759937)
            ·
              refine ⟨722688648091821565319953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963584864122428753759937 722688648091821565319953)
              ·
                refine ⟨542016486068866173989965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722688648091821565319953 542016486068866173989965)
                ·
                  refine ⟨203256182275824815246237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542016486068866173989965 203256182275824815246237)
                  ·
                    rfl

theorem cell20_445320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_445320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445320 prefixEnd_445320 := by exact prefixLift 445320
  have htrace : WordTrace (prefixWord ++ tailWord_445320) baseStart_445320 baseEnd_445320 := by
    simpa [prefixWord, tailWord_445320, baseEnd_445320] using wordTrace_append hprefix tailTrace_445320
  have hstable : (prefixWord ++ tailWord_445320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445320).length < 2 ^ (prefixWord ++ tailWord_445320).sum := by decide
  have hdescent : baseEnd_445320 < baseStart_445320 := by decide
  rcases family_descends (prefixWord ++ tailWord_445320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445324 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_445324 : Nat := 118140960795 + 445324 * 2 ^ 59
def prefixEnd_445324 : Nat := 4983230072969 + 3 ^ 40 * 445324 * 2
def baseEnd_445324 : Nat := 203258007984818579112887

theorem tailTrace_445324 : CollatzResearch.WordTrace tailWord_445324 prefixEnd_445324 203258007984818579112887 := by
  unfold tailWord_445324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121150319337339064619513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10828200425783118752826017 8121150319337339064619513)
  ·
    refine ⟨6090862739503004298464635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8121150319337339064619513 6090862739503004298464635)
    ·
      refine ⟨9136294109254506447696953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6090862739503004298464635 9136294109254506447696953)
      ·
        refine ⟨6852220581940879835772715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9136294109254506447696953 6852220581940879835772715)
        ·
          refine ⟨10278330872911319753659073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852220581940879835772715 10278330872911319753659073)
          ·
            refine ⟨7708748154683489815244305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10278330872911319753659073 7708748154683489815244305)
            ·
              refine ⟨5781561116012617361433229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7708748154683489815244305 5781561116012617361433229)
              ·
                refine ⟨2168085418504731510537461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5781561116012617361433229 2168085418504731510537461)
                ·
                  refine ⟨203258007984818579112887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2168085418504731510537461 203258007984818579112887)
                  ·
                    rfl

theorem cell20_445324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_445324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445324 prefixEnd_445324 := by exact prefixLift 445324
  have htrace : WordTrace (prefixWord ++ tailWord_445324) baseStart_445324 baseEnd_445324 := by
    simpa [prefixWord, tailWord_445324, baseEnd_445324] using wordTrace_append hprefix tailTrace_445324
  have hstable : (prefixWord ++ tailWord_445324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445324).length < 2 ^ (prefixWord ++ tailWord_445324).sum := by decide
  have hdescent : baseEnd_445324 < baseStart_445324 := by decide
  rcases family_descends (prefixWord ++ tailWord_445324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445330 : List Nat := [3, 2, 3, 2, 3, 1, 1, 5]
def baseStart_445330 : Nat := 118140960795 + 445330 * 2 ^ 59
def prefixEnd_445330 : Nat := 4983230072969 + 3 ^ 40 * 445330 * 2
def baseEnd_445330 : Nat := 67753582182769741637621

theorem tailTrace_445330 : CollatzResearch.WordTrace tailWord_445330 prefixEnd_445330 67753582182769741637621 := by
  unfold tailWord_445330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060629869163235288489361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10828346317768627435971629 4060629869163235288489361)
  ·
    refine ⟨3045472401872426466367021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4060629869163235288489361 3045472401872426466367021)
    ·
      refine ⟨1142052150702159924887633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3045472401872426466367021 1142052150702159924887633)
      ·
        refine ⟨856539113026619943665725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142052150702159924887633 856539113026619943665725)
        ·
          refine ⟨321202167384982478874647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 856539113026619943665725 321202167384982478874647)
          ·
            refine ⟨481803251077473718311971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321202167384982478874647 481803251077473718311971)
            ·
              refine ⟨722704876616210577467957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481803251077473718311971 722704876616210577467957)
              ·
                refine ⟨67753582182769741637621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 722704876616210577467957 67753582182769741637621)
                ·
                  rfl

theorem cell20_445330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_445330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445330 prefixEnd_445330 := by exact prefixLift 445330
  have htrace : WordTrace (prefixWord ++ tailWord_445330) baseStart_445330 baseEnd_445330 := by
    simpa [prefixWord, tailWord_445330, baseEnd_445330] using wordTrace_append hprefix tailTrace_445330
  have hstable : (prefixWord ++ tailWord_445330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445330).length < 2 ^ (prefixWord ++ tailWord_445330).sum := by decide
  have hdescent : baseEnd_445330 < baseStart_445330 := by decide
  rcases family_descends (prefixWord ++ tailWord_445330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445341 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 3]
def baseStart_445341 : Nat := 118140960795 + 445341 * 2 ^ 59
def prefixEnd_445341 : Nat := 4983230072969 + 3 ^ 40 * 445341 * 2
def baseEnd_445341 : Nat := 203265767248042075546151

theorem tailTrace_445341 : CollatzResearch.WordTrace tailWord_445341 prefixEnd_445341 203265767248042075546151 := by
  unfold tailWord_445341
  simp only [CollatzResearch.WordTrace]
  refine ⟨16242920679613090032607877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10828613786408726688405251 16242920679613090032607877)
  ·
    refine ⟨3045547627427454381113977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16242920679613090032607877 3045547627427454381113977)
    ·
      refine ⟨2284160720570590785835483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3045547627427454381113977 2284160720570590785835483)
      ·
        refine ⟨3426241080855886178753225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284160720570590785835483 3426241080855886178753225)
        ·
          refine ⟨2569680810641914634064919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3426241080855886178753225 2569680810641914634064919)
          ·
            refine ⟨3854521215962871951097379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569680810641914634064919 3854521215962871951097379)
            ·
              refine ⟨5781781823944307926646069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854521215962871951097379 5781781823944307926646069)
              ·
                refine ⟨542042045994778868123069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5781781823944307926646069 542042045994778868123069)
                ·
                  refine ⟨203265767248042075546151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542042045994778868123069 203265767248042075546151)
                  ·
                    rfl

theorem cell20_445341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_445341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445341 prefixEnd_445341 := by exact prefixLift 445341
  have htrace : WordTrace (prefixWord ++ tailWord_445341) baseStart_445341 baseEnd_445341 := by
    simpa [prefixWord, tailWord_445341, baseEnd_445341] using wordTrace_append hprefix tailTrace_445341
  have hstable : (prefixWord ++ tailWord_445341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445341).length < 2 ^ (prefixWord ++ tailWord_445341).sum := by decide
  have hdescent : baseEnd_445341 < baseStart_445341 := by decide
  rcases family_descends (prefixWord ++ tailWord_445341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445348 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_445348 : Nat := 118140960795 + 445348 * 2 ^ 59
def prefixEnd_445348 : Nat := 4983230072969 + 3 ^ 40 * 445348 * 2
def baseEnd_445348 : Nat := 203268962238781162312789

theorem tailTrace_445348 : CollatzResearch.WordTrace tailWord_445348 prefixEnd_445348 203268962238781162312789 := by
  unfold tailWord_445348
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121587995293865114056349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10828783993725153485408465 8121587995293865114056349)
  ·
    refine ⟨3045595498235199417771131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8121587995293865114056349 3045595498235199417771131)
    ·
      refine ⟨4568393247352799126656697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045595498235199417771131 4568393247352799126656697)
      ·
        refine ⟨3426294935514599344992523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4568393247352799126656697 3426294935514599344992523)
        ·
          refine ⟨5139442403271899017488785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426294935514599344992523 5139442403271899017488785)
          ·
            refine ⟨3854581802453924263116589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5139442403271899017488785 3854581802453924263116589)
            ·
              refine ⟨1445468175920221598668721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3854581802453924263116589 1445468175920221598668721)
              ·
                refine ⟨1084101131940166199001541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445468175920221598668721 1084101131940166199001541)
                ·
                  refine ⟨203268962238781162312789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084101131940166199001541 203268962238781162312789)
                  ·
                    rfl

theorem cell20_445348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_445348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445348 prefixEnd_445348 := by exact prefixLift 445348
  have htrace : WordTrace (prefixWord ++ tailWord_445348) baseStart_445348 baseEnd_445348 := by
    simpa [prefixWord, tailWord_445348, baseEnd_445348] using wordTrace_append hprefix tailTrace_445348
  have hstable : (prefixWord ++ tailWord_445348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445348).length < 2 ^ (prefixWord ++ tailWord_445348).sum := by decide
  have hdescent : baseEnd_445348 < baseStart_445348 := by decide
  rcases family_descends (prefixWord ++ tailWord_445348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445351 : List Nat := [1, 1, 6, 1, 3, 1, 3, 4]
def baseStart_445351 : Nat := 118140960795 + 445351 * 2 ^ 59
def prefixEnd_445351 : Nat := 4983230072969 + 3 ^ 40 * 445351 * 2
def baseEnd_445351 : Nat := 67756777173508828404259

theorem tailTrace_445351 : CollatzResearch.WordTrace tailWord_445351 prefixEnd_445351 67756777173508828404259 := by
  unfold tailWord_445351
  simp only [CollatzResearch.WordTrace]
  refine ⟨16243285409576861740471907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10828856939717907826981271 16243285409576861740471907)
  ·
    refine ⟨24364928114365292610707861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16243285409576861740471907 24364928114365292610707861)
    ·
      refine ⟨1142106005360873091126931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24364928114365292610707861 1142106005360873091126931)
      ·
        refine ⟨1713159008041309636690397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142106005360873091126931 1713159008041309636690397)
        ·
          refine ⟨642434628015491113758899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1713159008041309636690397 642434628015491113758899)
          ·
            refine ⟨963651942023236670638349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642434628015491113758899 963651942023236670638349)
            ·
              refine ⟨361369478258713751489381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 963651942023236670638349 361369478258713751489381)
              ·
                refine ⟨67756777173508828404259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361369478258713751489381 67756777173508828404259)
                ·
                  rfl

theorem cell20_445351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_445351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445351 prefixEnd_445351 := by exact prefixLift 445351
  have htrace : WordTrace (prefixWord ++ tailWord_445351) baseStart_445351 baseEnd_445351 := by
    simpa [prefixWord, tailWord_445351, baseEnd_445351] using wordTrace_append hprefix tailTrace_445351
  have hstable : (prefixWord ++ tailWord_445351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445351).length < 2 ^ (prefixWord ++ tailWord_445351).sum := by decide
  have hdescent : baseEnd_445351 < baseStart_445351 := by decide
  rcases family_descends (prefixWord ++ tailWord_445351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445441 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 4]
def baseStart_445441 : Nat := 118140960795 + 445441 * 2 ^ 59
def prefixEnd_445441 : Nat := 4983230072969 + 3 ^ 40 * 445441 * 2
def baseEnd_445441 : Nat := 203311409972886172212409

theorem tailTrace_445441 : CollatzResearch.WordTrace tailWord_445441 prefixEnd_445441 203311409972886172212409 := by
  unfold tailWord_445441
  simp only [CollatzResearch.WordTrace]
  refine ⟨16246567979250807111248177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10831045319500538074165451 16246567979250807111248177)
  ·
    refine ⟨12184925984438105333436133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16246567979250807111248177 12184925984438105333436133)
    ·
      refine ⟨2284673622082144750019275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12184925984438105333436133 2284673622082144750019275)
      ·
        refine ⟨3427010433123217125028913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284673622082144750019275 3427010433123217125028913)
        ·
          refine ⟨2570257824842412843771685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3427010433123217125028913 2570257824842412843771685)
          ·
            refine ⟨481923342157952408207191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2570257824842412843771685 481923342157952408207191)
            ·
              refine ⟨722885013236928612310787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481923342157952408207191 722885013236928612310787)
              ·
                refine ⟨1084327519855392918466181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722885013236928612310787 1084327519855392918466181)
                ·
                  refine ⟨203311409972886172212409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084327519855392918466181 203311409972886172212409)
                  ·
                    rfl

theorem cell20_445441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_445441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445441 prefixEnd_445441 := by exact prefixLift 445441
  have htrace : WordTrace (prefixWord ++ tailWord_445441) baseStart_445441 baseEnd_445441 := by
    simpa [prefixWord, tailWord_445441, baseEnd_445441] using wordTrace_append hprefix tailTrace_445441
  have hstable : (prefixWord ++ tailWord_445441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445441).length < 2 ^ (prefixWord ++ tailWord_445441).sum := by decide
  have hdescent : baseEnd_445441 < baseStart_445441 := by decide
  rcases family_descends (prefixWord ++ tailWord_445441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445492 : List Nat := [2, 5, 1, 2, 1, 3, 2, 2, 2]
def baseStart_445492 : Nat := 118140960795 + 445492 * 2 ^ 59
def prefixEnd_445492 : Nat := 4983230072969 + 3 ^ 40 * 445492 * 2
def baseEnd_445492 : Nat := 203334687762556661512201

theorem tailTrace_445492 : CollatzResearch.WordTrace tailWord_445492 prefixEnd_445492 203334687762556661512201 := by
  unfold tailWord_445492
  simp only [CollatzResearch.WordTrace]
  refine ⟨8124214051033021410677365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10832285401377361880903153 8124214051033021410677365)
  ·
    refine ⟨761645067284345757251003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8124214051033021410677365 761645067284345757251003)
    ·
      refine ⟨1142467600926518635876505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761645067284345757251003 1142467600926518635876505)
      ·
        refine ⟨856850700694888976907379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142467600926518635876505 856850700694888976907379)
        ·
          refine ⟨1285276051042333465361069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856850700694888976907379 1285276051042333465361069)
          ·
            refine ⟨481978519140875049510401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1285276051042333465361069 481978519140875049510401)
            ·
              refine ⟨361483889355656287132801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481978519140875049510401 361483889355656287132801)
              ·
                refine ⟨271112917016742215349601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361483889355656287132801 271112917016742215349601)
                ·
                  refine ⟨203334687762556661512201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271112917016742215349601 203334687762556661512201)
                  ·
                    rfl

theorem cell20_445492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_445492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445492 prefixEnd_445492 := by exact prefixLift 445492
  have htrace : WordTrace (prefixWord ++ tailWord_445492) baseStart_445492 baseEnd_445492 := by
    simpa [prefixWord, tailWord_445492, baseEnd_445492] using wordTrace_append hprefix tailTrace_445492
  have hstable : (prefixWord ++ tailWord_445492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445492).length < 2 ^ (prefixWord ++ tailWord_445492).sum := by decide
  have hdescent : baseEnd_445492 < baseStart_445492 := by decide
  rcases family_descends (prefixWord ++ tailWord_445492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445496 : List Nat := [2, 1, 2, 1, 5, 1, 4, 2, 2]
def baseStart_445496 : Nat := 118140960795 + 445496 * 2 ^ 59
def prefixEnd_445496 : Nat := 4983230072969 + 3 ^ 40 * 445496 * 2
def baseEnd_445496 : Nat := 203336513471550425378851

theorem tailTrace_445496 : CollatzResearch.WordTrace tailWord_445496 prefixEnd_445496 203336513471550425378851 := by
  unfold tailWord_445496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8124286997025775752250171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10832382662701034336333561 8124286997025775752250171)
  ·
    refine ⟨12186430495538663628375257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8124286997025775752250171 12186430495538663628375257)
    ·
      refine ⟨9139822871653997721281443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12186430495538663628375257 9139822871653997721281443)
      ·
        refine ⟨13709734307480996581922165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139822871653997721281443 13709734307480996581922165)
        ·
          refine ⟨1285287591326343429555203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13709734307480996581922165 1285287591326343429555203)
          ·
            refine ⟨1927931386989515144332805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285287591326343429555203 1927931386989515144332805)
            ·
              refine ⟨361487135060534089562401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1927931386989515144332805 361487135060534089562401)
              ·
                refine ⟨271115351295400567171801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361487135060534089562401 271115351295400567171801)
                ·
                  refine ⟨203336513471550425378851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271115351295400567171801 203336513471550425378851)
                  ·
                    rfl

theorem cell20_445496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_445496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445496 prefixEnd_445496 := by exact prefixLift 445496
  have htrace : WordTrace (prefixWord ++ tailWord_445496) baseStart_445496 baseEnd_445496 := by
    simpa [prefixWord, tailWord_445496, baseEnd_445496] using wordTrace_append hprefix tailTrace_445496
  have hstable : (prefixWord ++ tailWord_445496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445496).length < 2 ^ (prefixWord ++ tailWord_445496).sum := by decide
  have hdescent : baseEnd_445496 < baseStart_445496 := by decide
  rcases family_descends (prefixWord ++ tailWord_445496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445517 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_445517 : Nat := 118140960795 + 445517 * 2 ^ 59
def prefixEnd_445517 : Nat := 4983230072969 + 3 ^ 40 * 445517 * 2
def baseEnd_445517 : Nat := 203346098443767685678765

theorem tailTrace_445517 : CollatzResearch.WordTrace tailWord_445517 prefixEnd_445517 203346098443767685678765 := by
  unfold tailWord_445517
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249339926975472091014805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10832893284650314727343203 16249339926975472091014805)
  ·
    refine ⟨761687809076975254266319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16249339926975472091014805 761687809076975254266319)
    ·
      refine ⟨1142531713615462881399479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761687809076975254266319 1142531713615462881399479)
      ·
        refine ⟨1713797570423194322099219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142531713615462881399479 1713797570423194322099219)
        ·
          refine ⟨2570696355634791483148829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713797570423194322099219 2570696355634791483148829)
          ·
            refine ⟨964011133363046806180811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2570696355634791483148829 964011133363046806180811)
            ·
              refine ⟨1446016700044570209271217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964011133363046806180811 1446016700044570209271217)
              ·
                refine ⟨1084512525033427656953413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446016700044570209271217 1084512525033427656953413)
                ·
                  refine ⟨203346098443767685678765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084512525033427656953413 203346098443767685678765)
                  ·
                    rfl

theorem cell20_445517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_445517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445517 prefixEnd_445517 := by exact prefixLift 445517
  have htrace : WordTrace (prefixWord ++ tailWord_445517) baseStart_445517 baseEnd_445517 := by
    simpa [prefixWord, tailWord_445517, baseEnd_445517] using wordTrace_append hprefix tailTrace_445517
  have hstable : (prefixWord ++ tailWord_445517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445517).length < 2 ^ (prefixWord ++ tailWord_445517).sum := by decide
  have hdescent : baseEnd_445517 < baseStart_445517 := by decide
  rcases family_descends (prefixWord ++ tailWord_445517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445521 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_445521 : Nat := 118140960795 + 445521 * 2 ^ 59
def prefixEnd_445521 : Nat := 4983230072969 + 3 ^ 40 * 445521 * 2
def baseEnd_445521 : Nat := 203347924152761449545415

theorem tailTrace_445521 : CollatzResearch.WordTrace tailWord_445521 prefixEnd_445521 203347924152761449545415 := by
  unfold tailWord_445521
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249485818960980774160417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10832990545973987182773611 16249485818960980774160417)
  ·
    refine ⟨12187114364220735580620313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16249485818960980774160417 12187114364220735580620313)
    ·
      refine ⟨9140335773165551685465235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12187114364220735580620313 9140335773165551685465235)
      ·
        refine ⟨13710503659748327528197853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9140335773165551685465235 13710503659748327528197853)
        ·
          refine ⟨5141438872405622823074195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13710503659748327528197853 5141438872405622823074195)
          ·
            refine ⟨7712158308608434234611293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141438872405622823074195 7712158308608434234611293)
            ·
              refine ⟨2892059365728162837979235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7712158308608434234611293 2892059365728162837979235)
              ·
                refine ⟨4338089048592244256968853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892059365728162837979235 4338089048592244256968853)
                ·
                  refine ⟨203347924152761449545415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4338089048592244256968853 203347924152761449545415)
                  ·
                    rfl

theorem cell20_445521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_445521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445521 prefixEnd_445521 := by exact prefixLift 445521
  have htrace : WordTrace (prefixWord ++ tailWord_445521) baseStart_445521 baseEnd_445521 := by
    simpa [prefixWord, tailWord_445521, baseEnd_445521] using wordTrace_append hprefix tailTrace_445521
  have hstable : (prefixWord ++ tailWord_445521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445521).length < 2 ^ (prefixWord ++ tailWord_445521).sum := by decide
  have hdescent : baseEnd_445521 < baseStart_445521 := by decide
  rcases family_descends (prefixWord ++ tailWord_445521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445544 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 3]
def baseStart_445544 : Nat := 118140960795 + 445544 * 2 ^ 59
def prefixEnd_445544 : Nat := 4983230072969 + 3 ^ 40 * 445544 * 2
def baseEnd_445544 : Nat := 203358421979475591778655

theorem tailTrace_445544 : CollatzResearch.WordTrace tailWord_445544 prefixEnd_445544 203358421979475591778655 := by
  unfold tailWord_445544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125162348938827851123843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10833549798585103801498457 8125162348938827851123843)
  ·
    refine ⟨12187743523408241776685765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125162348938827851123843 12187743523408241776685765)
    ·
      refine ⟨2285201910639045333128581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12187743523408241776685765 2285201910639045333128581)
      ·
        refine ⟨428475358244820999961609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2285201910639045333128581 428475358244820999961609)
        ·
          refine ⟨321356518683615749971207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428475358244820999961609 321356518683615749971207)
          ·
            refine ⟨482034778025423624956811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321356518683615749971207 482034778025423624956811)
            ·
              refine ⟨723052167038135437435217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482034778025423624956811 723052167038135437435217)
              ·
                refine ⟨542289125278601578076413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723052167038135437435217 542289125278601578076413)
                ·
                  refine ⟨203358421979475591778655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542289125278601578076413 203358421979475591778655)
                  ·
                    rfl

theorem cell20_445544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_445544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445544 prefixEnd_445544 := by exact prefixLift 445544
  have htrace : WordTrace (prefixWord ++ tailWord_445544) baseStart_445544 baseEnd_445544 := by
    simpa [prefixWord, tailWord_445544, baseEnd_445544] using wordTrace_append hprefix tailTrace_445544
  have hstable : (prefixWord ++ tailWord_445544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445544).length < 2 ^ (prefixWord ++ tailWord_445544).sum := by decide
  have hdescent : baseEnd_445544 < baseStart_445544 := by decide
  rcases family_descends (prefixWord ++ tailWord_445544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445552 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_445552 : Nat := 118140960795 + 445552 * 2 ^ 59
def prefixEnd_445552 : Nat := 4983230072969 + 3 ^ 40 * 445552 * 2
def baseEnd_445552 : Nat := 203362073397463119511955

theorem tailTrace_445552 : CollatzResearch.WordTrace tailWord_445552 prefixEnd_445552 203362073397463119511955 := by
  unfold tailWord_445552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125308240924336534269455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10833744321232448712359273 8125308240924336534269455)
  ·
    refine ⟨12187962361386504801404183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125308240924336534269455 12187962361386504801404183)
    ·
      refine ⟨18281943542079757202106275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12187962361386504801404183 18281943542079757202106275)
      ·
        refine ⟨27422915313119635803159413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18281943542079757202106275 27422915313119635803159413)
        ·
          refine ⟨2570898310604965856546195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27422915313119635803159413 2570898310604965856546195)
          ·
            refine ⟨3856347465907448784819293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570898310604965856546195 3856347465907448784819293)
            ·
              refine ⟨1446130299715293294307235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3856347465907448784819293 1446130299715293294307235)
              ·
                refine ⟨2169195449572939941460853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446130299715293294307235 2169195449572939941460853)
                ·
                  refine ⟨203362073397463119511955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2169195449572939941460853 203362073397463119511955)
                  ·
                    rfl

theorem cell20_445552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_445552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445552 prefixEnd_445552 := by exact prefixLift 445552
  have htrace : WordTrace (prefixWord ++ tailWord_445552) baseStart_445552 baseEnd_445552 := by
    simpa [prefixWord, tailWord_445552, baseEnd_445552] using wordTrace_append hprefix tailTrace_445552
  have hstable : (prefixWord ++ tailWord_445552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445552).length < 2 ^ (prefixWord ++ tailWord_445552).sum := by decide
  have hdescent : baseEnd_445552 < baseStart_445552 := by decide
  rcases family_descends (prefixWord ++ tailWord_445552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445607 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_445607 : Nat := 118140960795 + 445607 * 2 ^ 59
def prefixEnd_445607 : Nat := 4983230072969 + 3 ^ 40 * 445607 * 2
def baseEnd_445607 : Nat := 203387176896127372678397

theorem tailTrace_445607 : CollatzResearch.WordTrace tailWord_445607 prefixEnd_445607 203387176896127372678397 := by
  unfold tailWord_445607
  simp only [CollatzResearch.WordTrace]
  refine ⟨16252622496649417461791075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10835081664432944974527383 16252622496649417461791075)
  ·
    refine ⟨24378933744974126192686613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16252622496649417461791075 24378933744974126192686613)
    ·
      refine ⟨1142762519295662165282185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24378933744974126192686613 1142762519295662165282185)
      ·
        refine ⟨857071889471746623961639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142762519295662165282185 857071889471746623961639)
        ·
          refine ⟨1285607834207619935942459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857071889471746623961639 1285607834207619935942459)
          ·
            refine ⟨1928411751311429903913689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285607834207619935942459 1928411751311429903913689)
            ·
              refine ⟨1446308813483572427935267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928411751311429903913689 1446308813483572427935267)
              ·
                refine ⟨2169463220225358641902901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446308813483572427935267 2169463220225358641902901)
                ·
                  refine ⟨203387176896127372678397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2169463220225358641902901 203387176896127372678397)
                  ·
                    rfl

theorem cell20_445607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_445607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445607 prefixEnd_445607 := by exact prefixLift 445607
  have htrace : WordTrace (prefixWord ++ tailWord_445607) baseStart_445607 baseEnd_445607 := by
    simpa [prefixWord, tailWord_445607, baseEnd_445607] using wordTrace_append hprefix tailTrace_445607
  have hstable : (prefixWord ++ tailWord_445607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445607).length < 2 ^ (prefixWord ++ tailWord_445607).sum := by decide
  have hdescent : baseEnd_445607 < baseStart_445607 := by decide
  rcases family_descends (prefixWord ++ tailWord_445607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445610 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_445610 : Nat := 118140960795 + 445610 * 2 ^ 59
def prefixEnd_445610 : Nat := 4983230072969 + 3 ^ 40 * 445610 * 2
def baseEnd_445610 : Nat := 203388546177872695578385

theorem tailTrace_445610 : CollatzResearch.WordTrace tailWord_445610 prefixEnd_445610 203388546177872695578385 := by
  unfold tailWord_445610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063182978909637243537571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10835154610425699316100189 4063182978909637243537571)
  ·
    refine ⟨6094774468364455865306357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4063182978909637243537571 6094774468364455865306357)
    ·
      refine ⟨571385106409167737372471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6094774468364455865306357 571385106409167737372471)
      ·
        refine ⟨857077659613751606058707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571385106409167737372471 857077659613751606058707)
        ·
          refine ⟨1285616489420627409088061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857077659613751606058707 1285616489420627409088061)
          ·
            refine ⟨482106183532735278408023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1285616489420627409088061 482106183532735278408023)
            ·
              refine ⟨723159275299102917612035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482106183532735278408023 723159275299102917612035)
              ·
                refine ⟨1084738912948654376418053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723159275299102917612035 1084738912948654376418053)
                ·
                  refine ⟨203388546177872695578385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084738912948654376418053 203388546177872695578385)
                  ·
                    rfl

theorem cell20_445610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_445610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445610 prefixEnd_445610 := by exact prefixLift 445610
  have htrace : WordTrace (prefixWord ++ tailWord_445610) baseStart_445610 baseEnd_445610 := by
    simpa [prefixWord, tailWord_445610, baseEnd_445610] using wordTrace_append hprefix tailTrace_445610
  have hstable : (prefixWord ++ tailWord_445610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445610).length < 2 ^ (prefixWord ++ tailWord_445610).sum := by decide
  have hdescent : baseEnd_445610 < baseStart_445610 := by decide
  rcases family_descends (prefixWord ++ tailWord_445610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445707 : List Nat := [1, 1, 1, 1, 5, 4, 2, 3, 2]
def baseStart_445707 : Nat := 118140960795 + 445707 * 2 ^ 59
def prefixEnd_445707 : Nat := 4983230072969 + 3 ^ 40 * 445707 * 2
def baseEnd_445707 : Nat := 203432819620971469344655

theorem tailTrace_445707 : CollatzResearch.WordTrace tailWord_445707 prefixEnd_445707 203432819620971469344655 := by
  unfold tailWord_445707
  simp only [CollatzResearch.WordTrace]
  refine ⟨16256269796287134540431375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10837513197524756360287583 16256269796287134540431375)
  ·
    refine ⟨24384404694430701810647063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16256269796287134540431375 24384404694430701810647063)
    ·
      refine ⟨36576607041646052715970595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24384404694430701810647063 36576607041646052715970595)
      ·
        refine ⟨54864910562469079073955893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36576607041646052715970595 54864910562469079073955893)
        ·
          refine ⟨5143585365231476163183365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54864910562469079073955893 5143585365231476163183365)
          ·
            refine ⟨964422255980901780596881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5143585365231476163183365 964422255980901780596881)
            ·
              refine ⟨723316691985676335447661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964422255980901780596881 723316691985676335447661)
              ·
                refine ⟨271243759494628625792873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 723316691985676335447661 271243759494628625792873)
                ·
                  refine ⟨203432819620971469344655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271243759494628625792873 203432819620971469344655)
                  ·
                    rfl

theorem cell20_445707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 2].length) (baseStart_445707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445707 prefixEnd_445707 := by exact prefixLift 445707
  have htrace : WordTrace (prefixWord ++ tailWord_445707) baseStart_445707 baseEnd_445707 := by
    simpa [prefixWord, tailWord_445707, baseEnd_445707] using wordTrace_append hprefix tailTrace_445707
  have hstable : (prefixWord ++ tailWord_445707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445707).length < 2 ^ (prefixWord ++ tailWord_445707).sum := by decide
  have hdescent : baseEnd_445707 < baseStart_445707 := by decide
  rcases family_descends (prefixWord ++ tailWord_445707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445780 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_445780 : Nat := 118140960795 + 445780 * 2 ^ 59
def prefixEnd_445780 : Nat := 4983230072969 + 3 ^ 40 * 445780 * 2
def baseEnd_445780 : Nat := 203466138810107659911023

theorem tailTrace_445780 : CollatzResearch.WordTrace tailWord_445780 prefixEnd_445780 203466138810107659911023 := by
  unfold tailWord_445780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8129466162511334003919397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10839288216681778671892529 8129466162511334003919397)
  ·
    refine ⟨1524274905470875125734887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8129466162511334003919397 1524274905470875125734887)
    ·
      refine ⟨2286412358206312688602331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524274905470875125734887 2286412358206312688602331)
      ·
        refine ⟨3429618537309469032903497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286412358206312688602331 3429618537309469032903497)
        ·
          refine ⟨2572213902982101774677623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429618537309469032903497 2572213902982101774677623)
          ·
            refine ⟨3858320854473152662016435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572213902982101774677623 3858320854473152662016435)
            ·
              refine ⟨5787481281709728993024653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858320854473152662016435 5787481281709728993024653)
              ·
                refine ⟨2170305480641148372384245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5787481281709728993024653 2170305480641148372384245)
                ·
                  refine ⟨203466138810107659911023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2170305480641148372384245 203466138810107659911023)
                  ·
                    rfl

theorem cell20_445780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_445780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445780 prefixEnd_445780 := by exact prefixLift 445780
  have htrace : WordTrace (prefixWord ++ tailWord_445780) baseStart_445780 baseEnd_445780 := by
    simpa [prefixWord, tailWord_445780, baseEnd_445780] using wordTrace_append hprefix tailTrace_445780
  have hstable : (prefixWord ++ tailWord_445780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445780).length < 2 ^ (prefixWord ++ tailWord_445780).sum := by decide
  have hdescent : baseEnd_445780 < baseStart_445780 := by decide
  rcases family_descends (prefixWord ++ tailWord_445780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445789 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 3]
def baseStart_445789 : Nat := 118140960795 + 445789 * 2 ^ 59
def prefixEnd_445789 : Nat := 4983230072969 + 3 ^ 40 * 445789 * 2
def baseEnd_445789 : Nat := 203470246655343628610987

theorem tailTrace_445789 : CollatzResearch.WordTrace tailWord_445789 prefixEnd_445789 203470246655343628610987 := by
  unfold tailWord_445789
  simp only [CollatzResearch.WordTrace]
  refine ⟨16259260581990062544916421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10839507054660041696610947 16259260581990062544916421)
  ·
    refine ⟨3048611359123136727171829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16259260581990062544916421 3048611359123136727171829)
    ·
      refine ⟨285807314917794068172359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3048611359123136727171829 285807314917794068172359)
      ·
        refine ⟨428710972376691102258539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285807314917794068172359 428710972376691102258539)
        ·
          refine ⟨643066458565036653387809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428710972376691102258539 643066458565036653387809)
          ·
            refine ⟨482299843923777490040857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643066458565036653387809 482299843923777490040857)
            ·
              refine ⟨361724882942833117530643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482299843923777490040857 361724882942833117530643)
              ·
                refine ⟨542587324414249676295965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361724882942833117530643 542587324414249676295965)
                ·
                  refine ⟨203470246655343628610987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542587324414249676295965 203470246655343628610987)
                  ·
                    rfl

theorem cell20_445789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_445789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445789 prefixEnd_445789 := by exact prefixLift 445789
  have htrace : WordTrace (prefixWord ++ tailWord_445789) baseStart_445789 baseEnd_445789 := by
    simpa [prefixWord, tailWord_445789, baseEnd_445789] using wordTrace_append hprefix tailTrace_445789
  have hstable : (prefixWord ++ tailWord_445789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445789).length < 2 ^ (prefixWord ++ tailWord_445789).sum := by decide
  have hdescent : baseEnd_445789 < baseStart_445789 := by decide
  rcases family_descends (prefixWord ++ tailWord_445789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445801 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_445801 : Nat := 118140960795 + 445801 * 2 ^ 59
def prefixEnd_445801 : Nat := 4983230072969 + 3 ^ 40 * 445801 * 2
def baseEnd_445801 : Nat := 203475723782324920210937

theorem tailTrace_445801 : CollatzResearch.WordTrace tailWord_445801 prefixEnd_445801 203475723782324920210937 := by
  unfold tailWord_445801
  simp only [CollatzResearch.WordTrace]
  refine ⟨16259698257946588594353257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10839798838631059062902171 16259698257946588594353257)
  ·
    refine ⟨12194773693459941445764943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16259698257946588594353257 12194773693459941445764943)
    ·
      refine ⟨18292160540189912168647415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12194773693459941445764943 18292160540189912168647415)
      ·
        refine ⟨27438240810284868252971123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18292160540189912168647415 27438240810284868252971123)
        ·
          refine ⟨41157361215427302379456685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27438240810284868252971123 41157361215427302379456685)
          ·
            refine ⟨15434010455785238392296257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41157361215427302379456685 15434010455785238392296257)
            ·
              refine ⟨11575507841838928794222193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15434010455785238392296257 11575507841838928794222193)
              ·
                refine ⟨8681630881379196595666645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11575507841838928794222193 8681630881379196595666645)
                ·
                  refine ⟨203475723782324920210937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8681630881379196595666645 203475723782324920210937)
                  ·
                    rfl

theorem cell20_445801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_445801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445801 prefixEnd_445801 := by exact prefixLift 445801
  have htrace : WordTrace (prefixWord ++ tailWord_445801) baseStart_445801 baseEnd_445801 := by
    simpa [prefixWord, tailWord_445801, baseEnd_445801] using wordTrace_append hprefix tailTrace_445801
  have hstable : (prefixWord ++ tailWord_445801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445801).length < 2 ^ (prefixWord ++ tailWord_445801).sum := by decide
  have hdescent : baseEnd_445801 < baseStart_445801 := by decide
  rcases family_descends (prefixWord ++ tailWord_445801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445832 : List Nat := [2, 1, 3, 3, 1, 10]
def baseStart_445832 : Nat := 118140960795 + 445832 * 2 ^ 59
def prefixEnd_445832 : Nat := 4983230072969 + 3 ^ 40 * 445832 * 2
def baseEnd_445832 : Nat := 7536661963963947784351

theorem tailTrace_445832 : CollatzResearch.WordTrace tailWord_445832 prefixEnd_445832 7536661963963947784351 := by
  unfold tailWord_445832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130414460417140444365875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10840552613889520592487833 8130414460417140444365875)
  ·
    refine ⟨12195621690625710666548813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8130414460417140444365875 12195621690625710666548813)
    ·
      refine ⟨4573358133984641499955805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12195621690625710666548813 4573358133984641499955805)
      ·
        refine ⟨1715009300244240562483427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4573358133984641499955805 1715009300244240562483427)
        ·
          refine ⟨2572513950366360843725141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715009300244240562483427 2572513950366360843725141)
          ·
            refine ⟨7536661963963947784351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2572513950366360843725141 7536661963963947784351)
            ·
              rfl

theorem cell20_445832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 10].length) (baseStart_445832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445832 prefixEnd_445832 := by exact prefixLift 445832
  have htrace : WordTrace (prefixWord ++ tailWord_445832) baseStart_445832 baseEnd_445832 := by
    simpa [prefixWord, tailWord_445832, baseEnd_445832] using wordTrace_append hprefix tailTrace_445832
  have hstable : (prefixWord ++ tailWord_445832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445832).length < 2 ^ (prefixWord ++ tailWord_445832).sum := by decide
  have hdescent : baseEnd_445832 < baseStart_445832 := by decide
  rcases family_descends (prefixWord ++ tailWord_445832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445838 : List Nat := [4, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_445838 : Nat := 118140960795 + 445838 * 2 ^ 59
def prefixEnd_445838 : Nat := 4983230072969 + 3 ^ 40 * 445838 * 2
def baseEnd_445838 : Nat := 203492611590517235977453

theorem tailTrace_445838 : CollatzResearch.WordTrace tailWord_445838 prefixEnd_445838 203492611590517235977453 := by
  unfold tailWord_445838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032630969851567989181271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10840698505875029275633445 2032630969851567989181271)
  ·
    refine ⟨3048946454777351983771907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2032630969851567989181271 3048946454777351983771907)
    ·
      refine ⟨4573419682166027975657861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3048946454777351983771907 4573419682166027975657861)
      ·
        refine ⟨857516190406130245435849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4573419682166027975657861 857516190406130245435849)
        ·
          refine ⟨643137142804597684076887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857516190406130245435849 643137142804597684076887)
          ·
            refine ⟨964705714206896526115331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643137142804597684076887 964705714206896526115331)
            ·
              refine ⟨1447058571310344789172997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964705714206896526115331 1447058571310344789172997)
              ·
                refine ⟨271323482120689647969937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1447058571310344789172997 271323482120689647969937)
                ·
                  refine ⟨203492611590517235977453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271323482120689647969937 203492611590517235977453)
                  ·
                    rfl

theorem cell20_445838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_445838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445838 prefixEnd_445838 := by exact prefixLift 445838
  have htrace : WordTrace (prefixWord ++ tailWord_445838) baseStart_445838 baseEnd_445838 := by
    simpa [prefixWord, tailWord_445838, baseEnd_445838] using wordTrace_append hprefix tailTrace_445838
  have hstable : (prefixWord ++ tailWord_445838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445838).length < 2 ^ (prefixWord ++ tailWord_445838).sum := by decide
  have hdescent : baseEnd_445838 < baseStart_445838 := by decide
  rcases family_descends (prefixWord ++ tailWord_445838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445849 : List Nat := [1, 2, 1, 2, 1, 7, 1, 5]
def baseStart_445849 : Nat := 118140960795 + 445849 * 2 ^ 59
def prefixEnd_445849 : Nat := 4983230072969 + 3 ^ 40 * 445849 * 2
def baseEnd_445849 : Nat := 67832544096750028870247

theorem tailTrace_445849 : CollatzResearch.WordTrace tailWord_445849 prefixEnd_445849 67832544096750028870247 := by
  unfold tailWord_445849
  simp only [CollatzResearch.WordTrace]
  refine ⟨16261448961772692792100601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10840965974515128528067067 16261448961772692792100601)
  ·
    refine ⟨12196086721329519594075451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16261448961772692792100601 12196086721329519594075451)
    ·
      refine ⟨18294130081994279391113177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12196086721329519594075451 18294130081994279391113177)
      ·
        refine ⟨13720597561495709543334883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18294130081994279391113177 13720597561495709543334883)
        ·
          refine ⟨20580896342243564315002325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13720597561495709543334883 20580896342243564315002325)
          ·
            refine ⟨482364758021333538632867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20580896342243564315002325 482364758021333538632867)
            ·
              refine ⟨723547137032000307949301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482364758021333538632867 723547137032000307949301)
              ·
                refine ⟨67832544096750028870247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 723547137032000307949301 67832544096750028870247)
                ·
                  rfl

theorem cell20_445849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_445849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445849 prefixEnd_445849 := by exact prefixLift 445849
  have htrace : WordTrace (prefixWord ++ tailWord_445849) baseStart_445849 baseEnd_445849 := by
    simpa [prefixWord, tailWord_445849, baseEnd_445849] using wordTrace_append hprefix tailTrace_445849
  have hstable : (prefixWord ++ tailWord_445849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445849).length < 2 ^ (prefixWord ++ tailWord_445849).sum := by decide
  have hdescent : baseEnd_445849 < baseStart_445849 := by decide
  rcases family_descends (prefixWord ++ tailWord_445849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445856 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_445856 : Nat := 118140960795 + 445856 * 2 ^ 59
def prefixEnd_445856 : Nat := 4983230072969 + 3 ^ 40 * 445856 * 2
def baseEnd_445856 : Nat := 203500827280989173377379

theorem tailTrace_445856 : CollatzResearch.WordTrace tailWord_445856 prefixEnd_445856 203500827280989173377379 := by
  unfold tailWord_445856
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130852136373666493802711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10841136181831555325070281 8130852136373666493802711)
  ·
    refine ⟨12196278204560499740704067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8130852136373666493802711 12196278204560499740704067)
    ·
      refine ⟨18294417306840749611056101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12196278204560499740704067 18294417306840749611056101)
      ·
        refine ⟨3430203245032640552073019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18294417306840749611056101 3430203245032640552073019)
        ·
          refine ⟨5145304867548960828109529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3430203245032640552073019 5145304867548960828109529)
          ·
            refine ⟨3858978650661720621082147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5145304867548960828109529 3858978650661720621082147)
            ·
              refine ⟨5788467975992580931623221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858978650661720621082147 5788467975992580931623221)
              ·
                refine ⟨542668872749304462339677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5788467975992580931623221 542668872749304462339677)
                ·
                  refine ⟨203500827280989173377379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542668872749304462339677 203500827280989173377379)
                  ·
                    rfl

theorem cell20_445856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_445856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445856 prefixEnd_445856 := by exact prefixLift 445856
  have htrace : WordTrace (prefixWord ++ tailWord_445856) baseStart_445856 baseEnd_445856 := by
    simpa [prefixWord, tailWord_445856, baseEnd_445856] using wordTrace_append hprefix tailTrace_445856
  have hstable : (prefixWord ++ tailWord_445856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445856).length < 2 ^ (prefixWord ++ tailWord_445856).sum := by decide
  have hdescent : baseEnd_445856 < baseStart_445856 := by decide
  rcases family_descends (prefixWord ++ tailWord_445856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445880 : List Nat := [2, 1, 2, 1, 2, 2, 3, 5, 2]
def baseStart_445880 : Nat := 118140960795 + 445880 * 2 ^ 59
def prefixEnd_445880 : Nat := 4983230072969 + 3 ^ 40 * 445880 * 2
def baseEnd_445880 : Nat := 203511781534951756577281

theorem tailTrace_445880 : CollatzResearch.WordTrace tailWord_445880 prefixEnd_445880 203511781534951756577281 := by
  unfold tailWord_445880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131289812330192543239547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10841719749773590057652729 8131289812330192543239547)
  ·
    refine ⟨12196934718495288814859321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8131289812330192543239547 12196934718495288814859321)
    ·
      refine ⟨9147701038871466611144491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12196934718495288814859321 9147701038871466611144491)
      ·
        refine ⟨13721551558307199916716737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9147701038871466611144491 13721551558307199916716737)
        ·
          refine ⟨10291163668730399937537553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13721551558307199916716737 10291163668730399937537553)
          ·
            refine ⟨7718372751547799953153165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10291163668730399937537553 7718372751547799953153165)
            ·
              refine ⟨2894389781830424982432437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7718372751547799953153165 2894389781830424982432437)
              ·
                refine ⟨271349042046602342103041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2894389781830424982432437 271349042046602342103041)
                ·
                  refine ⟨203511781534951756577281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271349042046602342103041 203511781534951756577281)
                  ·
                    rfl

theorem cell20_445880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_445880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445880 prefixEnd_445880 := by exact prefixLift 445880
  have htrace : WordTrace (prefixWord ++ tailWord_445880) baseStart_445880 baseEnd_445880 := by
    simpa [prefixWord, tailWord_445880, baseEnd_445880] using wordTrace_append hprefix tailTrace_445880
  have hstable : (prefixWord ++ tailWord_445880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445880).length < 2 ^ (prefixWord ++ tailWord_445880).sum := by decide
  have hdescent : baseEnd_445880 < baseStart_445880 := by decide
  rcases family_descends (prefixWord ++ tailWord_445880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445925 : List Nat := [1, 3, 1, 5, 1, 2, 1, 6]
def baseStart_445925 : Nat := 118140960795 + 445925 * 2 ^ 59
def prefixEnd_445925 : Nat := 4983230072969 + 3 ^ 40 * 445925 * 2
def baseEnd_445925 : Nat := 67844106920377200025699

theorem tailTrace_445925 : CollatzResearch.WordTrace tailWord_445925 prefixEnd_445925 67844106920377200025699 := by
  unfold tailWord_445925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16264220909497357771867229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10842813939664905181244819 16264220909497357771867229)
  ·
    refine ⟨6099082841061509164450211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16264220909497357771867229 6099082841061509164450211)
    ·
      refine ⟨9148624261592263746675317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6099082841061509164450211 9148624261592263746675317)
      ·
        refine ⟨857683524524274726250811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9148624261592263746675317 857683524524274726250811)
        ·
          refine ⟨1286525286786412089376217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857683524524274726250811 1286525286786412089376217)
          ·
            refine ⟨964893965089809067032163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286525286786412089376217 964893965089809067032163)
            ·
              refine ⟨1447340947634713600548245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964893965089809067032163 1447340947634713600548245)
              ·
                refine ⟨67844106920377200025699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1447340947634713600548245 67844106920377200025699)
                ·
                  rfl

theorem cell20_445925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_445925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445925 prefixEnd_445925 := by exact prefixLift 445925
  have htrace : WordTrace (prefixWord ++ tailWord_445925) baseStart_445925 baseEnd_445925 := by
    simpa [prefixWord, tailWord_445925, baseEnd_445925] using wordTrace_append hprefix tailTrace_445925
  have hstable : (prefixWord ++ tailWord_445925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445925).length < 2 ^ (prefixWord ++ tailWord_445925).sum := by decide
  have hdescent : baseEnd_445925 < baseStart_445925 := by decide
  rcases family_descends (prefixWord ++ tailWord_445925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445958 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_445958 : Nat := 118140960795 + 445958 * 2 ^ 59
def prefixEnd_445958 : Nat := 4983230072969 + 3 ^ 40 * 445958 * 2
def baseEnd_445958 : Nat := 203547382860330151976963

theorem tailTrace_445958 : CollatzResearch.WordTrace tailWord_445958 prefixEnd_445958 203547382860330151976963 := by
  unfold tailWord_445958
  simp only [CollatzResearch.WordTrace]
  refine ⟨508294516199306387744329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10843616345585202938545685 508294516199306387744329)
  ·
    refine ⟨381220887149479790808247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 508294516199306387744329 381220887149479790808247)
    ·
      refine ⟨571831330724219686212371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381220887149479790808247 571831330724219686212371)
      ·
        refine ⟨857746996086329529318557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571831330724219686212371 857746996086329529318557)
        ·
          refine ⟨321655123532373573494459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 857746996086329529318557 321655123532373573494459)
          ·
            refine ⟨482482685298560360241689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321655123532373573494459 482482685298560360241689)
            ·
              refine ⟨361862013973920270181267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482482685298560360241689 361862013973920270181267)
              ·
                refine ⟨542793020960880405271901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361862013973920270181267 542793020960880405271901)
                ·
                  refine ⟨203547382860330151976963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542793020960880405271901 203547382860330151976963)
                  ·
                    rfl

theorem cell20_445958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_445958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445958 prefixEnd_445958 := by exact prefixLift 445958
  have htrace : WordTrace (prefixWord ++ tailWord_445958) baseStart_445958 baseEnd_445958 := by
    simpa [prefixWord, tailWord_445958, baseEnd_445958] using wordTrace_append hprefix tailTrace_445958
  have hstable : (prefixWord ++ tailWord_445958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445958).length < 2 ^ (prefixWord ++ tailWord_445958).sum := by decide
  have hdescent : baseEnd_445958 < baseStart_445958 := by decide
  rcases family_descends (prefixWord ++ tailWord_445958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445963 : List Nat := [1, 1, 1, 1, 8, 1, 2, 5]
def baseStart_445963 : Nat := 118140960795 + 445963 * 2 ^ 59
def prefixEnd_445963 : Nat := 4983230072969 + 3 ^ 40 * 445963 * 2
def baseEnd_445963 : Nat := 67849888332190785603425

theorem tailTrace_445963 : CollatzResearch.WordTrace tailWord_445963 prefixEnd_445963 67849888332190785603425 := by
  unfold tailWord_445963
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265606883359690261750543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10843737922239793507833695 16265606883359690261750543)
  ·
    refine ⟨24398410325039535392625815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16265606883359690261750543 24398410325039535392625815)
    ·
      refine ⟨36597615487559303088938723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24398410325039535392625815 36597615487559303088938723)
      ·
        refine ⟨54896423231338954633408085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36597615487559303088938723 54896423231338954633408085)
        ·
          refine ⟨643317459742253374610251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 54896423231338954633408085 643317459742253374610251)
          ·
            refine ⟨964976189613380061915377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643317459742253374610251 964976189613380061915377)
            ·
              refine ⟨723732142210035046436533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964976189613380061915377 723732142210035046436533)
              ·
                refine ⟨67849888332190785603425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 723732142210035046436533 67849888332190785603425)
                ·
                  rfl

theorem cell20_445963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_445963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_445963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_445963 prefixEnd_445963 := by exact prefixLift 445963
  have htrace : WordTrace (prefixWord ++ tailWord_445963) baseStart_445963 baseEnd_445963 := by
    simpa [prefixWord, tailWord_445963, baseEnd_445963] using wordTrace_append hprefix tailTrace_445963
  have hstable : (prefixWord ++ tailWord_445963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445963).length < 2 ^ (prefixWord ++ tailWord_445963).sum := by decide
  have hdescent : baseEnd_445963 < baseStart_445963 := by decide
  rcases family_descends (prefixWord ++ tailWord_445963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446008 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_446008 : Nat := 118140960795 + 446008 * 2 ^ 59
def prefixEnd_446008 : Nat := 4983230072969 + 3 ^ 40 * 446008 * 2
def baseEnd_446008 : Nat := 203570204222752200310091

theorem tailTrace_446008 : CollatzResearch.WordTrace tailWord_446008 prefixEnd_446008 203570204222752200310091 := by
  unfold tailWord_446008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133624084098331473569339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10844832112131108631425785 8133624084098331473569339)
  ·
    refine ⟨12200436126147497210354009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8133624084098331473569339 12200436126147497210354009)
    ·
      refine ⟨9150327094610622907765507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12200436126147497210354009 9150327094610622907765507)
      ·
        refine ⟨13725490641915934361648261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9150327094610622907765507 13725490641915934361648261)
        ·
          refine ⟨2573529495359237692809049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13725490641915934361648261 2573529495359237692809049)
          ·
            refine ⟨1930147121519428269606787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2573529495359237692809049 1930147121519428269606787)
            ·
              refine ⟨2895220682279142404410181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930147121519428269606787 2895220682279142404410181)
              ·
                refine ⟨542853877927339200826909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2895220682279142404410181 542853877927339200826909)
                ·
                  refine ⟨203570204222752200310091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542853877927339200826909 203570204222752200310091)
                  ·
                    rfl

theorem cell20_446008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_446008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446008 prefixEnd_446008 := by exact prefixLift 446008
  have htrace : WordTrace (prefixWord ++ tailWord_446008) baseStart_446008 baseEnd_446008 := by
    simpa [prefixWord, tailWord_446008, baseEnd_446008] using wordTrace_append hprefix tailTrace_446008
  have hstable : (prefixWord ++ tailWord_446008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446008).length < 2 ^ (prefixWord ++ tailWord_446008).sum := by decide
  have hdescent : baseEnd_446008 < baseStart_446008 := by decide
  rcases family_descends (prefixWord ++ tailWord_446008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446039 : List Nat := [1, 1, 3, 2, 2, 4, 3, 4]
def baseStart_446039 : Nat := 118140960795 + 446039 * 2 ^ 59
def prefixEnd_446039 : Nat := 4983230072969 + 3 ^ 40 * 446039 * 2
def baseEnd_446039 : Nat := 67861451155817956758877

theorem tailTrace_446039 : CollatzResearch.WordTrace tailWord_446039 prefixEnd_446039 67861451155817956758877 := by
  unfold tailWord_446039
  simp only [CollatzResearch.WordTrace]
  refine ⟨16268378831084355241517171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10845585887389570161011447 16268378831084355241517171)
  ·
    refine ⟨24402568246626532862275757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16268378831084355241517171 24402568246626532862275757)
    ·
      refine ⟨9150963092484949823353409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24402568246626532862275757 9150963092484949823353409)
      ·
        refine ⟨6863222319363712367515057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9150963092484949823353409 6863222319363712367515057)
        ·
          refine ⟨5147416739522784275636293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6863222319363712367515057 5147416739522784275636293)
          ·
            refine ⟨965140638660522051681805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5147416739522784275636293 965140638660522051681805)
            ·
              refine ⟨361927739497695769380677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 965140638660522051681805 361927739497695769380677)
              ·
                refine ⟨67861451155817956758877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361927739497695769380677 67861451155817956758877)
                ·
                  rfl

theorem cell20_446039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_446039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446039 prefixEnd_446039 := by exact prefixLift 446039
  have htrace : WordTrace (prefixWord ++ tailWord_446039) baseStart_446039 baseEnd_446039 := by
    simpa [prefixWord, tailWord_446039, baseEnd_446039] using wordTrace_append hprefix tailTrace_446039
  have hstable : (prefixWord ++ tailWord_446039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446039).length < 2 ^ (prefixWord ++ tailWord_446039).sum := by decide
  have hdescent : baseEnd_446039 < baseStart_446039 := by decide
  rcases family_descends (prefixWord ++ tailWord_446039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446045 : List Nat := [1, 4, 4, 2, 1, 1, 2, 3, 2]
def baseStart_446045 : Nat := 118140960795 + 446045 * 2 ^ 59
def prefixEnd_446045 : Nat := 4983230072969 + 3 ^ 40 * 446045 * 2
def baseEnd_446045 : Nat := 203587092030944516076607

theorem tailTrace_446045 : CollatzResearch.WordTrace tailWord_446045 prefixEnd_446045 203587092030944516076607 := by
  unfold tailWord_446045
  simp only [CollatzResearch.WordTrace]
  refine ⟨16268597669062618266235589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10845731779375078844157059 16268597669062618266235589)
  ·
    refine ⟨3050362062949240924919173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16268597669062618266235589 3050362062949240924919173)
    ·
      refine ⟨571942886802982673422345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3050362062949240924919173 571942886802982673422345)
      ·
        refine ⟨428957165102237005066759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571942886802982673422345 428957165102237005066759)
        ·
          refine ⟨643435747653355507600139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428957165102237005066759 643435747653355507600139)
          ·
            refine ⟨965153621480033261400209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643435747653355507600139 965153621480033261400209)
            ·
              refine ⟨723865216110024946050157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965153621480033261400209 723865216110024946050157)
              ·
                refine ⟨271449456041259354768809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 723865216110024946050157 271449456041259354768809)
                ·
                  refine ⟨203587092030944516076607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271449456041259354768809 203587092030944516076607)
                  ·
                    rfl

theorem cell20_446045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_446045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446045 prefixEnd_446045 := by exact prefixLift 446045
  have htrace : WordTrace (prefixWord ++ tailWord_446045) baseStart_446045 baseEnd_446045 := by
    simpa [prefixWord, tailWord_446045, baseEnd_446045] using wordTrace_append hprefix tailTrace_446045
  have hstable : (prefixWord ++ tailWord_446045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446045).length < 2 ^ (prefixWord ++ tailWord_446045).sum := by decide
  have hdescent : baseEnd_446045 < baseStart_446045 := by decide
  rcases family_descends (prefixWord ++ tailWord_446045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446070 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_446070 : Nat := 118140960795 + 446070 * 2 ^ 59
def prefixEnd_446070 : Nat := 4983230072969 + 3 ^ 40 * 446070 * 2
def baseEnd_446070 : Nat := 203598502712155540243171

theorem tailTrace_446070 : CollatzResearch.WordTrace tailWord_446070 prefixEnd_446070 203598502712155540243171 := by
  unfold tailWord_446070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016844343373252970993479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10846339662648031690597109 1016844343373252970993479)
  ·
    refine ⟨1525266515059879456490219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1016844343373252970993479 1525266515059879456490219)
    ·
      refine ⟨2287899772589819184735329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525266515059879456490219 2287899772589819184735329)
      ·
        refine ⟨1715924829442364388551497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2287899772589819184735329 1715924829442364388551497)
        ·
          refine ⟨1286943622081773291413623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1715924829442364388551497 1286943622081773291413623)
          ·
            refine ⟨1930415433122659937120435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286943622081773291413623 1930415433122659937120435)
            ·
              refine ⟨2895623149683989905680653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930415433122659937120435 2895623149683989905680653)
              ·
                refine ⟨1085858681131496214630245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2895623149683989905680653 1085858681131496214630245)
                ·
                  refine ⟨203598502712155540243171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085858681131496214630245 203598502712155540243171)
                  ·
                    rfl

theorem cell20_446070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_446070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446070 prefixEnd_446070 := by exact prefixLift 446070
  have htrace : WordTrace (prefixWord ++ tailWord_446070) baseStart_446070 baseEnd_446070 := by
    simpa [prefixWord, tailWord_446070, baseEnd_446070] using wordTrace_append hprefix tailTrace_446070
  have hstable : (prefixWord ++ tailWord_446070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446070).length < 2 ^ (prefixWord ++ tailWord_446070).sum := by decide
  have hdescent : baseEnd_446070 < baseStart_446070 := by decide
  rcases family_descends (prefixWord ++ tailWord_446070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446094 : List Nat := [4, 1, 1, 3, 1, 4, 2, 4]
def baseStart_446094 : Nat := 118140960795 + 446094 * 2 ^ 59
def prefixEnd_446094 : Nat := 4983230072969 + 3 ^ 40 * 446094 * 2
def baseEnd_446094 : Nat := 67869818988706041147691

theorem tailTrace_446094 : CollatzResearch.WordTrace tailWord_446094 prefixEnd_446094 67869818988706041147691 := by
  unfold tailWord_446094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2033798105735637454346167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10846923230590066423179557 2033798105735637454346167)
  ·
    refine ⟨3050697158603456181519251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2033798105735637454346167 3050697158603456181519251)
    ·
      refine ⟨4576045737905184272278877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3050697158603456181519251 4576045737905184272278877)
      ·
        refine ⟨1716017151714444102104579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4576045737905184272278877 1716017151714444102104579)
        ·
          refine ⟨2574025727571666153156869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716017151714444102104579 2574025727571666153156869)
          ·
            refine ⟨482629823919687403716913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2574025727571666153156869 482629823919687403716913)
            ·
              refine ⟨361972367939765552787685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482629823919687403716913 361972367939765552787685)
              ·
                refine ⟨67869818988706041147691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361972367939765552787685 67869818988706041147691)
                ·
                  rfl

theorem cell20_446094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_446094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446094 prefixEnd_446094 := by exact prefixLift 446094
  have htrace : WordTrace (prefixWord ++ tailWord_446094) baseStart_446094 baseEnd_446094 := by
    simpa [prefixWord, tailWord_446094, baseEnd_446094] using wordTrace_append hprefix tailTrace_446094
  have hstable : (prefixWord ++ tailWord_446094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446094).length < 2 ^ (prefixWord ++ tailWord_446094).sum := by decide
  have hdescent : baseEnd_446094 < baseStart_446094 := by decide
  rcases family_descends (prefixWord ++ tailWord_446094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446177 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 3]
def baseStart_446177 : Nat := 118140960795 + 446177 * 2 ^ 59
def prefixEnd_446177 : Nat := 4983230072969 + 3 ^ 40 * 446177 * 2
def baseEnd_446177 : Nat := 203647340427738723676067

theorem tailTrace_446177 : CollatzResearch.WordTrace tailWord_446177 prefixEnd_446177 203647340427738723676067 := by
  unfold tailWord_446177
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273412104584404810040785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10848941403056269873360523 16273412104584404810040785)
  ·
    refine ⟨12205059078438303607530589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16273412104584404810040785 12205059078438303607530589)
    ·
      refine ⟨4576897154414363852823971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12205059078438303607530589 4576897154414363852823971)
      ·
        refine ⟨6865345731621545779235957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576897154414363852823971 6865345731621545779235957)
        ·
          refine ⟨643626162339519916803371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6865345731621545779235957 643626162339519916803371)
          ·
            refine ⟨965439243509279875205057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643626162339519916803371 965439243509279875205057)
            ·
              refine ⟨724079432631959906403793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965439243509279875205057 724079432631959906403793)
              ·
                refine ⟨543059574473969929802845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724079432631959906403793 543059574473969929802845)
                ·
                  refine ⟨203647340427738723676067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543059574473969929802845 203647340427738723676067)
                  ·
                    rfl

theorem cell20_446177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_446177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446177 prefixEnd_446177 := by exact prefixLift 446177
  have htrace : WordTrace (prefixWord ++ tailWord_446177) baseStart_446177 baseEnd_446177 := by
    simpa [prefixWord, tailWord_446177, baseEnd_446177] using wordTrace_append hprefix tailTrace_446177
  have hstable : (prefixWord ++ tailWord_446177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446177).length < 2 ^ (prefixWord ++ tailWord_446177).sum := by decide
  have hdescent : baseEnd_446177 < baseStart_446177 := by decide
  rcases family_descends (prefixWord ++ tailWord_446177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446222 : List Nat := [4, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_446222 : Nat := 118140960795 + 446222 * 2 ^ 59
def prefixEnd_446222 : Nat := 4983230072969 + 3 ^ 40 * 446222 * 2
def baseEnd_446222 : Nat := 203667879653918567175883

theorem tailTrace_446222 : CollatzResearch.WordTrace tailWord_446222 prefixEnd_446222 203667879653918567175883 := by
  unfold tailWord_446222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034381673677672186928615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10850035592947584996952613 2034381673677672186928615)
  ·
    refine ⟨3051572510516508280392923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2034381673677672186928615 3051572510516508280392923)
    ·
      refine ⟨4577358765774762420589385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051572510516508280392923 4577358765774762420589385)
      ·
        refine ⟨3433019074331071815442039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577358765774762420589385 3433019074331071815442039)
        ·
          refine ⟨5149528611496607723163059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433019074331071815442039 5149528611496607723163059)
          ·
            refine ⟨7724292917244911584744589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149528611496607723163059 7724292917244911584744589)
            ·
              refine ⟨2896609843966841844279221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7724292917244911584744589 2896609843966841844279221)
              ·
                refine ⟨271557172871891422901177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2896609843966841844279221 271557172871891422901177)
                ·
                  refine ⟨203667879653918567175883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271557172871891422901177 203667879653918567175883)
                  ·
                    rfl

theorem cell20_446222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_446222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446222 prefixEnd_446222 := by exact prefixLift 446222
  have htrace : WordTrace (prefixWord ++ tailWord_446222) baseStart_446222 baseEnd_446222 := by
    simpa [prefixWord, tailWord_446222, baseEnd_446222] using wordTrace_append hprefix tailTrace_446222
  have hstable : (prefixWord ++ tailWord_446222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446222).length < 2 ^ (prefixWord ++ tailWord_446222).sum := by decide
  have hdescent : baseEnd_446222 < baseStart_446222 := by decide
  rcases family_descends (prefixWord ++ tailWord_446222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446228 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 3]
def baseStart_446228 : Nat := 118140960795 + 446228 * 2 ^ 59
def prefixEnd_446228 : Nat := 4983230072969 + 3 ^ 40 * 446228 * 2
def baseEnd_446228 : Nat := 203670618217409212975859

theorem tailTrace_446228 : CollatzResearch.WordTrace tailWord_446228 prefixEnd_446228 203670618217409212975859 := by
  unfold tailWord_446228
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137636113699820260073669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10850181484933093680098225 8137636113699820260073669)
  ·
    refine ⟨1525806771318716298763813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8137636113699820260073669 1525806771318716298763813)
    ·
      refine ⟨286088769622259306018215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1525806771318716298763813 286088769622259306018215)
      ·
        refine ⟨429133154433388959027323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286088769622259306018215 429133154433388959027323)
        ·
          refine ⟨643699731650083438540985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429133154433388959027323 643699731650083438540985)
          ·
            refine ⟨482774798737562578905739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643699731650083438540985 482774798737562578905739)
            ·
              refine ⟨724162198106343868358609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482774798737562578905739 724162198106343868358609)
              ·
                refine ⟨543121648579757901268957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724162198106343868358609 543121648579757901268957)
                ·
                  refine ⟨203670618217409212975859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543121648579757901268957 203670618217409212975859)
                  ·
                    rfl

theorem cell20_446228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_446228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446228 prefixEnd_446228 := by exact prefixLift 446228
  have htrace : WordTrace (prefixWord ++ tailWord_446228) baseStart_446228 baseEnd_446228 := by
    simpa [prefixWord, tailWord_446228, baseEnd_446228] using wordTrace_append hprefix tailTrace_446228
  have hstable : (prefixWord ++ tailWord_446228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446228).length < 2 ^ (prefixWord ++ tailWord_446228).sum := by decide
  have hdescent : baseEnd_446228 < baseStart_446228 := by decide
  rcases family_descends (prefixWord ++ tailWord_446228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446260 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_446260 : Nat := 118140960795 + 446260 * 2 ^ 59
def prefixEnd_446260 : Nat := 4983230072969 + 3 ^ 40 * 446260 * 2
def baseEnd_446260 : Nat := 203685223889359323909061

theorem tailTrace_446260 : CollatzResearch.WordTrace tailWord_446260 prefixEnd_446260 203685223889359323909061 := by
  unfold tailWord_446260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138219681641854992656117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10850959575522473323541489 8138219681641854992656117)
  ·
    refine ⟨762958095153923905561511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8138219681641854992656117 762958095153923905561511)
    ·
      refine ⟨1144437142730885858342267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762958095153923905561511 1144437142730885858342267)
      ·
        refine ⟨1716655714096328787513401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144437142730885858342267 1716655714096328787513401)
        ·
          refine ⟨1287491785572246590635051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716655714096328787513401 1287491785572246590635051)
          ·
            refine ⟨1931237678358369885952577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287491785572246590635051 1931237678358369885952577)
            ·
              refine ⟨1448428258768777414464433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931237678358369885952577 1448428258768777414464433)
              ·
                refine ⟨1086321194076583060848325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448428258768777414464433 1086321194076583060848325)
                ·
                  refine ⟨203685223889359323909061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086321194076583060848325 203685223889359323909061)
                  ·
                    rfl

theorem cell20_446260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_446260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446260 prefixEnd_446260 := by exact prefixLift 446260
  have htrace : WordTrace (prefixWord ++ tailWord_446260) baseStart_446260 baseEnd_446260 := by
    simpa [prefixWord, tailWord_446260, baseEnd_446260] using wordTrace_append hprefix tailTrace_446260
  have hstable : (prefixWord ++ tailWord_446260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446260).length < 2 ^ (prefixWord ++ tailWord_446260).sum := by decide
  have hdescent : baseEnd_446260 < baseStart_446260 := by decide
  rcases family_descends (prefixWord ++ tailWord_446260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446308 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_446308 : Nat := 118140960795 + 446308 * 2 ^ 59
def prefixEnd_446308 : Nat := 4983230072969 + 3 ^ 40 * 446308 * 2
def baseEnd_446308 : Nat := 203707132397284490308865

theorem tailTrace_446308 : CollatzResearch.WordTrace tailWord_446308 prefixEnd_446308 203707132397284490308865 := by
  unfold tailWord_446308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139095033554907091529789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10852126711406542788706385 8139095033554907091529789)
  ·
    refine ⟨3052160637583090159323671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8139095033554907091529789 3052160637583090159323671)
    ·
      refine ⟨4578240956374635238985507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3052160637583090159323671 4578240956374635238985507)
      ·
        refine ⟨6867361434561952858478261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578240956374635238985507 6867361434561952858478261)
        ·
          refine ⟨643815134490183080482337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6867361434561952858478261 643815134490183080482337)
          ·
            refine ⟨482861350867637310361753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643815134490183080482337 482861350867637310361753)
            ·
              refine ⟨362146013150727982771315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482861350867637310361753 362146013150727982771315)
              ·
                refine ⟨543219019726091974156973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362146013150727982771315 543219019726091974156973)
                ·
                  refine ⟨203707132397284490308865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543219019726091974156973 203707132397284490308865)
                  ·
                    rfl

theorem cell20_446308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_446308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446308 prefixEnd_446308 := by exact prefixLift 446308
  have htrace : WordTrace (prefixWord ++ tailWord_446308) baseStart_446308 baseEnd_446308 := by
    simpa [prefixWord, tailWord_446308, baseEnd_446308] using wordTrace_append hprefix tailTrace_446308
  have hstable : (prefixWord ++ tailWord_446308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446308).length < 2 ^ (prefixWord ++ tailWord_446308).sum := by decide
  have hdescent : baseEnd_446308 < baseStart_446308 := by decide
  rcases family_descends (prefixWord ++ tailWord_446308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446312 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_446312 : Nat := 118140960795 + 446312 * 2 ^ 59
def prefixEnd_446312 : Nat := 4983230072969 + 3 ^ 40 * 446312 * 2
def baseEnd_446312 : Nat := 203708958106278254175515

theorem tailTrace_446312 : CollatzResearch.WordTrace tailWord_446312 prefixEnd_446312 203708958106278254175515 := by
  unfold tailWord_446312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139167979547661433102595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10852223972730215244136793 8139167979547661433102595)
  ·
    refine ⟨12208751969321492149653893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8139167979547661433102595 12208751969321492149653893)
    ·
      refine ⟨2289140994247779778060105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12208751969321492149653893 2289140994247779778060105)
      ·
        refine ⟨1716855745685834833545079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289140994247779778060105 1716855745685834833545079)
        ·
          refine ⟨2575283618528752250317619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716855745685834833545079 2575283618528752250317619)
          ·
            refine ⟨3862925427793128375476429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575283618528752250317619 3862925427793128375476429)
            ·
              refine ⟨1448597035422423140803661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3862925427793128375476429 1448597035422423140803661)
              ·
                refine ⟨543223888283408677801373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1448597035422423140803661 543223888283408677801373)
                ·
                  refine ⟨203708958106278254175515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543223888283408677801373 203708958106278254175515)
                  ·
                    rfl

theorem cell20_446312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_446312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446312 prefixEnd_446312 := by exact prefixLift 446312
  have htrace : WordTrace (prefixWord ++ tailWord_446312) baseStart_446312 baseEnd_446312 := by
    simpa [prefixWord, tailWord_446312, baseEnd_446312] using wordTrace_append hprefix tailTrace_446312
  have hstable : (prefixWord ++ tailWord_446312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446312).length < 2 ^ (prefixWord ++ tailWord_446312).sum := by decide
  have hdescent : baseEnd_446312 < baseStart_446312 := by decide
  rcases family_descends (prefixWord ++ tailWord_446312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446360 : List Nat := [2, 1, 2, 6, 1, 2, 1, 5]
def baseStart_446360 : Nat := 118140960795 + 446360 * 2 ^ 59
def prefixEnd_446360 : Nat := 4983230072969 + 3 ^ 40 * 446360 * 2
def baseEnd_446360 : Nat := 67910288871401140191773

theorem tailTrace_446360 : CollatzResearch.WordTrace tailWord_446360 prefixEnd_446360 67910288871401140191773 := by
  unfold tailWord_446360
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140043331460713531976267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10853391108614284709301689 8140043331460713531976267)
  ·
    refine ⟨12210064997191070297964401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140043331460713531976267 12210064997191070297964401)
    ·
      refine ⟨9157548747893302723473301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12210064997191070297964401 9157548747893302723473301)
      ·
        refine ⟨429260097557498565162811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9157548747893302723473301 429260097557498565162811)
        ·
          refine ⟨643890146336247847744217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429260097557498565162811 643890146336247847744217)
          ·
            refine ⟨482917609752185885808163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643890146336247847744217 482917609752185885808163)
            ·
              refine ⟨724376414628278828712245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482917609752185885808163 724376414628278828712245)
              ·
                refine ⟨67910288871401140191773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 724376414628278828712245 67910288871401140191773)
                ·
                  rfl

theorem cell20_446360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_446360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446360 prefixEnd_446360 := by exact prefixLift 446360
  have htrace : WordTrace (prefixWord ++ tailWord_446360) baseStart_446360 baseEnd_446360 := by
    simpa [prefixWord, tailWord_446360, baseEnd_446360] using wordTrace_append hprefix tailTrace_446360
  have hstable : (prefixWord ++ tailWord_446360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446360).length < 2 ^ (prefixWord ++ tailWord_446360).sum := by decide
  have hdescent : baseEnd_446360 < baseStart_446360 := by decide
  rcases family_descends (prefixWord ++ tailWord_446360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446395 : List Nat := [1, 1, 1, 1, 1, 2, 2, 9, 2]
def baseStart_446395 : Nat := 118140960795 + 446395 * 2 ^ 59
def prefixEnd_446395 : Nat := 4983230072969 + 3 ^ 40 * 446395 * 2
def baseEnd_446395 : Nat := 203746841567898854408509

theorem tailTrace_446395 : CollatzResearch.WordTrace tailWord_446395 prefixEnd_446395 203746841567898854408509 := by
  unfold tailWord_446395
  simp only [CollatzResearch.WordTrace]
  refine ⟨16281363217794628041476639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10854242145196418694317759 16281363217794628041476639)
  ·
    refine ⟨24422044826691942062214959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16281363217794628041476639 24422044826691942062214959)
    ·
      refine ⟨36633067240037913093322439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24422044826691942062214959 36633067240037913093322439)
      ·
        refine ⟨54949600860056869639983659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36633067240037913093322439 54949600860056869639983659)
        ·
          refine ⟨82424401290085304459975489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54949600860056869639983659 82424401290085304459975489)
          ·
            refine ⟨61818300967563978344981617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82424401290085304459975489 61818300967563978344981617)
            ·
              refine ⟨46363725725672983758736213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61818300967563978344981617 46363725725672983758736213)
              ·
                refine ⟨271662455423865139211345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 46363725725672983758736213 271662455423865139211345)
                ·
                  refine ⟨203746841567898854408509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271662455423865139211345 203746841567898854408509)
                  ·
                    rfl

theorem cell20_446395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 2].length) (baseStart_446395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446395 prefixEnd_446395 := by exact prefixLift 446395
  have htrace : WordTrace (prefixWord ++ tailWord_446395) baseStart_446395 baseEnd_446395 := by
    simpa [prefixWord, tailWord_446395, baseEnd_446395] using wordTrace_append hprefix tailTrace_446395
  have hstable : (prefixWord ++ tailWord_446395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446395).length < 2 ^ (prefixWord ++ tailWord_446395).sum := by decide
  have hdescent : baseEnd_446395 < baseStart_446395 := by decide
  rcases family_descends (prefixWord ++ tailWord_446395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446412 : List Nat := [2, 2, 1, 4, 1, 2, 2, 4, 2]
def baseStart_446412 : Nat := 118140960795 + 446412 * 2 ^ 59
def prefixEnd_446412 : Nat := 4983230072969 + 3 ^ 40 * 446412 * 2
def baseEnd_446412 : Nat := 203754600831122350841773

theorem tailTrace_446412 : CollatzResearch.WordTrace tailWord_446412 prefixEnd_446412 203754600831122350841773 := by
  unfold tailWord_446412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140991629366519972422745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10854655505822026629896993 8140991629366519972422745)
  ·
    refine ⟨6105743722024889979317059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8140991629366519972422745 6105743722024889979317059)
    ·
      refine ⟨9158615583037334968975589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6105743722024889979317059 9158615583037334968975589)
      ·
        refine ⟨1717240421819500306682923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9158615583037334968975589 1717240421819500306682923)
        ·
          refine ⟨2575860632729250460024385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717240421819500306682923 2575860632729250460024385)
          ·
            refine ⟨1931895474546937845018289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2575860632729250460024385 1931895474546937845018289)
            ·
              refine ⟨1448921605910203383763717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931895474546937845018289 1448921605910203383763717)
              ·
                refine ⟨271672801108163134455697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1448921605910203383763717 271672801108163134455697)
                ·
                  refine ⟨203754600831122350841773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271672801108163134455697 203754600831122350841773)
                  ·
                    rfl

theorem cell20_446412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_446412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446412 prefixEnd_446412 := by exact prefixLift 446412
  have htrace : WordTrace (prefixWord ++ tailWord_446412) baseStart_446412 baseEnd_446412 := by
    simpa [prefixWord, tailWord_446412, baseEnd_446412] using wordTrace_append hprefix tailTrace_446412
  have hstable : (prefixWord ++ tailWord_446412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446412).length < 2 ^ (prefixWord ++ tailWord_446412).sum := by decide
  have hdescent : baseEnd_446412 < baseStart_446412 := by decide
  rcases family_descends (prefixWord ++ tailWord_446412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446416 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_446416 : Nat := 118140960795 + 446416 * 2 ^ 59
def prefixEnd_446416 : Nat := 4983230072969 + 3 ^ 40 * 446416 * 2
def baseEnd_446416 : Nat := 203756426540116114708423

theorem tailTrace_446416 : CollatzResearch.WordTrace tailWord_446416 prefixEnd_446416 203756426540116114708423 := by
  unfold tailWord_446416
  simp only [CollatzResearch.WordTrace]
  refine ⟨8141064575359274313995551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10854752767145699085327401 8141064575359274313995551)
  ·
    refine ⟨12211596863038911470993327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8141064575359274313995551 12211596863038911470993327)
    ·
      refine ⟨18317395294558367206489991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211596863038911470993327 18317395294558367206489991)
      ·
        refine ⟨27476092941837550809734987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18317395294558367206489991 27476092941837550809734987)
        ·
          refine ⟨41214139412756326214602481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27476092941837550809734987 41214139412756326214602481)
          ·
            refine ⟨30910604559567244660951861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41214139412756326214602481 30910604559567244660951861)
            ·
              refine ⟨2897869177459429186964237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30910604559567244660951861 2897869177459429186964237)
              ·
                refine ⟨1086700941547285945111589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897869177459429186964237 1086700941547285945111589)
                ·
                  refine ⟨203756426540116114708423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086700941547285945111589 203756426540116114708423)
                  ·
                    rfl

theorem cell20_446416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_446416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446416 prefixEnd_446416 := by exact prefixLift 446416
  have htrace : WordTrace (prefixWord ++ tailWord_446416) baseStart_446416 baseEnd_446416 := by
    simpa [prefixWord, tailWord_446416, baseEnd_446416] using wordTrace_append hprefix tailTrace_446416
  have hstable : (prefixWord ++ tailWord_446416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446416).length < 2 ^ (prefixWord ++ tailWord_446416).sum := by decide
  have hdescent : baseEnd_446416 < baseStart_446416 := by decide
  rcases family_descends (prefixWord ++ tailWord_446416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446423 : List Nat := [1, 1, 3, 2, 1, 1, 4, 7]
def baseStart_446423 : Nat := 118140960795 + 446423 * 2 ^ 59
def prefixEnd_446423 : Nat := 4983230072969 + 3 ^ 40 * 446423 * 2
def baseEnd_446423 : Nat := 67919873843618400491687

theorem tailTrace_446423 : CollatzResearch.WordTrace tailWord_446423 prefixEnd_446423 67919873843618400491687 := by
  unfold tailWord_446423
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282384461693188823495923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10854922974462125882330615 16282384461693188823495923)
  ·
    refine ⟨24423576692539783235243885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16282384461693188823495923 24423576692539783235243885)
    ·
      refine ⟨9158841259702418713216457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24423576692539783235243885 9158841259702418713216457)
      ·
        refine ⟨6869130944776814034912343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9158841259702418713216457 6869130944776814034912343)
        ·
          refine ⟨10303696417165221052368515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6869130944776814034912343 10303696417165221052368515)
          ·
            refine ⟨15455544625747831578552773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10303696417165221052368515 15455544625747831578552773)
            ·
              refine ⟨2897914617327718420978645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15455544625747831578552773 2897914617327718420978645)
              ·
                refine ⟨67919873843618400491687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2897914617327718420978645 67919873843618400491687)
                ·
                  rfl

theorem cell20_446423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_446423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446423 prefixEnd_446423 := by exact prefixLift 446423
  have htrace : WordTrace (prefixWord ++ tailWord_446423) baseStart_446423 baseEnd_446423 := by
    simpa [prefixWord, tailWord_446423, baseEnd_446423] using wordTrace_append hprefix tailTrace_446423
  have hstable : (prefixWord ++ tailWord_446423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446423).length < 2 ^ (prefixWord ++ tailWord_446423).sum := by decide
  have hdescent : baseEnd_446423 < baseStart_446423 := by decide
  rcases family_descends (prefixWord ++ tailWord_446423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446461 : List Nat := [1, 4, 1, 1, 1, 2, 10]
def baseStart_446461 : Nat := 118140960795 + 446461 * 2 ^ 59
def prefixEnd_446461 : Nat := 4983230072969 + 3 ^ 40 * 446461 * 2
def baseEnd_446461 : Nat := 22641885085143995356471

theorem tailTrace_446461 : CollatzResearch.WordTrace tailWord_446461 prefixEnd_446461 22641885085143995356471 := by
  unfold tailWord_446461
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283770435555521313379237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10855846957037014208919491 16283770435555521313379237)
  ·
    refine ⟨3053206956666660246258607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16283770435555521313379237 3053206956666660246258607)
    ·
      refine ⟨4579810434999990369387911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3053206956666660246258607 4579810434999990369387911)
      ·
        refine ⟨6869715652499985554081867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579810434999990369387911 6869715652499985554081867)
        ·
          refine ⟨10304573478749978331122801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6869715652499985554081867 10304573478749978331122801)
          ·
            refine ⟨7728430109062483748342101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10304573478749978331122801 7728430109062483748342101)
            ·
              refine ⟨22641885085143995356471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7728430109062483748342101 22641885085143995356471)
              ·
                rfl

theorem cell20_446461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_446461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446461 prefixEnd_446461 := by exact prefixLift 446461
  have htrace : WordTrace (prefixWord ++ tailWord_446461) baseStart_446461 baseEnd_446461 := by
    simpa [prefixWord, tailWord_446461, baseEnd_446461] using wordTrace_append hprefix tailTrace_446461
  have hstable : (prefixWord ++ tailWord_446461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446461).length < 2 ^ (prefixWord ++ tailWord_446461).sum := by decide
  have hdescent : baseEnd_446461 < baseStart_446461 := by decide
  rcases family_descends (prefixWord ++ tailWord_446461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446470 : List Nat := [6, 2, 1, 2, 1, 1, 2, 5]
def baseStart_446470 : Nat := 118140960795 + 446470 * 2 ^ 59
def prefixEnd_446470 : Nat := 4983230072969 + 3 ^ 40 * 446470 * 2
def baseEnd_446470 : Nat := 67927024537177308969401

theorem tailTrace_446470 : CollatzResearch.WordTrace tailWord_446470 prefixEnd_446470 67927024537177308969401 := by
  unfold tailWord_446470
  simp only [CollatzResearch.WordTrace]
  refine ⟨508878084141341120326777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10856065795015277233637909 508878084141341120326777)
  ·
    refine ⟨381658563106005840245083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 508878084141341120326777 381658563106005840245083)
    ·
      refine ⟨572487844659008760367625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381658563106005840245083 572487844659008760367625)
      ·
        refine ⟨429365883494256570275719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572487844659008760367625 429365883494256570275719)
        ·
          refine ⟨644048825241384855413579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429365883494256570275719 644048825241384855413579)
          ·
            refine ⟨966073237862077283120369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644048825241384855413579 966073237862077283120369)
            ·
              refine ⟨724554928396557962340277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966073237862077283120369 724554928396557962340277)
              ·
                refine ⟨67927024537177308969401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 724554928396557962340277 67927024537177308969401)
                ·
                  rfl

theorem cell20_446470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_446470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446470 prefixEnd_446470 := by exact prefixLift 446470
  have htrace : WordTrace (prefixWord ++ tailWord_446470) baseStart_446470 baseEnd_446470 := by
    simpa [prefixWord, tailWord_446470, baseEnd_446470] using wordTrace_append hprefix tailTrace_446470
  have hstable : (prefixWord ++ tailWord_446470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446470).length < 2 ^ (prefixWord ++ tailWord_446470).sum := by decide
  have hdescent : baseEnd_446470 < baseStart_446470 := by decide
  rcases family_descends (prefixWord ++ tailWord_446470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446471 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_446471 : Nat := 118140960795 + 446471 * 2 ^ 59
def prefixEnd_446471 : Nat := 4983230072969 + 3 ^ 40 * 446471 * 2
def baseEnd_446471 : Nat := 203781530038780367874865

theorem tailTrace_446471 : CollatzResearch.WordTrace tailWord_446471 prefixEnd_446471 203781530038780367874865 := by
  unfold tailWord_446471
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284135165519293021243267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10856090110346195347495511 16284135165519293021243267)
  ·
    refine ⟨24426202748278939531864901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16284135165519293021243267 24426202748278939531864901)
    ·
      refine ⟨4579913015302301162224669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24426202748278939531864901 4579913015302301162224669)
      ·
        refine ⟨1717467380738362935834251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4579913015302301162224669 1717467380738362935834251)
        ·
          refine ⟨2576201071107544403751377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717467380738362935834251 2576201071107544403751377)
          ·
            refine ⟨1932150803330658302813533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576201071107544403751377 1932150803330658302813533)
            ·
              refine ⟨724556551248996863555075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1932150803330658302813533 724556551248996863555075)
              ·
                refine ⟨1086834826873495295332613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724556551248996863555075 1086834826873495295332613)
                ·
                  refine ⟨203781530038780367874865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086834826873495295332613 203781530038780367874865)
                  ·
                    rfl

theorem cell20_446471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_446471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446471 prefixEnd_446471 := by exact prefixLift 446471
  have htrace : WordTrace (prefixWord ++ tailWord_446471) baseStart_446471 baseEnd_446471 := by
    simpa [prefixWord, tailWord_446471, baseEnd_446471] using wordTrace_append hprefix tailTrace_446471
  have hstable : (prefixWord ++ tailWord_446471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446471).length < 2 ^ (prefixWord ++ tailWord_446471).sum := by decide
  have hdescent : baseEnd_446471 < baseStart_446471 := by decide
  rcases family_descends (prefixWord ++ tailWord_446471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446477 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 3]
def baseStart_446477 : Nat := 118140960795 + 446477 * 2 ^ 59
def prefixEnd_446477 : Nat := 4983230072969 + 3 ^ 40 * 446477 * 2
def baseEnd_446477 : Nat := 203784268602271013674841

theorem tailTrace_446477 : CollatzResearch.WordTrace tailWord_446477 prefixEnd_446477 203784268602271013674841 := by
  unfold tailWord_446477
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284354003497556045961685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10856236002331704030641123 16284354003497556045961685)
  ·
    refine ⟨381664546956973969827227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16284354003497556045961685 381664546956973969827227)
    ·
      refine ⟨572496820435460954740841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381664546956973969827227 572496820435460954740841)
      ·
        refine ⟨429372615326595716055631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572496820435460954740841 429372615326595716055631)
        ·
          refine ⟨644058922989893574083447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429372615326595716055631 644058922989893574083447)
          ·
            refine ⟨966088384484840361125171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644058922989893574083447 966088384484840361125171)
            ·
              refine ⟨1449132576727260541687757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966088384484840361125171 1449132576727260541687757)
              ·
                refine ⟨543424716272722703132909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1449132576727260541687757 543424716272722703132909)
                ·
                  refine ⟨203784268602271013674841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543424716272722703132909 203784268602271013674841)
                  ·
                    rfl

theorem cell20_446477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_446477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446477 prefixEnd_446477 := by exact prefixLift 446477
  have htrace : WordTrace (prefixWord ++ tailWord_446477) baseStart_446477 baseEnd_446477 := by
    simpa [prefixWord, tailWord_446477, baseEnd_446477] using wordTrace_append hprefix tailTrace_446477
  have hstable : (prefixWord ++ tailWord_446477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446477).length < 2 ^ (prefixWord ++ tailWord_446477).sum := by decide
  have hdescent : baseEnd_446477 < baseStart_446477 := by decide
  rcases family_descends (prefixWord ++ tailWord_446477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446478 : List Nat := [4, 1, 1, 2, 2, 1, 4, 5]
def baseStart_446478 : Nat := 118140960795 + 446478 * 2 ^ 59
def prefixEnd_446478 : Nat := 4983230072969 + 3 ^ 40 * 446478 * 2
def baseEnd_446478 : Nat := 67928241676506484880501

theorem tailTrace_446478 : CollatzResearch.WordTrace tailWord_446478 prefixEnd_446478 67928241676506484880501 := by
  unfold tailWord_446478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035548809561741652093511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10856260317662622144498725 2035548809561741652093511)
  ·
    refine ⟨3053323214342612478140267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2035548809561741652093511 3053323214342612478140267)
    ·
      refine ⟨4579984821513918717210401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3053323214342612478140267 4579984821513918717210401)
      ·
        refine ⟨3434988616135439037907801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4579984821513918717210401 3434988616135439037907801)
        ·
          refine ⟨2576241462101579278430851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434988616135439037907801 2576241462101579278430851)
          ·
            refine ⟨3864362193152368917646277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576241462101579278430851 3864362193152368917646277)
            ·
              refine ⟨724567911216069172058677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3864362193152368917646277 724567911216069172058677)
              ·
                refine ⟨67928241676506484880501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 724567911216069172058677 67928241676506484880501)
                ·
                  rfl

theorem cell20_446478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_446478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446478 prefixEnd_446478 := by exact prefixLift 446478
  have htrace : WordTrace (prefixWord ++ tailWord_446478) baseStart_446478 baseEnd_446478 := by
    simpa [prefixWord, tailWord_446478, baseEnd_446478] using wordTrace_append hprefix tailTrace_446478
  have hstable : (prefixWord ++ tailWord_446478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446478).length < 2 ^ (prefixWord ++ tailWord_446478).sum := by decide
  have hdescent : baseEnd_446478 < baseStart_446478 := by decide
  rcases family_descends (prefixWord ++ tailWord_446478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446499 : List Nat := [1, 1, 1, 4, 3, 1, 1, 8]
def baseStart_446499 : Nat := 118140960795 + 446499 * 2 ^ 59
def prefixEnd_446499 : Nat := 4983230072969 + 3 ^ 40 * 446499 * 2
def baseEnd_446499 : Nat := 67931436667245571647139

theorem tailTrace_446499 : CollatzResearch.WordTrace tailWord_446499 prefixEnd_446499 67931436667245571647139 := by
  unfold tailWord_446499
  simp only [CollatzResearch.WordTrace]
  refine ⟨16285156409417853803262551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10856770939611902535508367 16285156409417853803262551)
  ·
    refine ⟨24427734614126780704893827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16285156409417853803262551 24427734614126780704893827)
    ·
      refine ⟨36641601921190171057340741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24427734614126780704893827 36641601921190171057340741)
      ·
        refine ⟨6870300360223157073251389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36641601921190171057340741 6870300360223157073251389)
        ·
          refine ⟨2576362635083683902469271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6870300360223157073251389 2576362635083683902469271)
          ·
            refine ⟨3864543952625525853703907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576362635083683902469271 3864543952625525853703907)
            ·
              refine ⟨5796815928938288780555861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864543952625525853703907 5796815928938288780555861)
              ·
                refine ⟨67931436667245571647139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5796815928938288780555861 67931436667245571647139)
                ·
                  rfl

theorem cell20_446499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_446499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446499 prefixEnd_446499 := by exact prefixLift 446499
  have htrace : WordTrace (prefixWord ++ tailWord_446499) baseStart_446499 baseEnd_446499 := by
    simpa [prefixWord, tailWord_446499, baseEnd_446499] using wordTrace_append hprefix tailTrace_446499
  have hstable : (prefixWord ++ tailWord_446499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446499).length < 2 ^ (prefixWord ++ tailWord_446499).sum := by decide
  have hdescent : baseEnd_446499 < baseStart_446499 := by decide
  rcases family_descends (prefixWord ++ tailWord_446499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446516 : List Nat := [2, 5, 1, 2, 10]
def baseStart_446516 : Nat := 118140960795 + 446516 * 2 ^ 59
def prefixEnd_446516 : Nat := 4983230072969 + 3 ^ 40 * 446516 * 2
def baseEnd_446516 : Nat := 2516074929197039646601

theorem tailTrace_446516 : CollatzResearch.WordTrace tailWord_446516 prefixEnd_446516 2516074929197039646601 := by
  unfold tailWord_446516
  simp only [CollatzResearch.WordTrace]
  refine ⟨8142888225178132853315701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10857184300237510471087601 8142888225178132853315701)
  ·
    refine ⟨763395771110449954998347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8142888225178132853315701 763395771110449954998347)
    ·
      refine ⟨1145093656665674932497521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763395771110449954998347 1145093656665674932497521)
      ·
        refine ⟨858820242499256199373141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1145093656665674932497521 858820242499256199373141)
        ·
          refine ⟨2516074929197039646601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 858820242499256199373141 2516074929197039646601)
          ·
            rfl

theorem cell20_446516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 10].length) (baseStart_446516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446516 prefixEnd_446516 := by exact prefixLift 446516
  have htrace : WordTrace (prefixWord ++ tailWord_446516) baseStart_446516 baseEnd_446516 := by
    simpa [prefixWord, tailWord_446516, baseEnd_446516] using wordTrace_append hprefix tailTrace_446516
  have hstable : (prefixWord ++ tailWord_446516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446516).length < 2 ^ (prefixWord ++ tailWord_446516).sum := by decide
  have hdescent : baseEnd_446516 < baseStart_446516 := by decide
  rcases family_descends (prefixWord ++ tailWord_446516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446544 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_446544 : Nat := 118140960795 + 446544 * 2 ^ 59
def prefixEnd_446544 : Nat := 4983230072969 + 3 ^ 40 * 446544 * 2
def baseEnd_446544 : Nat := 203814849227916558441233

theorem tailTrace_446544 : CollatzResearch.WordTrace tailWord_446544 prefixEnd_446544 203814849227916558441233 := by
  unfold tailWord_446544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8143398847127413244325343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10857865129503217659100457 8143398847127413244325343)
  ·
    refine ⟨12215098270691119866488015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8143398847127413244325343 12215098270691119866488015)
    ·
      refine ⟨18322647406036679799732023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12215098270691119866488015 18322647406036679799732023)
      ·
        refine ⟨27483971109055019699598035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18322647406036679799732023 27483971109055019699598035)
        ·
          refine ⟨41225956663582529549397053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27483971109055019699598035 41225956663582529549397053)
          ·
            refine ⟨15459733748843448581023895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41225956663582529549397053 15459733748843448581023895)
            ·
              refine ⟨23189600623265172871535843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15459733748843448581023895 23189600623265172871535843)
              ·
                refine ⟨34784400934897759307303765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23189600623265172871535843 34784400934897759307303765)
                ·
                  refine ⟨203814849227916558441233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34784400934897759307303765 203814849227916558441233)
                  ·
                    rfl

theorem cell20_446544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_446544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446544 prefixEnd_446544 := by exact prefixLift 446544
  have htrace : WordTrace (prefixWord ++ tailWord_446544) baseStart_446544 baseEnd_446544 := by
    simpa [prefixWord, tailWord_446544, baseEnd_446544] using wordTrace_append hprefix tailTrace_446544
  have hstable : (prefixWord ++ tailWord_446544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446544).length < 2 ^ (prefixWord ++ tailWord_446544).sum := by decide
  have hdescent : baseEnd_446544 < baseStart_446544 := by decide
  rcases family_descends (prefixWord ++ tailWord_446544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446554 : List Nat := [3, 1, 1, 2, 1, 1, 7, 4]
def baseStart_446554 : Nat := 118140960795 + 446554 * 2 ^ 59
def prefixEnd_446554 : Nat := 4983230072969 + 3 ^ 40 * 446554 * 2
def baseEnd_446554 : Nat := 67939804500133656035953

theorem tailTrace_446554 : CollatzResearch.WordTrace tailWord_446554 prefixEnd_446554 67939804500133656035953 := by
  unfold tailWord_446554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071790606054649549128679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10858108282812398797676477 4071790606054649549128679)
  ·
    refine ⟨6107685909081974323693019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4071790606054649549128679 6107685909081974323693019)
    ·
      refine ⟨9161528863622961485539529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6107685909081974323693019 9161528863622961485539529)
      ·
        refine ⟨6871146647717221114154647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9161528863622961485539529 6871146647717221114154647)
        ·
          refine ⟨10306719971575831671231971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871146647717221114154647 10306719971575831671231971)
          ·
            refine ⟨15460079957363747506847957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10306719971575831671231971 15460079957363747506847957)
            ·
              refine ⟨362345624000712832191749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15460079957363747506847957 362345624000712832191749)
              ·
                refine ⟨67939804500133656035953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362345624000712832191749 67939804500133656035953)
                ·
                  rfl

theorem cell20_446554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_446554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446554 prefixEnd_446554 := by exact prefixLift 446554
  have htrace : WordTrace (prefixWord ++ tailWord_446554) baseStart_446554 baseEnd_446554 := by
    simpa [prefixWord, tailWord_446554, baseEnd_446554] using wordTrace_append hprefix tailTrace_446554
  have hstable : (prefixWord ++ tailWord_446554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446554).length < 2 ^ (prefixWord ++ tailWord_446554).sum := by decide
  have hdescent : baseEnd_446554 < baseStart_446554 := by decide
  rcases family_descends (prefixWord ++ tailWord_446554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446575 : List Nat := [1, 1, 2, 1, 3, 5, 7]
def baseStart_446575 : Nat := 118140960795 + 446575 * 2 ^ 59
def prefixEnd_446575 : Nat := 4983230072969 + 3 ^ 40 * 446575 * 2
def baseEnd_446575 : Nat := 22647666496957580934197

theorem tailTrace_446575 : CollatzResearch.WordTrace tailWord_446575 prefixEnd_446575 22647666496957580934197 := by
  unfold tailWord_446575
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287928357142518783029179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10858618904761679188686119 16287928357142518783029179)
  ·
    refine ⟨24431892535713778174543769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16287928357142518783029179 24431892535713778174543769)
    ·
      refine ⟨18323919401785333630907827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24431892535713778174543769 18323919401785333630907827)
      ·
        refine ⟨27485879102678000446361741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18323919401785333630907827 27485879102678000446361741)
        ·
          refine ⟨10307204663504250167385653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27485879102678000446361741 10307204663504250167385653)
          ·
            refine ⟨966300437203523453192405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10307204663504250167385653 966300437203523453192405)
            ·
              refine ⟨22647666496957580934197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 966300437203523453192405 22647666496957580934197)
              ·
                rfl

theorem cell20_446575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_446575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446575 prefixEnd_446575 := by exact prefixLift 446575
  have htrace : WordTrace (prefixWord ++ tailWord_446575) baseStart_446575 baseEnd_446575 := by
    simpa [prefixWord, tailWord_446575, baseEnd_446575] using wordTrace_append hprefix tailTrace_446575
  have hstable : (prefixWord ++ tailWord_446575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446575).length < 2 ^ (prefixWord ++ tailWord_446575).sum := by decide
  have hdescent : baseEnd_446575 < baseStart_446575 := by decide
  rcases family_descends (prefixWord ++ tailWord_446575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446578 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_446578 : Nat := 118140960795 + 446578 * 2 ^ 59
def prefixEnd_446578 : Nat := 4983230072969 + 3 ^ 40 * 446578 * 2
def baseEnd_446578 : Nat := 203830367754363551307761

theorem tailTrace_446578 : CollatzResearch.WordTrace tailWord_446578 prefixEnd_446578 203830367754363551307761 := by
  unfold tailWord_446578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072009444032912573847097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10858691850754433530258925 4072009444032912573847097)
  ·
    refine ⟨3054007083024684430385323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4072009444032912573847097 3054007083024684430385323)
    ·
      refine ⟨4581010624537026645577985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054007083024684430385323 4581010624537026645577985)
      ·
        refine ⟨3435757968402769984183489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4581010624537026645577985 3435757968402769984183489)
        ·
          refine ⟨2576818476302077488137617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3435757968402769984183489 2576818476302077488137617)
          ·
            refine ⟨1932613857226558116103213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576818476302077488137617 1932613857226558116103213)
            ·
              refine ⟨724730196459959293538705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1932613857226558116103213 724730196459959293538705)
              ·
                refine ⟨543547647344969470154029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724730196459959293538705 543547647344969470154029)
                ·
                  refine ⟨203830367754363551307761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543547647344969470154029 203830367754363551307761)
                  ·
                    rfl

theorem cell20_446578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_446578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446578 prefixEnd_446578 := by exact prefixLift 446578
  have htrace : WordTrace (prefixWord ++ tailWord_446578) baseStart_446578 baseEnd_446578 := by
    simpa [prefixWord, tailWord_446578, baseEnd_446578] using wordTrace_append hprefix tailTrace_446578
  have hstable : (prefixWord ++ tailWord_446578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446578).length < 2 ^ (prefixWord ++ tailWord_446578).sum := by decide
  have hdescent : baseEnd_446578 < baseStart_446578 := by decide
  rcases family_descends (prefixWord ++ tailWord_446578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446585 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_446585 : Nat := 118140960795 + 446585 * 2 ^ 59
def prefixEnd_446585 : Nat := 4983230072969 + 3 ^ 40 * 446585 * 2
def baseEnd_446585 : Nat := 203833562745102638074399

theorem tailTrace_446585 : CollatzResearch.WordTrace tailWord_446585 prefixEnd_446585 203833562745102638074399 := by
  unfold tailWord_446585
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288293087106290490893209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10858862058070860327262139 16288293087106290490893209)
  ·
    refine ⟨12216219815329717868169907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16288293087106290490893209 12216219815329717868169907)
    ·
      refine ⟨18324329722994576802254861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12216219815329717868169907 18324329722994576802254861)
      ·
        refine ⟨6871623646122966300845573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18324329722994576802254861 6871623646122966300845573)
        ·
          refine ⟨1288429433648056181408545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6871623646122966300845573 1288429433648056181408545)
          ·
            refine ⟨966322075236042136056409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288429433648056181408545 966322075236042136056409)
            ·
              refine ⟨724741556427031602042307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966322075236042136056409 724741556427031602042307)
              ·
                refine ⟨1087112334640547403063461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724741556427031602042307 1087112334640547403063461)
                ·
                  refine ⟨203833562745102638074399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087112334640547403063461 203833562745102638074399)
                  ·
                    rfl

theorem cell20_446585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_446585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446585 prefixEnd_446585 := by exact prefixLift 446585
  have htrace : WordTrace (prefixWord ++ tailWord_446585) baseStart_446585 baseEnd_446585 := by
    simpa [prefixWord, tailWord_446585, baseEnd_446585] using wordTrace_append hprefix tailTrace_446585
  have hstable : (prefixWord ++ tailWord_446585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446585).length < 2 ^ (prefixWord ++ tailWord_446585).sum := by decide
  have hdescent : baseEnd_446585 < baseStart_446585 := by decide
  rcases family_descends (prefixWord ++ tailWord_446585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446599 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 3]
def baseStart_446599 : Nat := 118140960795 + 446599 * 2 ^ 59
def prefixEnd_446599 : Nat := 4983230072969 + 3 ^ 40 * 446599 * 2
def baseEnd_446599 : Nat := 203839952726580811607675

theorem tailTrace_446599 : CollatzResearch.WordTrace tailWord_446599 prefixEnd_446599 203839952726580811607675 := by
  unfold tailWord_446599
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288803709055570881902851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10859202472703713921268567 16288803709055570881902851)
  ·
    refine ⟨24433205563583356322854277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16288803709055570881902851 24433205563583356322854277)
    ·
      refine ⟨4581226043171879310535177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24433205563583356322854277 4581226043171879310535177)
      ·
        refine ⟨3435919532378909482901383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4581226043171879310535177 3435919532378909482901383)
        ·
          refine ⟨5153879298568364224352075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435919532378909482901383 5153879298568364224352075)
          ·
            refine ⟨7730818947852546336528113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153879298568364224352075 7730818947852546336528113)
            ·
              refine ⟨5798114210889409752396085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7730818947852546336528113 5798114210889409752396085)
              ·
                refine ⟨543573207270882164287133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5798114210889409752396085 543573207270882164287133)
                ·
                  refine ⟨203839952726580811607675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543573207270882164287133 203839952726580811607675)
                  ·
                    rfl

theorem cell20_446599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_446599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446599 prefixEnd_446599 := by exact prefixLift 446599
  have htrace : WordTrace (prefixWord ++ tailWord_446599) baseStart_446599 baseEnd_446599 := by
    simpa [prefixWord, tailWord_446599, baseEnd_446599] using wordTrace_append hprefix tailTrace_446599
  have hstable : (prefixWord ++ tailWord_446599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446599).length < 2 ^ (prefixWord ++ tailWord_446599).sum := by decide
  have hdescent : baseEnd_446599 < baseStart_446599 := by decide
  rcases family_descends (prefixWord ++ tailWord_446599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446613 : List Nat := [1, 3, 2, 1, 1, 1, 5, 6]
def baseStart_446613 : Nat := 118140960795 + 446613 * 2 ^ 59
def prefixEnd_446613 : Nat := 4983230072969 + 3 ^ 40 * 446613 * 2
def baseEnd_446613 : Nat := 67948780902686328380317

theorem tailTrace_446613 : CollatzResearch.WordTrace tailWord_446613 prefixEnd_446613 67948780902686328380317 := by
  unfold tailWord_446613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16289314331004851272912493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10859542887336567515274995 16289314331004851272912493)
  ·
    refine ⟨6108492874126819227342185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16289314331004851272912493 6108492874126819227342185)
    ·
      refine ⟨4581369655595114420506639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6108492874126819227342185 4581369655595114420506639)
      ·
        refine ⟨6872054483392671630759959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581369655595114420506639 6872054483392671630759959)
        ·
          refine ⟨10308081725089007446139939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6872054483392671630759959 10308081725089007446139939)
          ·
            refine ⟨15462122587633511169209909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10308081725089007446139939 15462122587633511169209909)
            ·
              refine ⟨1449573992590641672113429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15462122587633511169209909 1449573992590641672113429)
              ·
                refine ⟨67948780902686328380317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1449573992590641672113429 67948780902686328380317)
                ·
                  rfl

theorem cell20_446613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_446613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446613 prefixEnd_446613 := by exact prefixLift 446613
  have htrace : WordTrace (prefixWord ++ tailWord_446613) baseStart_446613 baseEnd_446613 := by
    simpa [prefixWord, tailWord_446613, baseEnd_446613] using wordTrace_append hprefix tailTrace_446613
  have hstable : (prefixWord ++ tailWord_446613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446613).length < 2 ^ (prefixWord ++ tailWord_446613).sum := by decide
  have hdescent : baseEnd_446613 < baseStart_446613 := by decide
  rcases family_descends (prefixWord ++ tailWord_446613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446651 : List Nat := [1, 1, 1, 1, 1, 2, 8, 5]
def baseStart_446651 : Nat := 118140960795 + 446651 * 2 ^ 59
def prefixEnd_446651 : Nat := 4983230072969 + 3 ^ 40 * 446651 * 2
def baseEnd_446651 : Nat := 67954562314499913958043

theorem tailTrace_446651 : CollatzResearch.WordTrace tailWord_446651 prefixEnd_446651 67954562314499913958043 := by
  unfold tailWord_446651
  simp only [CollatzResearch.WordTrace]
  refine ⟨16290700304867183762795807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10860466869911455841863871 16290700304867183762795807)
  ·
    refine ⟨24436050457300775644193711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16290700304867183762795807 24436050457300775644193711)
    ·
      refine ⟨36654075685951163466290567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24436050457300775644193711 36654075685951163466290567)
      ·
        refine ⟨54981113528926745199435851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36654075685951163466290567 54981113528926745199435851)
        ·
          refine ⟨82471670293390117799153777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54981113528926745199435851 82471670293390117799153777)
          ·
            refine ⟨61853752720042588349365333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82471670293390117799153777 61853752720042588349365333)
            ·
              refine ⟨724848664687999082219125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 61853752720042588349365333 724848664687999082219125)
              ·
                refine ⟨67954562314499913958043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 724848664687999082219125 67954562314499913958043)
                ·
                  rfl

theorem cell20_446651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_446651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446651 prefixEnd_446651 := by exact prefixLift 446651
  have htrace : WordTrace (prefixWord ++ tailWord_446651) baseStart_446651 baseEnd_446651 := by
    simpa [prefixWord, tailWord_446651, baseEnd_446651] using wordTrace_append hprefix tailTrace_446651
  have hstable : (prefixWord ++ tailWord_446651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446651).length < 2 ^ (prefixWord ++ tailWord_446651).sum := by decide
  have hdescent : baseEnd_446651 < baseStart_446651 := by decide
  rcases family_descends (prefixWord ++ tailWord_446651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446691 : List Nat := [1, 1, 1, 8, 2, 1, 2, 2, 2]
def baseStart_446691 : Nat := 118140960795 + 446691 * 2 ^ 59
def prefixEnd_446691 : Nat := 4983230072969 + 3 ^ 40 * 446691 * 2
def baseEnd_446691 : Nat := 203881944033437380540633

theorem tailTrace_446691 : CollatzResearch.WordTrace tailWord_446691 prefixEnd_446691 203881944033437380540633 := by
  unfold tailWord_446691
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292159224722270594251927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10861439483148180396167951 16292159224722270594251927)
  ·
    refine ⟨24438238837083405891377891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16292159224722270594251927 24438238837083405891377891)
    ·
      refine ⟨36657358255625108837066837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24438238837083405891377891 36657358255625108837066837)
      ·
        refine ⟨429578417058106744184377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 36657358255625108837066837 429578417058106744184377)
        ·
          refine ⟨322183812793580058138283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429578417058106744184377 322183812793580058138283)
          ·
            refine ⟨483275719190370087207425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322183812793580058138283 483275719190370087207425)
            ·
              refine ⟨362456789392777565405569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483275719190370087207425 362456789392777565405569)
              ·
                refine ⟨271842592044583174054177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362456789392777565405569 271842592044583174054177)
                ·
                  refine ⟨203881944033437380540633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271842592044583174054177 203881944033437380540633)
                  ·
                    rfl

theorem cell20_446691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 2].length) (baseStart_446691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446691 prefixEnd_446691 := by exact prefixLift 446691
  have htrace : WordTrace (prefixWord ++ tailWord_446691) baseStart_446691 baseEnd_446691 := by
    simpa [prefixWord, tailWord_446691, baseEnd_446691] using wordTrace_append hprefix tailTrace_446691
  have hstable : (prefixWord ++ tailWord_446691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446691).length < 2 ^ (prefixWord ++ tailWord_446691).sum := by decide
  have hdescent : baseEnd_446691 < baseStart_446691 := by decide
  rcases family_descends (prefixWord ++ tailWord_446691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446695 : List Nat := [1, 1, 5, 3, 1, 1, 4, 2, 2]
def baseStart_446695 : Nat := 118140960795 + 446695 * 2 ^ 59
def prefixEnd_446695 : Nat := 4983230072969 + 3 ^ 40 * 446695 * 2
def baseEnd_446695 : Nat := 203883769742431144407283

theorem tailTrace_446695 : CollatzResearch.WordTrace tailWord_446695 prefixEnd_446695 203883769742431144407283 := by
  unfold tailWord_446695
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292305116707779277397539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10861536744471852851598359 16292305116707779277397539)
  ·
    refine ⟨24438457675061668916096309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16292305116707779277397539 24438457675061668916096309)
    ·
      refine ⟨2291105407037031460884029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24438457675061668916096309 2291105407037031460884029)
      ·
        refine ⟨859164527638886797831511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2291105407037031460884029 859164527638886797831511)
        ·
          refine ⟨1288746791458330196747267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859164527638886797831511 1288746791458330196747267)
          ·
            refine ⟨1933120187187495295120901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288746791458330196747267 1933120187187495295120901)
            ·
              refine ⟨362460035097655367835169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1933120187187495295120901 362460035097655367835169)
              ·
                refine ⟨271845026323241525876377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362460035097655367835169 271845026323241525876377)
                ·
                  refine ⟨203883769742431144407283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271845026323241525876377 203883769742431144407283)
                  ·
                    rfl

theorem cell20_446695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 2].length) (baseStart_446695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446695 prefixEnd_446695 := by exact prefixLift 446695
  have htrace : WordTrace (prefixWord ++ tailWord_446695) baseStart_446695 baseEnd_446695 := by
    simpa [prefixWord, tailWord_446695, baseEnd_446695] using wordTrace_append hprefix tailTrace_446695
  have hstable : (prefixWord ++ tailWord_446695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446695).length < 2 ^ (prefixWord ++ tailWord_446695).sum := by decide
  have hdescent : baseEnd_446695 < baseStart_446695 := by decide
  rcases family_descends (prefixWord ++ tailWord_446695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446699 : List Nat := [1, 1, 1, 1, 2, 5, 3, 4, 2]
def baseStart_446699 : Nat := 118140960795 + 446699 * 2 ^ 59
def prefixEnd_446699 : Nat := 4983230072969 + 3 ^ 40 * 446699 * 2
def baseEnd_446699 : Nat := 203885595451424908273933

theorem tailTrace_446699 : CollatzResearch.WordTrace tailWord_446699 prefixEnd_446699 203885595451424908273933 := by
  unfold tailWord_446699
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292451008693287960543151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10861634005795525307028767 16292451008693287960543151)
  ·
    refine ⟨24438676513039931940814727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16292451008693287960543151 24438676513039931940814727)
    ·
      refine ⟨36658014769559897911222091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24438676513039931940814727 36658014769559897911222091)
      ·
        refine ⟨54987022154339846866833137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36658014769559897911222091 54987022154339846866833137)
        ·
          refine ⟨41240266615754885150124853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54987022154339846866833137 41240266615754885150124853)
          ·
            refine ⟨3866274995227020482824205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41240266615754885150124853 3866274995227020482824205)
            ·
              refine ⟨1449853123210132681059077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3866274995227020482824205 1449853123210132681059077)
              ·
                refine ⟨271847460601899877698577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1449853123210132681059077 271847460601899877698577)
                ·
                  refine ⟨203885595451424908273933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271847460601899877698577 203885595451424908273933)
                  ·
                    rfl

theorem cell20_446699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 2].length) (baseStart_446699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446699 prefixEnd_446699 := by exact prefixLift 446699
  have htrace : WordTrace (prefixWord ++ tailWord_446699) baseStart_446699 baseEnd_446699 := by
    simpa [prefixWord, tailWord_446699, baseEnd_446699] using wordTrace_append hprefix tailTrace_446699
  have hstable : (prefixWord ++ tailWord_446699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446699).length < 2 ^ (prefixWord ++ tailWord_446699).sum := by decide
  have hdescent : baseEnd_446699 < baseStart_446699 := by decide
  rcases family_descends (prefixWord ++ tailWord_446699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446706 : List Nat := [3, 2, 1, 3, 2, 1, 3, 5]
def baseStart_446706 : Nat := 118140960795 + 446706 * 2 ^ 59
def prefixEnd_446706 : Nat := 4983230072969 + 3 ^ 40 * 446706 * 2
def baseEnd_446706 : Nat := 67962930147387998346857

theorem tailTrace_446706 : CollatzResearch.WordTrace tailWord_446706 prefixEnd_446706 67962930147387998346857 := by
  unfold tailWord_446706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073176579916982039011993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10861804213111952104031981 4073176579916982039011993)
  ·
    refine ⟨3054882434937736529258995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4073176579916982039011993 3054882434937736529258995)
    ·
      refine ⟨4582323652406604793888493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054882434937736529258995 4582323652406604793888493)
      ·
        refine ⟨1718371369652476797708185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4582323652406604793888493 1718371369652476797708185)
        ·
          refine ⟨1288778527239357598281139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718371369652476797708185 1288778527239357598281139)
          ·
            refine ⟨1933167790859036397421709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288778527239357598281139 1933167790859036397421709)
            ·
              refine ⟨724937921572138649033141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1933167790859036397421709 724937921572138649033141)
              ·
                refine ⟨67962930147387998346857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 724937921572138649033141 67962930147387998346857)
                ·
                  rfl

theorem cell20_446706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_446706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446706 prefixEnd_446706 := by exact prefixLift 446706
  have htrace : WordTrace (prefixWord ++ tailWord_446706) baseStart_446706 baseEnd_446706 := by
    simpa [prefixWord, tailWord_446706, baseEnd_446706] using wordTrace_append hprefix tailTrace_446706
  have hstable : (prefixWord ++ tailWord_446706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446706).length < 2 ^ (prefixWord ++ tailWord_446706).sum := by decide
  have hdescent : baseEnd_446706 < baseStart_446706 := by decide
  rcases family_descends (prefixWord ++ tailWord_446706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446737 : List Nat := [1, 2, 2, 1, 1, 5, 1, 5, 2]
def baseStart_446737 : Nat := 118140960795 + 446737 * 2 ^ 59
def prefixEnd_446737 : Nat := 4983230072969 + 3 ^ 40 * 446737 * 2
def baseEnd_446737 : Nat := 203902939686865665007111

theorem tailTrace_446737 : CollatzResearch.WordTrace tailWord_446737 prefixEnd_446737 203902939686865665007111 := by
  unfold tailWord_446737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16293836982555620450426465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10862557988370413633617643 16293836982555620450426465)
  ·
    refine ⟨12220377736916715337819849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16293836982555620450426465 12220377736916715337819849)
    ·
      refine ⟨9165283302687536503364887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12220377736916715337819849 9165283302687536503364887)
      ·
        refine ⟨13747924954031304755047331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9165283302687536503364887 13747924954031304755047331)
        ·
          refine ⟨20621887431046957132570997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13747924954031304755047331 20621887431046957132570997)
          ·
            refine ⟨1933301946660652231178531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20621887431046957132570997 1933301946660652231178531)
            ·
              refine ⟨2899952919990978346767797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933301946660652231178531 2899952919990978346767797)
              ·
                refine ⟨271870586249154220009481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2899952919990978346767797 271870586249154220009481)
                ·
                  refine ⟨203902939686865665007111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271870586249154220009481 203902939686865665007111)
                  ·
                    rfl

theorem cell20_446737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_446737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446737 prefixEnd_446737 := by exact prefixLift 446737
  have htrace : WordTrace (prefixWord ++ tailWord_446737) baseStart_446737 baseEnd_446737 := by
    simpa [prefixWord, tailWord_446737, baseEnd_446737] using wordTrace_append hprefix tailTrace_446737
  have hstable : (prefixWord ++ tailWord_446737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446737).length < 2 ^ (prefixWord ++ tailWord_446737).sum := by decide
  have hdescent : baseEnd_446737 < baseStart_446737 := by decide
  rcases family_descends (prefixWord ++ tailWord_446737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446751 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_446751 : Nat := 118140960795 + 446751 * 2 ^ 59
def prefixEnd_446751 : Nat := 4983230072969 + 3 ^ 40 * 446751 * 2
def baseEnd_446751 : Nat := 203909329668343838540387

theorem tailTrace_446751 : CollatzResearch.WordTrace tailWord_446751 prefixEnd_446751 203909329668343838540387 := by
  unfold tailWord_446751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16294347604504900841436107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10862898403003267227624071 16294347604504900841436107)
  ·
    refine ⟨24441521406757351262154161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16294347604504900841436107 24441521406757351262154161)
    ·
      refine ⟨18331141055068013446615621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24441521406757351262154161 18331141055068013446615621)
      ·
        refine ⟨3437088947825252521240429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18331141055068013446615621 3437088947825252521240429)
        ·
          refine ⟨1288908355434469695465161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3437088947825252521240429 1288908355434469695465161)
          ·
            refine ⟨966681266575852271598871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288908355434469695465161 966681266575852271598871)
            ·
              refine ⟨1450021899863778407398307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966681266575852271598871 1450021899863778407398307)
              ·
                refine ⟨2175032849795667611097461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450021899863778407398307 2175032849795667611097461)
                ·
                  refine ⟨203909329668343838540387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2175032849795667611097461 203909329668343838540387)
                  ·
                    rfl

theorem cell20_446751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_446751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446751 prefixEnd_446751 := by exact prefixLift 446751
  have htrace : WordTrace (prefixWord ++ tailWord_446751) baseStart_446751 baseEnd_446751 := by
    simpa [prefixWord, tailWord_446751, baseEnd_446751] using wordTrace_append hprefix tailTrace_446751
  have hstable : (prefixWord ++ tailWord_446751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446751).length < 2 ^ (prefixWord ++ tailWord_446751).sum := by decide
  have hdescent : baseEnd_446751 < baseStart_446751 := by decide
  rcases family_descends (prefixWord ++ tailWord_446751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446754 : List Nat := [3, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_446754 : Nat := 118140960795 + 446754 * 2 ^ 59
def prefixEnd_446754 : Nat := 4983230072969 + 3 ^ 40 * 446754 * 2
def baseEnd_446754 : Nat := 203910698950089161440375

theorem tailTrace_446754 : CollatzResearch.WordTrace tailWord_446754 prefixEnd_446754 203910698950089161440375 := by
  unfold tailWord_446754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073614255873508088448829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10862971348996021569196877 4073614255873508088448829)
  ·
    refine ⟨1527605345952565533168311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4073614255873508088448829 1527605345952565533168311)
    ·
      refine ⟨2291408018928848299752467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527605345952565533168311 2291408018928848299752467)
      ·
        refine ⟨3437112028393272449628701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291408018928848299752467 3437112028393272449628701)
        ·
          refine ⟨1288917010647477168610763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3437112028393272449628701 1288917010647477168610763)
          ·
            refine ⟨1933375515971215752916145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288917010647477168610763 1933375515971215752916145)
            ·
              refine ⟨1450031636978411814687109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933375515971215752916145 1450031636978411814687109)
              ·
                refine ⟨271880931933452215253833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1450031636978411814687109 271880931933452215253833)
                ·
                  refine ⟨203910698950089161440375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271880931933452215253833 203910698950089161440375)
                  ·
                    rfl

theorem cell20_446754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_446754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446754 prefixEnd_446754 := by exact prefixLift 446754
  have htrace : WordTrace (prefixWord ++ tailWord_446754) baseStart_446754 baseEnd_446754 := by
    simpa [prefixWord, tailWord_446754, baseEnd_446754] using wordTrace_append hprefix tailTrace_446754
  have hstable : (prefixWord ++ tailWord_446754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446754).length < 2 ^ (prefixWord ++ tailWord_446754).sum := by decide
  have hdescent : baseEnd_446754 < baseStart_446754 := by decide
  rcases family_descends (prefixWord ++ tailWord_446754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446782 : List Nat := [4, 2, 1, 2, 1, 3, 1, 6]
def baseStart_446782 : Nat := 118140960795 + 446782 * 2 ^ 59
def prefixEnd_446782 : Nat := 4983230072969 + 3 ^ 40 * 446782 * 2
def baseEnd_446782 : Nat := 67974492971015169502309

theorem tailTrace_446782 : CollatzResearch.WordTrace tailWord_446782 prefixEnd_446782 67974492971015169502309 := by
  unfold tailWord_446782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036934783424074141976825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10863652178261728757209733 2036934783424074141976825)
  ·
    refine ⟨1527701087568055606482619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2036934783424074141976825 1527701087568055606482619)
    ·
      refine ⟨2291551631352083409723929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527701087568055606482619 2291551631352083409723929)
      ·
        refine ⟨1718663723514062557292947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2291551631352083409723929 1718663723514062557292947)
        ·
          refine ⟨2577995585271093835939421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718663723514062557292947 2577995585271093835939421)
          ·
            refine ⟨966748344476660188477283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2577995585271093835939421 966748344476660188477283)
            ·
              refine ⟨1450122516714990282715925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966748344476660188477283 1450122516714990282715925)
              ·
                refine ⟨67974492971015169502309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1450122516714990282715925 67974492971015169502309)
                ·
                  rfl

theorem cell20_446782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_446782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446782 prefixEnd_446782 := by exact prefixLift 446782
  have htrace : WordTrace (prefixWord ++ tailWord_446782) baseStart_446782 baseEnd_446782 := by
    simpa [prefixWord, tailWord_446782, baseEnd_446782] using wordTrace_append hprefix tailTrace_446782
  have hstable : (prefixWord ++ tailWord_446782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446782).length < 2 ^ (prefixWord ++ tailWord_446782).sum := by decide
  have hdescent : baseEnd_446782 < baseStart_446782 := by decide
  rcases family_descends (prefixWord ++ tailWord_446782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446788 : List Nat := [2, 3, 4, 1, 2, 2, 1, 3, 2]
def baseStart_446788 : Nat := 118140960795 + 446788 * 2 ^ 59
def prefixEnd_446788 : Nat := 4983230072969 + 3 ^ 40 * 446788 * 2
def baseEnd_446788 : Nat := 203926217476536154306903

theorem tailTrace_446788 : CollatzResearch.WordTrace tailWord_446788 prefixEnd_446788 203926217476536154306903 := by
  unfold tailWord_446788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147848552685428080266509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10863798070247237440355345 8147848552685428080266509)
  ·
    refine ⟨3055443207257035530099941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8147848552685428080266509 3055443207257035530099941)
    ·
      refine ⟨572895601360694161893739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3055443207257035530099941 572895601360694161893739)
      ·
        refine ⟨859343402041041242840609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572895601360694161893739 859343402041041242840609)
        ·
          refine ⟨644507551530780932130457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859343402041041242840609 644507551530780932130457)
          ·
            refine ⟨483380663648085699097843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644507551530780932130457 483380663648085699097843)
            ·
              refine ⟨725070995472128548646765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483380663648085699097843 725070995472128548646765)
              ·
                refine ⟨271901623302048205742537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725070995472128548646765 271901623302048205742537)
                ·
                  refine ⟨203926217476536154306903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271901623302048205742537 203926217476536154306903)
                  ·
                    rfl

theorem cell20_446788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_446788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446788 prefixEnd_446788 := by exact prefixLift 446788
  have htrace : WordTrace (prefixWord ++ tailWord_446788) baseStart_446788 baseEnd_446788 := by
    simpa [prefixWord, tailWord_446788, baseEnd_446788] using wordTrace_append hprefix tailTrace_446788
  have hstable : (prefixWord ++ tailWord_446788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446788).length < 2 ^ (prefixWord ++ tailWord_446788).sum := by decide
  have hdescent : baseEnd_446788 < baseStart_446788 := by decide
  rcases family_descends (prefixWord ++ tailWord_446788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446823 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 3]
def baseStart_446823 : Nat := 118140960795 + 446823 * 2 ^ 59
def prefixEnd_446823 : Nat := 4983230072969 + 3 ^ 40 * 446823 * 2
def baseEnd_446823 : Nat := 203942192430231588140093

theorem tailTrace_446823 : CollatzResearch.WordTrace tailWord_446823 prefixEnd_446823 203942192430231588140093 := by
  unfold tailWord_446823
  simp only [CollatzResearch.WordTrace]
  refine ⟨16296973660244057138057123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10864649106829371425371415 16296973660244057138057123)
  ·
    refine ⟨24445460490366085707085685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16296973660244057138057123 24445460490366085707085685)
    ·
      refine ⟨2291761920971820535039283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24445460490366085707085685 2291761920971820535039283)
      ·
        refine ⟨3437642881457730802558925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291761920971820535039283 3437642881457730802558925)
        ·
          refine ⟨1289116080546649050959597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3437642881457730802558925 1289116080546649050959597)
          ·
            refine ⟨483418530204993394109849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1289116080546649050959597 483418530204993394109849)
            ·
              refine ⟨362563897653745045582387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483418530204993394109849 362563897653745045582387)
              ·
                refine ⟨543845846480617568373581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362563897653745045582387 543845846480617568373581)
                ·
                  refine ⟨203942192430231588140093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543845846480617568373581 203942192430231588140093)
                  ·
                    rfl

theorem cell20_446823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 3].length) (baseStart_446823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446823 prefixEnd_446823 := by exact prefixLift 446823
  have htrace : WordTrace (prefixWord ++ tailWord_446823) baseStart_446823 baseEnd_446823 := by
    simpa [prefixWord, tailWord_446823, baseEnd_446823] using wordTrace_append hprefix tailTrace_446823
  have hstable : (prefixWord ++ tailWord_446823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446823).length < 2 ^ (prefixWord ++ tailWord_446823).sum := by decide
  have hdescent : baseEnd_446823 < baseStart_446823 := by decide
  rcases family_descends (prefixWord ++ tailWord_446823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446858 : List Nat := [3, 1, 2, 5, 1, 8]
def baseStart_446858 : Nat := 118140960795 + 446858 * 2 ^ 59
def prefixEnd_446858 : Nat := 4983230072969 + 3 ^ 40 * 446858 * 2
def baseEnd_446858 : Nat := 7554006199404704517529

theorem tailTrace_446858 : CollatzResearch.WordTrace tailWord_446858 prefixEnd_446858 7554006199404704517529 := by
  unfold tailWord_446858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074562553779314528895307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10865500143411505410387485 4074562553779314528895307)
  ·
    refine ⟨6111843830668971793342961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4074562553779314528895307 6111843830668971793342961)
    ·
      refine ⟨4583882873001728845007221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6111843830668971793342961 4583882873001728845007221)
      ·
        refine ⟨429739019343912079219427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4583882873001728845007221 429739019343912079219427)
        ·
          refine ⟨644608529015868118829141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429739019343912079219427 644608529015868118829141)
          ·
            refine ⟨7554006199404704517529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 644608529015868118829141 7554006199404704517529)
            ·
              rfl

theorem cell20_446858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 8].length) (baseStart_446858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446858 prefixEnd_446858 := by exact prefixLift 446858
  have htrace : WordTrace (prefixWord ++ tailWord_446858) baseStart_446858 baseEnd_446858 := by
    simpa [prefixWord, tailWord_446858, baseEnd_446858] using wordTrace_append hprefix tailTrace_446858
  have hstable : (prefixWord ++ tailWord_446858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446858).length < 2 ^ (prefixWord ++ tailWord_446858).sum := by decide
  have hdescent : baseEnd_446858 < baseStart_446858 := by decide
  rcases family_descends (prefixWord ++ tailWord_446858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446916 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 3]
def baseStart_446916 : Nat := 118140960795 + 446916 * 2 ^ 59
def prefixEnd_446916 : Nat := 4983230072969 + 3 ^ 40 * 446916 * 2
def baseEnd_446916 : Nat := 203984640164336598039713

theorem tailTrace_446916 : CollatzResearch.WordTrace tailWord_446916 prefixEnd_446916 203984640164336598039713 := by
  unfold tailWord_446916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150182824453567010596301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10866910432604756014128401 8150182824453567010596301)
  ·
    refine ⟨3056318559170087628973613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8150182824453567010596301 3056318559170087628973613)
    ·
      refine ⟨1146119459688782860865105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3056318559170087628973613 1146119459688782860865105)
      ·
        refine ⟨859589594766587145648829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146119459688782860865105 859589594766587145648829)
        ·
          refine ⟨322346098037470179618311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 859589594766587145648829 322346098037470179618311)
          ·
            refine ⟨483519147056205269427467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322346098037470179618311 483519147056205269427467)
            ·
              refine ⟨725278720584307904141201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483519147056205269427467 725278720584307904141201)
              ·
                refine ⟨543959040438230928105901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725278720584307904141201 543959040438230928105901)
                ·
                  refine ⟨203984640164336598039713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543959040438230928105901 203984640164336598039713)
                  ·
                    rfl

theorem cell20_446916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_446916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446916 prefixEnd_446916 := by exact prefixLift 446916
  have htrace : WordTrace (prefixWord ++ tailWord_446916) baseStart_446916 baseEnd_446916 := by
    simpa [prefixWord, tailWord_446916, baseEnd_446916] using wordTrace_append hprefix tailTrace_446916
  have hstable : (prefixWord ++ tailWord_446916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446916).length < 2 ^ (prefixWord ++ tailWord_446916).sum := by decide
  have hdescent : baseEnd_446916 < baseStart_446916 := by decide
  rcases family_descends (prefixWord ++ tailWord_446916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446920 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_446920 : Nat := 118140960795 + 446920 * 2 ^ 59
def prefixEnd_446920 : Nat := 4983230072969 + 3 ^ 40 * 446920 * 2
def baseEnd_446920 : Nat := 203986465873330361906363

theorem tailTrace_446920 : CollatzResearch.WordTrace tailWord_446920 prefixEnd_446920 203986465873330361906363 := by
  unfold tailWord_446920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150255770446321352169107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10867007693928428469558809 8150255770446321352169107)
  ·
    refine ⟨12225383655669482028253661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150255770446321352169107 12225383655669482028253661)
    ·
      refine ⟨4584518870876055760595123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12225383655669482028253661 4584518870876055760595123)
      ·
        refine ⟨6876778306314083640892685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584518870876055760595123 6876778306314083640892685)
        ·
          refine ⟨2578791864867781365334757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6876778306314083640892685 2578791864867781365334757)
          ·
            refine ⟨483523474662709006000267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2578791864867781365334757 483523474662709006000267)
            ·
              refine ⟨725285211994063509000401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483523474662709006000267 725285211994063509000401)
              ·
                refine ⟨543963908995547631750301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725285211994063509000401 543963908995547631750301)
                ·
                  refine ⟨203986465873330361906363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543963908995547631750301 203986465873330361906363)
                  ·
                    rfl

theorem cell20_446920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_446920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446920 prefixEnd_446920 := by exact prefixLift 446920
  have htrace : WordTrace (prefixWord ++ tailWord_446920) baseStart_446920 baseEnd_446920 := by
    simpa [prefixWord, tailWord_446920, baseEnd_446920] using wordTrace_append hprefix tailTrace_446920
  have hstable : (prefixWord ++ tailWord_446920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446920).length < 2 ^ (prefixWord ++ tailWord_446920).sum := by decide
  have hdescent : baseEnd_446920 < baseStart_446920 := by decide
  rcases family_descends (prefixWord ++ tailWord_446920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446934 : List Nat := [5, 2, 1, 1, 1, 1, 2, 7]
def baseStart_446934 : Nat := 118140960795 + 446934 * 2 ^ 59
def prefixEnd_446934 : Nat := 4983230072969 + 3 ^ 40 * 446934 * 2
def baseEnd_446934 : Nat := 67997618618269511813213

theorem tailTrace_446934 : CollatzResearch.WordTrace tailWord_446934 prefixEnd_446934 67997618618269511813213 := by
  unfold tailWord_446934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018813885177620193459241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10867348108561282063565237 1018813885177620193459241)
  ·
    refine ⟨764110413883215145094431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1018813885177620193459241 764110413883215145094431)
    ·
      refine ⟨1146165620824822717641647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764110413883215145094431 1146165620824822717641647)
      ·
        refine ⟨1719248431237234076462471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146165620824822717641647 1719248431237234076462471)
        ·
          refine ⟨2578872646855851114693707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719248431237234076462471 2578872646855851114693707)
          ·
            refine ⟨3868308970283776672040561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578872646855851114693707 3868308970283776672040561)
            ·
              refine ⟨2901231727712832504030421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3868308970283776672040561 2901231727712832504030421)
              ·
                refine ⟨67997618618269511813213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2901231727712832504030421 67997618618269511813213)
                ·
                  rfl

theorem cell20_446934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_446934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446934 prefixEnd_446934 := by exact prefixLift 446934
  have htrace : WordTrace (prefixWord ++ tailWord_446934) baseStart_446934 baseEnd_446934 := by
    simpa [prefixWord, tailWord_446934, baseEnd_446934] using wordTrace_append hprefix tailTrace_446934
  have hstable : (prefixWord ++ tailWord_446934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446934).length < 2 ^ (prefixWord ++ tailWord_446934).sum := by decide
  have hdescent : baseEnd_446934 < baseStart_446934 := by decide
  rcases family_descends (prefixWord ++ tailWord_446934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446969 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_446969 : Nat := 118140960795 + 446969 * 2 ^ 59
def prefixEnd_446969 : Nat := 4983230072969 + 3 ^ 40 * 446969 * 2
def baseEnd_446969 : Nat := 204008830808503969272829

theorem tailTrace_446969 : CollatzResearch.WordTrace tailWord_446969 prefixEnd_446969 204008830808503969272829 := by
  unfold tailWord_446969
  simp only [CollatzResearch.WordTrace]
  refine ⟨16302298717715124072871961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10868199145143416048581307 16302298717715124072871961)
  ·
    refine ⟨12226724038286343054653971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16302298717715124072871961 12226724038286343054653971)
    ·
      refine ⟨18340086057429514581980957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12226724038286343054653971 18340086057429514581980957)
      ·
        refine ⟨6877532271536067968242859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18340086057429514581980957 6877532271536067968242859)
        ·
          refine ⟨10316298407304101952364289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877532271536067968242859 10316298407304101952364289)
          ·
            refine ⟨7737223805478076464273217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10316298407304101952364289 7737223805478076464273217)
            ·
              refine ⟨5802917854108557348204913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7737223805478076464273217 5802917854108557348204913)
              ·
                refine ⟨4352188390581418011153685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5802917854108557348204913 4352188390581418011153685)
                ·
                  refine ⟨204008830808503969272829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4352188390581418011153685 204008830808503969272829)
                  ·
                    rfl

theorem cell20_446969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_446969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446969 prefixEnd_446969 := by exact prefixLift 446969
  have htrace : WordTrace (prefixWord ++ tailWord_446969) baseStart_446969 baseEnd_446969 := by
    simpa [prefixWord, tailWord_446969, baseEnd_446969] using wordTrace_append hprefix tailTrace_446969
  have hstable : (prefixWord ++ tailWord_446969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446969).length < 2 ^ (prefixWord ++ tailWord_446969).sum := by decide
  have hdescent : baseEnd_446969 < baseStart_446969 := by decide
  rcases family_descends (prefixWord ++ tailWord_446969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446978 : List Nat := [3, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_446978 : Nat := 118140960795 + 446978 * 2 ^ 59
def prefixEnd_446978 : Nat := 4983230072969 + 3 ^ 40 * 446978 * 2
def baseEnd_446978 : Nat := 204012938653739937972793

theorem tailTrace_446978 : CollatzResearch.WordTrace tailWord_446978 prefixEnd_446978 204012938653739937972793 := by
  unfold tailWord_446978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075656743670629652487397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10868417983121679073299725 4075656743670629652487397)
  ·
    refine ⟨764185639438243059841387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4075656743670629652487397 764185639438243059841387)
    ·
      refine ⟨1146278459157364589762081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764185639438243059841387 1146278459157364589762081)
      ·
        refine ⟨859708844368023442321561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146278459157364589762081 859708844368023442321561)
        ·
          refine ⟨644781633276017581741171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859708844368023442321561 644781633276017581741171)
          ·
            refine ⟨967172449914026372611757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644781633276017581741171 967172449914026372611757)
            ·
              refine ⟨362689668717759889729409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967172449914026372611757 362689668717759889729409)
              ·
                refine ⟨272017251538319917297057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362689668717759889729409 272017251538319917297057)
                ·
                  refine ⟨204012938653739937972793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272017251538319917297057 204012938653739937972793)
                  ·
                    rfl

theorem cell20_446978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_446978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446978 prefixEnd_446978 := by exact prefixLift 446978
  have htrace : WordTrace (prefixWord ++ tailWord_446978) baseStart_446978 baseEnd_446978 := by
    simpa [prefixWord, tailWord_446978, baseEnd_446978] using wordTrace_append hprefix tailTrace_446978
  have hstable : (prefixWord ++ tailWord_446978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446978).length < 2 ^ (prefixWord ++ tailWord_446978).sum := by decide
  have hdescent : baseEnd_446978 < baseStart_446978 := by decide
  rcases family_descends (prefixWord ++ tailWord_446978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446989 : List Nat := [1, 7, 1, 1, 1, 1, 1, 7]
def baseStart_446989 : Nat := 118140960795 + 446989 * 2 ^ 59
def prefixEnd_446989 : Nat := 4983230072969 + 3 ^ 40 * 446989 * 2
def baseEnd_446989 : Nat := 68005986451157596202027

theorem tailTrace_446989 : CollatzResearch.WordTrace tailWord_446989 prefixEnd_446989 68005986451157596202027 := by
  unfold tailWord_446989
  simp only [CollatzResearch.WordTrace]
  refine ⟨16303028177642667488600021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10868685451761778325733347 16303028177642667488600021)
  ·
    refine ⟨382102222913500019264063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16303028177642667488600021 382102222913500019264063)
    ·
      refine ⟨573153334370250028896095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382102222913500019264063 573153334370250028896095)
      ·
        refine ⟨859730001555375043344143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573153334370250028896095 859730001555375043344143)
        ·
          refine ⟨1289595002333062565016215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859730001555375043344143 1289595002333062565016215)
          ·
            refine ⟨1934392503499593847524323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289595002333062565016215 1934392503499593847524323)
            ·
              refine ⟨2901588755249390771286485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934392503499593847524323 2901588755249390771286485)
              ·
                refine ⟨68005986451157596202027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2901588755249390771286485 68005986451157596202027)
                ·
                  rfl

theorem cell20_446989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_446989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_446989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_446989 prefixEnd_446989 := by exact prefixLift 446989
  have htrace : WordTrace (prefixWord ++ tailWord_446989) baseStart_446989 baseEnd_446989 := by
    simpa [prefixWord, tailWord_446989, baseEnd_446989] using wordTrace_append hprefix tailTrace_446989
  have hstable : (prefixWord ++ tailWord_446989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446989).length < 2 ^ (prefixWord ++ tailWord_446989).sum := by decide
  have hdescent : baseEnd_446989 < baseStart_446989 := by decide
  rcases family_descends (prefixWord ++ tailWord_446989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447007 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_447007 : Nat := 118140960795 + 447007 * 2 ^ 59
def prefixEnd_447007 : Nat := 4983230072969 + 3 ^ 40 * 447007 * 2
def baseEnd_447007 : Nat := 204026175043944726006007

theorem tailTrace_447007 : CollatzResearch.WordTrace tailWord_447007 prefixEnd_447007 204026175043944726006007 := by
  unfold tailWord_447007
  simp only [CollatzResearch.WordTrace]
  refine ⟨16303684691577456562755275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10869123127718304375170183 16303684691577456562755275)
  ·
    refine ⟨24455527037366184844132913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16303684691577456562755275 24455527037366184844132913)
    ·
      refine ⟨18341645278024638633099685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24455527037366184844132913 18341645278024638633099685)
      ·
        refine ⟨3439058489629619743706191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18341645278024638633099685 3439058489629619743706191)
        ·
          refine ⟨5158587734444429615559287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439058489629619743706191 5158587734444429615559287)
          ·
            refine ⟨7737881601666644423338931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158587734444429615559287 7737881601666644423338931)
            ·
              refine ⟨11606822402499966635008397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737881601666644423338931 11606822402499966635008397)
              ·
                refine ⟨4352558400937487488128149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11606822402499966635008397 4352558400937487488128149)
                ·
                  refine ⟨204026175043944726006007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4352558400937487488128149 204026175043944726006007)
                  ·
                    rfl

theorem cell20_447007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_447007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447007 prefixEnd_447007 := by exact prefixLift 447007
  have htrace : WordTrace (prefixWord ++ tailWord_447007) baseStart_447007 baseEnd_447007 := by
    simpa [prefixWord, tailWord_447007, baseEnd_447007] using wordTrace_append hprefix tailTrace_447007
  have hstable : (prefixWord ++ tailWord_447007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447007).length < 2 ^ (prefixWord ++ tailWord_447007).sum := by decide
  have hdescent : baseEnd_447007 < baseStart_447007 := by decide
  rcases family_descends (prefixWord ++ tailWord_447007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447037 : List Nat := [1, 4, 1, 3, 2, 3, 2, 2, 2]
def baseStart_447037 : Nat := 118140960795 + 447037 * 2 ^ 59
def prefixEnd_447037 : Nat := 4983230072969 + 3 ^ 40 * 447037 * 2
def baseEnd_447037 : Nat := 204039867861397955005885

theorem tailTrace_447037 : CollatzResearch.WordTrace tailWord_447037 prefixEnd_447037 204039867861397955005885 := by
  unfold tailWord_447037
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304778881468771686347365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10869852587645847790898243 16304778881468771686347365)
  ·
    refine ⟨3057146040275394691190131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16304778881468771686347365 3057146040275394691190131)
    ·
      refine ⟨4585719060413092036785197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3057146040275394691190131 4585719060413092036785197)
      ·
        refine ⟨1719644647654909513794449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4585719060413092036785197 1719644647654909513794449)
        ·
          refine ⟨1289733485741182135345837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719644647654909513794449 1289733485741182135345837)
          ·
            refine ⟨483650057152943300754689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1289733485741182135345837 483650057152943300754689)
            ·
              refine ⟨362737542864707475566017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483650057152943300754689 362737542864707475566017)
              ·
                refine ⟨272053157148530606674513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362737542864707475566017 272053157148530606674513)
                ·
                  refine ⟨204039867861397955005885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272053157148530606674513 204039867861397955005885)
                  ·
                    rfl

theorem cell20_447037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_447037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447037 prefixEnd_447037 := by exact prefixLift 447037
  have htrace : WordTrace (prefixWord ++ tailWord_447037) baseStart_447037 baseEnd_447037 := by
    simpa [prefixWord, tailWord_447037, baseEnd_447037] using wordTrace_append hprefix tailTrace_447037
  have hstable : (prefixWord ++ tailWord_447037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447037).length < 2 ^ (prefixWord ++ tailWord_447037).sum := by decide
  have hdescent : baseEnd_447037 < baseStart_447037 := by decide
  rcases family_descends (prefixWord ++ tailWord_447037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447076 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_447076 : Nat := 118140960795 + 447076 * 2 ^ 59
def prefixEnd_447076 : Nat := 4983230072969 + 3 ^ 40 * 447076 * 2
def baseEnd_447076 : Nat := 204057668524087152705725

theorem tailTrace_447076 : CollatzResearch.WordTrace tailWord_447076 prefixEnd_447076 204057668524087152705725 := by
  unfold tailWord_447076
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153100664163740673508541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10870800885551654231344721 8153100664163740673508541)
  ·
    refine ⟨3057412749061402752565703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8153100664163740673508541 3057412749061402752565703)
    ·
      refine ⟨4586119123592104128848555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3057412749061402752565703 4586119123592104128848555)
      ·
        refine ⟨6879178685388156193272833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586119123592104128848555 6879178685388156193272833)
        ·
          refine ⟨5159384014041117144954625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6879178685388156193272833 5159384014041117144954625)
          ·
            refine ⟨3869538010530837858715969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5159384014041117144954625 3869538010530837858715969)
            ·
              refine ⟨2902153507898128394036977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869538010530837858715969 2902153507898128394036977)
              ·
                refine ⟨2176615130923596295527733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902153507898128394036977 2176615130923596295527733)
                ·
                  refine ⟨204057668524087152705725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2176615130923596295527733 204057668524087152705725)
                  ·
                    rfl

theorem cell20_447076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_447076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447076 prefixEnd_447076 := by exact prefixLift 447076
  have htrace : WordTrace (prefixWord ++ tailWord_447076) baseStart_447076 baseEnd_447076 := by
    simpa [prefixWord, tailWord_447076, baseEnd_447076] using wordTrace_append hprefix tailTrace_447076
  have hstable : (prefixWord ++ tailWord_447076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447076).length < 2 ^ (prefixWord ++ tailWord_447076).sum := by decide
  have hdescent : baseEnd_447076 < baseStart_447076 := by decide
  rcases family_descends (prefixWord ++ tailWord_447076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447124 : List Nat := [2, 4, 2, 2, 1, 2, 1, 6]
def baseStart_447124 : Nat := 118140960795 + 447124 * 2 ^ 59
def prefixEnd_447124 : Nat := 4983230072969 + 3 ^ 40 * 447124 * 2
def baseEnd_447124 : Nat := 68026525677337439701843

theorem tailTrace_447124 : CollatzResearch.WordTrace tailWord_447124 prefixEnd_447124 68026525677337439701843 := by
  unfold tailWord_447124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153976016076792772382213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10871968021435723696509617 8153976016076792772382213)
  ·
    refine ⟨1528870503014398644821665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8153976016076792772382213 1528870503014398644821665)
    ·
      refine ⟨1146652877260798983616249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528870503014398644821665 1146652877260798983616249)
      ·
        refine ⟨859989657945599237712187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146652877260798983616249 859989657945599237712187)
        ·
          refine ⟨1289984486918398856568281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859989657945599237712187 1289984486918398856568281)
          ·
            refine ⟨967488365188799142426211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289984486918398856568281 967488365188799142426211)
            ·
              refine ⟨1451232547783198713639317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967488365188799142426211 1451232547783198713639317)
              ·
                refine ⟨68026525677337439701843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1451232547783198713639317 68026525677337439701843)
                ·
                  rfl

theorem cell20_447124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_447124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447124 prefixEnd_447124 := by exact prefixLift 447124
  have htrace : WordTrace (prefixWord ++ tailWord_447124) baseStart_447124 baseEnd_447124 := by
    simpa [prefixWord, tailWord_447124, baseEnd_447124] using wordTrace_append hprefix tailTrace_447124
  have hstable : (prefixWord ++ tailWord_447124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447124).length < 2 ^ (prefixWord ++ tailWord_447124).sum := by decide
  have hdescent : baseEnd_447124 < baseStart_447124 := by decide
  rcases family_descends (prefixWord ++ tailWord_447124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447130 : List Nat := [3, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_447130 : Nat := 118140960795 + 447130 * 2 ^ 59
def prefixEnd_447130 : Nat := 4983230072969 + 3 ^ 40 * 447130 * 2
def baseEnd_447130 : Nat := 204082315595502964905505

theorem tailTrace_447130 : CollatzResearch.WordTrace tailWord_447130 prefixEnd_447130 204082315595502964905505 := by
  unfold tailWord_447130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077042717532962142370711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10872113913421232379655229 4077042717532962142370711)
  ·
    refine ⟨6115564076299443213556067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4077042717532962142370711 6115564076299443213556067)
    ·
      refine ⟨9173346114449164820334101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6115564076299443213556067 9173346114449164820334101)
      ·
        refine ⟨430000599114804600953161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9173346114449164820334101 430000599114804600953161)
        ·
          refine ⟨322500449336103450714871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430000599114804600953161 322500449336103450714871)
          ·
            refine ⟨483750674004155176072307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322500449336103450714871 483750674004155176072307)
            ·
              refine ⟨725626011006232764108461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483750674004155176072307 725626011006232764108461)
              ·
                refine ⟨272109754127337286540673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725626011006232764108461 272109754127337286540673)
                ·
                  refine ⟨204082315595502964905505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272109754127337286540673 204082315595502964905505)
                  ·
                    rfl

theorem cell20_447130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_447130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447130 prefixEnd_447130 := by exact prefixLift 447130
  have htrace : WordTrace (prefixWord ++ tailWord_447130) baseStart_447130 baseEnd_447130 := by
    simpa [prefixWord, tailWord_447130, baseEnd_447130] using wordTrace_append hprefix tailTrace_447130
  have hstable : (prefixWord ++ tailWord_447130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447130).length < 2 ^ (prefixWord ++ tailWord_447130).sum := by decide
  have hdescent : baseEnd_447130 < baseStart_447130 := by decide
  rcases family_descends (prefixWord ++ tailWord_447130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447152 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_447152 : Nat := 118140960795 + 447152 * 2 ^ 59
def prefixEnd_447152 : Nat := 4983230072969 + 3 ^ 40 * 447152 * 2
def baseEnd_447152 : Nat := 204092356994968666172081

theorem tailTrace_447152 : CollatzResearch.WordTrace tailWord_447152 prefixEnd_447152 204092356994968666172081 := by
  unfold tailWord_447152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8154486638026073163391855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10872648850701430884522473 8154486638026073163391855)
  ·
    refine ⟨12231729957039109745087783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8154486638026073163391855 12231729957039109745087783)
    ·
      refine ⟨18347594935558664617631675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12231729957039109745087783 18347594935558664617631675)
      ·
        refine ⟨27521392403337996926447513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18347594935558664617631675 27521392403337996926447513)
        ·
          refine ⟨20641044302503497694835635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27521392403337996926447513 20641044302503497694835635)
          ·
            refine ⟨30961566453755246542253453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20641044302503497694835635 30961566453755246542253453)
            ·
              refine ⟨11610587420158217453345045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30961566453755246542253453 11610587420158217453345045)
              ·
                refine ⟨544246285319916443125549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11610587420158217453345045 544246285319916443125549)
                ·
                  refine ⟨204092356994968666172081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544246285319916443125549 204092356994968666172081)
                  ·
                    rfl

theorem cell20_447152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_447152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447152 prefixEnd_447152 := by exact prefixLift 447152
  have htrace : WordTrace (prefixWord ++ tailWord_447152) baseStart_447152 baseEnd_447152 := by
    simpa [prefixWord, tailWord_447152, baseEnd_447152] using wordTrace_append hprefix tailTrace_447152
  have hstable : (prefixWord ++ tailWord_447152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447152).length < 2 ^ (prefixWord ++ tailWord_447152).sum := by decide
  have hdescent : baseEnd_447152 < baseStart_447152 := by decide
  rcases family_descends (prefixWord ++ tailWord_447152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447204 : List Nat := [2, 3, 1, 1, 1, 12]
def baseStart_447204 : Nat := 118140960795 + 447204 * 2 ^ 59
def prefixEnd_447204 : Nat := 4983230072969 + 3 ^ 40 * 447204 * 2
def baseEnd_447204 : Nat := 7559855230069910979205

theorem tailTrace_447204 : CollatzResearch.WordTrace tailWord_447204 prefixEnd_447204 7559855230069910979205 := by
  unfold tailWord_447204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155434935931879603838333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10873913247909172805117777 8155434935931879603838333)
  ·
    refine ⟨3058288100974454851439375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8155434935931879603838333 3058288100974454851439375)
    ·
      refine ⟨4587432151461682277159063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3058288100974454851439375 4587432151461682277159063)
      ·
        refine ⟨6881148227192523415738595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587432151461682277159063 6881148227192523415738595)
        ·
          refine ⟨10321722340788785123607893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881148227192523415738595 10321722340788785123607893)
          ·
            refine ⟨7559855230069910979205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10321722340788785123607893 7559855230069910979205)
            ·
              rfl

theorem cell20_447204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 12].length) (baseStart_447204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447204 prefixEnd_447204 := by exact prefixLift 447204
  have htrace : WordTrace (prefixWord ++ tailWord_447204) baseStart_447204 baseEnd_447204 := by
    simpa [prefixWord, tailWord_447204, baseEnd_447204] using wordTrace_append hprefix tailTrace_447204
  have hstable : (prefixWord ++ tailWord_447204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447204).length < 2 ^ (prefixWord ++ tailWord_447204).sum := by decide
  have hdescent : baseEnd_447204 < baseStart_447204 := by decide
  rcases family_descends (prefixWord ++ tailWord_447204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447293 : List Nat := [1, 4, 1, 4, 2, 2, 2, 4]
def baseStart_447293 : Nat := 118140960795 + 447293 * 2 ^ 59
def prefixEnd_447293 : Nat := 4983230072969 + 3 ^ 40 * 447293 * 2
def baseEnd_447293 : Nat := 68052237745666280823835

theorem tailTrace_447293 : CollatzResearch.WordTrace tailWord_447293 prefixEnd_447293 68052237745666280823835 := by
  unfold tailWord_447293
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314115968541327407666533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10876077312360884938444355 16314115968541327407666533)
  ·
    refine ⟨3058896744101498888937475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16314115968541327407666533 3058896744101498888937475)
    ·
      refine ⟨4588345116152248333406213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3058896744101498888937475 4588345116152248333406213)
      ·
        refine ⟨860314709278546562513665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4588345116152248333406213 860314709278546562513665)
        ·
          refine ⟨645236031958909921885249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860314709278546562513665 645236031958909921885249)
          ·
            refine ⟨483927023969182441413937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645236031958909921885249 483927023969182441413937)
            ·
              refine ⟨362945267976886831060453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483927023969182441413937 362945267976886831060453)
              ·
                refine ⟨68052237745666280823835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362945267976886831060453 68052237745666280823835)
                ·
                  rfl

theorem cell20_447293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_447293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447293 prefixEnd_447293 := by exact prefixLift 447293
  have htrace : WordTrace (prefixWord ++ tailWord_447293) baseStart_447293 baseEnd_447293 := by
    simpa [prefixWord, tailWord_447293, baseEnd_447293] using wordTrace_append hprefix tailTrace_447293
  have hstable : (prefixWord ++ tailWord_447293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447293).length < 2 ^ (prefixWord ++ tailWord_447293).sum := by decide
  have hdescent : baseEnd_447293 < baseStart_447293 := by decide
  rcases family_descends (prefixWord ++ tailWord_447293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447335 : List Nat := [1, 1, 5, 1, 2, 3, 2, 5]
def baseStart_447335 : Nat := 118140960795 + 447335 * 2 ^ 59
def prefixEnd_447335 : Nat := 4983230072969 + 3 ^ 40 * 447335 * 2
def baseEnd_447335 : Nat := 68058627727144454357111

theorem tailTrace_447335 : CollatzResearch.WordTrace tailWord_447335 prefixEnd_447335 68058627727144454357111 := by
  unfold tailWord_447335
  simp only [CollatzResearch.WordTrace]
  refine ⟨16315647834389168580695459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10877098556259445720463639 16315647834389168580695459)
  ·
    refine ⟨24473471751583752871043189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16315647834389168580695459 24473471751583752871043189)
    ·
      refine ⟨2294387976710976831660299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24473471751583752871043189 2294387976710976831660299)
      ·
        refine ⟨3441581965066465247490449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294387976710976831660299 3441581965066465247490449)
        ·
          refine ⟨2581186473799848935617837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441581965066465247490449 2581186473799848935617837)
          ·
            refine ⟨967944927674943350856689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2581186473799848935617837 967944927674943350856689)
            ·
              refine ⟨725958695756207513142517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967944927674943350856689 725958695756207513142517)
              ·
                refine ⟨68058627727144454357111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 725958695756207513142517 68058627727144454357111)
                ·
                  rfl

theorem cell20_447335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_447335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447335 prefixEnd_447335 := by exact prefixLift 447335
  have htrace : WordTrace (prefixWord ++ tailWord_447335) baseStart_447335 baseEnd_447335 := by
    simpa [prefixWord, tailWord_447335, baseEnd_447335] using wordTrace_append hprefix tailTrace_447335
  have hstable : (prefixWord ++ tailWord_447335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447335).length < 2 ^ (prefixWord ++ tailWord_447335).sum := by decide
  have hdescent : baseEnd_447335 < baseStart_447335 := by decide
  rcases family_descends (prefixWord ++ tailWord_447335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447428 : List Nat := [2, 3, 3, 3, 1, 1, 7]
def baseStart_447428 : Nat := 118140960795 + 447428 * 2 ^ 59
def prefixEnd_447428 : Nat := 4983230072969 + 3 ^ 40 * 447428 * 2
def baseEnd_447428 : Nat := 22690925657282041441217

theorem tailTrace_447428 : CollatzResearch.WordTrace tailWord_447428 prefixEnd_447428 22690925657282041441217 := by
  unfold tailWord_447428
  simp only [CollatzResearch.WordTrace]
  refine ⟨8159519911526122731915469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10879359882034830309220625 8159519911526122731915469)
  ·
    refine ⟨3059819966822296024468301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8159519911526122731915469 3059819966822296024468301)
    ·
      refine ⟨1147432487558361009175613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3059819966822296024468301 1147432487558361009175613)
      ·
        refine ⟨430287182834385378440855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1147432487558361009175613 430287182834385378440855)
        ·
          refine ⟨645430774251578067661283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430287182834385378440855 645430774251578067661283)
          ·
            refine ⟨968146161377367101491925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645430774251578067661283 968146161377367101491925)
            ·
              refine ⟨22690925657282041441217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 968146161377367101491925 22690925657282041441217)
              ·
                rfl

theorem cell20_447428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 7].length) (baseStart_447428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447428 prefixEnd_447428 := by exact prefixLift 447428
  have htrace : WordTrace (prefixWord ++ tailWord_447428) baseStart_447428 baseEnd_447428 := by
    simpa [prefixWord, tailWord_447428, baseEnd_447428] using wordTrace_append hprefix tailTrace_447428
  have hstable : (prefixWord ++ tailWord_447428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447428).length < 2 ^ (prefixWord ++ tailWord_447428).sum := by decide
  have hdescent : baseEnd_447428 < baseStart_447428 := by decide
  rcases family_descends (prefixWord ++ tailWord_447428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447435 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 3]
def baseStart_447435 : Nat := 118140960795 + 447435 * 2 ^ 59
def prefixEnd_447435 : Nat := 4983230072969 + 3 ^ 40 * 447435 * 2
def baseEnd_447435 : Nat := 204221525906277459737591

theorem tailTrace_447435 : CollatzResearch.WordTrace tailWord_447435 prefixEnd_447435 204221525906277459737591 := by
  unfold tailWord_447435
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319295134026885659335759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10879530089351257106223839 16319295134026885659335759)
  ·
    refine ⟨24478942701040328489003639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16319295134026885659335759 24478942701040328489003639)
    ·
      refine ⟨36718414051560492733505459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478942701040328489003639 36718414051560492733505459)
      ·
        refine ⟨55077621077340739100258189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36718414051560492733505459 55077621077340739100258189)
        ·
          refine ⟨20654107904002777162596821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55077621077340739100258189 20654107904002777162596821)
          ·
            refine ⟨484080654000065089748363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20654107904002777162596821 484080654000065089748363)
            ·
              refine ⟨726120981000097634622545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484080654000065089748363 726120981000097634622545)
              ·
                refine ⟨544590735750073225966909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726120981000097634622545 544590735750073225966909)
                ·
                  refine ⟨204221525906277459737591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544590735750073225966909 204221525906277459737591)
                  ·
                    rfl

theorem cell20_447435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_447435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447435 prefixEnd_447435 := by exact prefixLift 447435
  have htrace : WordTrace (prefixWord ++ tailWord_447435) baseStart_447435 baseEnd_447435 := by
    simpa [prefixWord, tailWord_447435, baseEnd_447435] using wordTrace_append hprefix tailTrace_447435
  have hstable : (prefixWord ++ tailWord_447435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447435).length < 2 ^ (prefixWord ++ tailWord_447435).sum := by decide
  have hdescent : baseEnd_447435 < baseStart_447435 := by decide
  rcases family_descends (prefixWord ++ tailWord_447435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447442 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_447442 : Nat := 118140960795 + 447442 * 2 ^ 59
def prefixEnd_447442 : Nat := 4983230072969 + 3 ^ 40 * 447442 * 2
def baseEnd_447442 : Nat := 204224720897016546504229

theorem tailTrace_447442 : CollatzResearch.WordTrace tailWord_447442 prefixEnd_447442 204224720897016546504229 := by
  unfold tailWord_447442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079887611250381463710145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10879700296667683903227053 4079887611250381463710145)
  ·
    refine ⟨3059915708437786097782609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4079887611250381463710145 3059915708437786097782609)
    ·
      refine ⟨2294936781328339573336957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3059915708437786097782609 2294936781328339573336957)
      ·
        refine ⟨860601292998127340001359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2294936781328339573336957 860601292998127340001359)
        ·
          refine ⟨1290901939497191010002039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860601292998127340001359 1290901939497191010002039)
          ·
            refine ⟨1936352909245786515003059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290901939497191010002039 1936352909245786515003059)
            ·
              refine ⟨2904529363868679772504589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936352909245786515003059 2904529363868679772504589)
              ·
                refine ⟨1089198511450754914689221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2904529363868679772504589 1089198511450754914689221)
                ·
                  refine ⟨204224720897016546504229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1089198511450754914689221 204224720897016546504229)
                  ·
                    rfl

theorem cell20_447442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_447442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447442 prefixEnd_447442 := by exact prefixLift 447442
  have htrace : WordTrace (prefixWord ++ tailWord_447442) baseStart_447442 baseEnd_447442 := by
    simpa [prefixWord, tailWord_447442, baseEnd_447442] using wordTrace_append hprefix tailTrace_447442
  have hstable : (prefixWord ++ tailWord_447442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447442).length < 2 ^ (prefixWord ++ tailWord_447442).sum := by decide
  have hdescent : baseEnd_447442 < baseStart_447442 := by decide
  rcases family_descends (prefixWord ++ tailWord_447442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447466 : List Nat := [3, 1, 3, 1, 2, 4, 2, 4]
def baseStart_447466 : Nat := 118140960795 + 447466 * 2 ^ 59
def prefixEnd_447466 : Nat := 4983230072969 + 3 ^ 40 * 447466 * 2
def baseEnd_447466 : Nat := 68078558383659709901377

theorem tailTrace_447466 : CollatzResearch.WordTrace tailWord_447466 prefixEnd_447466 68078558383659709901377 := by
  unfold tailWord_447466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080106449228644488428563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10880283864609718635809501 4080106449228644488428563)
  ·
    refine ⟨6120159673842966732642845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4080106449228644488428563 6120159673842966732642845)
    ·
      refine ⟨2295059877691112524741067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6120159673842966732642845 2295059877691112524741067)
      ·
        refine ⟨3442589816536668787111601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295059877691112524741067 3442589816536668787111601)
        ·
          refine ⟨2581942362402501590333701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442589816536668787111601 2581942362402501590333701)
          ·
            refine ⟨484114192950469048187569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2581942362402501590333701 484114192950469048187569)
            ·
              refine ⟨363085644712851786140677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484114192950469048187569 363085644712851786140677)
              ·
                refine ⟨68078558383659709901377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363085644712851786140677 68078558383659709901377)
                ·
                  rfl

theorem cell20_447466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_447466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447466 prefixEnd_447466 := by exact prefixLift 447466
  have htrace : WordTrace (prefixWord ++ tailWord_447466) baseStart_447466 baseEnd_447466 := by
    simpa [prefixWord, tailWord_447466, baseEnd_447466] using wordTrace_append hprefix tailTrace_447466
  have hstable : (prefixWord ++ tailWord_447466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447466).length < 2 ^ (prefixWord ++ tailWord_447466).sum := by decide
  have hdescent : baseEnd_447466 < baseStart_447466 := by decide
  rcases family_descends (prefixWord ++ tailWord_447466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447511 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 3]
def baseStart_447511 : Nat := 118140960795 + 447511 * 2 ^ 59
def prefixEnd_447511 : Nat := 4983230072969 + 3 ^ 40 * 447511 * 2
def baseEnd_447511 : Nat := 204256214377158973203947

theorem tailTrace_447511 : CollatzResearch.WordTrace tailWord_447511 prefixEnd_447511 204256214377158973203947 := by
  unfold tailWord_447511
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322067081751550639102387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10881378054501033759401591 16322067081751550639102387)
  ·
    refine ⟨24483100622627325958653581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16322067081751550639102387 24483100622627325958653581)
    ·
      refine ⟨9181162733485247234495093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24483100622627325958653581 9181162733485247234495093)
      ·
        refine ⟨860734006264241928233915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9181162733485247234495093 860734006264241928233915)
        ·
          refine ⟨1291101009396362892350873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860734006264241928233915 1291101009396362892350873)
          ·
            refine ⟨968325757047272169263155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291101009396362892350873 968325757047272169263155)
            ·
              refine ⟨1452488635570908253894733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968325757047272169263155 1452488635570908253894733)
              ·
                refine ⟨544683238339090595210525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1452488635570908253894733 544683238339090595210525)
                ·
                  refine ⟨204256214377158973203947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544683238339090595210525 204256214377158973203947)
                  ·
                    rfl

theorem cell20_447511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_447511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447511 prefixEnd_447511 := by exact prefixLift 447511
  have htrace : WordTrace (prefixWord ++ tailWord_447511) baseStart_447511 baseEnd_447511 := by
    simpa [prefixWord, tailWord_447511, baseEnd_447511] using wordTrace_append hprefix tailTrace_447511
  have hstable : (prefixWord ++ tailWord_447511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447511).length < 2 ^ (prefixWord ++ tailWord_447511).sum := by decide
  have hdescent : baseEnd_447511 < baseStart_447511 := by decide
  rcases family_descends (prefixWord ++ tailWord_447511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447549 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 3]
def baseStart_447549 : Nat := 118140960795 + 447549 * 2 ^ 59
def prefixEnd_447549 : Nat := 4983230072969 + 3 ^ 40 * 447549 * 2
def baseEnd_447549 : Nat := 204273558612599729937125

theorem tailTrace_447549 : CollatzResearch.WordTrace tailWord_447549 prefixEnd_447549 204273558612599729937125 := by
  unfold tailWord_447549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323453055613883128985701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10882302037075922085990467 16323453055613883128985701)
  ·
    refine ⟨3060647447927603086684819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16323453055613883128985701 3060647447927603086684819)
    ·
      refine ⟨4590971171891404630027229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060647447927603086684819 4590971171891404630027229)
      ·
        refine ⟨1721614189459276736260211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4590971171891404630027229 1721614189459276736260211)
        ·
          refine ⟨2582421284188915104390317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721614189459276736260211 2582421284188915104390317)
          ·
            refine ⟨968407981570843164146369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2582421284188915104390317 968407981570843164146369)
            ·
              refine ⟨726305986178132373109777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968407981570843164146369 726305986178132373109777)
              ·
                refine ⟨544729489633599279832333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726305986178132373109777 544729489633599279832333)
                ·
                  refine ⟨204273558612599729937125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544729489633599279832333 204273558612599729937125)
                  ·
                    rfl

theorem cell20_447549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_447549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447549 prefixEnd_447549 := by exact prefixLift 447549
  have htrace : WordTrace (prefixWord ++ tailWord_447549) baseStart_447549 baseEnd_447549 := by
    simpa [prefixWord, tailWord_447549, baseEnd_447549] using wordTrace_append hprefix tailTrace_447549
  have hstable : (prefixWord ++ tailWord_447549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447549).length < 2 ^ (prefixWord ++ tailWord_447549).sum := by decide
  have hdescent : baseEnd_447549 < baseStart_447549 := by decide
  rcases family_descends (prefixWord ++ tailWord_447549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447608 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_447608 : Nat := 118140960795 + 447608 * 2 ^ 59
def prefixEnd_447608 : Nat := 4983230072969 + 3 ^ 40 * 447608 * 2
def baseEnd_447608 : Nat := 204300487820257746970217

theorem tailTrace_447608 : CollatzResearch.WordTrace tailWord_447608 prefixEnd_447608 204300487820257746970217 := by
  unfold tailWord_447608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162802481200068102691739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10883736641600090803588985 8162802481200068102691739)
  ·
    refine ⟨12244203721800102154037609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8162802481200068102691739 12244203721800102154037609)
    ·
      refine ⟨9183152791350076615528207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12244203721800102154037609 9183152791350076615528207)
      ·
        refine ⟨13774729187025114923292311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9183152791350076615528207 13774729187025114923292311)
        ·
          refine ⟨20662093780537672384938467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13774729187025114923292311 20662093780537672384938467)
          ·
            refine ⟨30993140670806508577407701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20662093780537672384938467 30993140670806508577407701)
            ·
              refine ⟨726401734472027544782993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30993140670806508577407701 726401734472027544782993)
              ·
                refine ⟨544801300854020658587245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726401734472027544782993 544801300854020658587245)
                ·
                  refine ⟨204300487820257746970217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544801300854020658587245 204300487820257746970217)
                  ·
                    rfl

theorem cell20_447608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_447608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447608 prefixEnd_447608 := by exact prefixLift 447608
  have htrace : WordTrace (prefixWord ++ tailWord_447608) baseStart_447608 baseEnd_447608 := by
    simpa [prefixWord, tailWord_447608, baseEnd_447608] using wordTrace_append hprefix tailTrace_447608
  have hstable : (prefixWord ++ tailWord_447608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447608).length < 2 ^ (prefixWord ++ tailWord_447608).sum := by decide
  have hdescent : baseEnd_447608 < baseStart_447608 := by decide
  rcases family_descends (prefixWord ++ tailWord_447608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447625 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 3]
def baseStart_447625 : Nat := 118140960795 + 447625 * 2 ^ 59
def prefixEnd_447625 : Nat := 4983230072969 + 3 ^ 40 * 447625 * 2
def baseEnd_447625 : Nat := 204308247083481243403481

theorem tailTrace_447625 : CollatzResearch.WordTrace tailWord_447625 prefixEnd_447625 204308247083481243403481 := by
  unfold tailWord_447625
  simp only [CollatzResearch.WordTrace]
  refine ⟨16326225003338548108752329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10884150002225698739168219 16326225003338548108752329)
  ·
    refine ⟨12244668752503911081564247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16326225003338548108752329 12244668752503911081564247)
    ·
      refine ⟨18367003128755866622346371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12244668752503911081564247 18367003128755866622346371)
      ·
        refine ⟨27550504693133799933519557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18367003128755866622346371 27550504693133799933519557)
        ·
          refine ⟨5165719629962587487534917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27550504693133799933519557 5165719629962587487534917)
          ·
            refine ⟨968572430617985153912797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5165719629962587487534917 968572430617985153912797)
            ·
              refine ⟨363214661481744432717299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 968572430617985153912797 363214661481744432717299)
              ·
                refine ⟨544821992222616649075949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363214661481744432717299 544821992222616649075949)
                ·
                  refine ⟨204308247083481243403481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544821992222616649075949 204308247083481243403481)
                  ·
                    rfl

theorem cell20_447625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_447625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447625 prefixEnd_447625 := by exact prefixLift 447625
  have htrace : WordTrace (prefixWord ++ tailWord_447625) baseStart_447625 baseEnd_447625 := by
    simpa [prefixWord, tailWord_447625, baseEnd_447625] using wordTrace_append hprefix tailTrace_447625
  have hstable : (prefixWord ++ tailWord_447625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447625).length < 2 ^ (prefixWord ++ tailWord_447625).sum := by decide
  have hdescent : baseEnd_447625 < baseStart_447625 := by decide
  rcases family_descends (prefixWord ++ tailWord_447625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447639 : List Nat := [1, 1, 3, 3, 3, 1, 4, 4]
def baseStart_447639 : Nat := 118140960795 + 447639 * 2 ^ 59
def prefixEnd_447639 : Nat := 4983230072969 + 3 ^ 40 * 447639 * 2
def baseEnd_447639 : Nat := 68104879021653138978919

theorem tailTrace_447639 : CollatzResearch.WordTrace tailWord_447639 prefixEnd_447639 68104879021653138978919 := by
  unfold tailWord_447639
  simp only [CollatzResearch.WordTrace]
  refine ⟨16326735625287828499761971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10884490416858552333174647 16326735625287828499761971)
  ·
    refine ⟨24490103437931742749642957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16326735625287828499761971 24490103437931742749642957)
    ·
      refine ⟨9183788789224403531116109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24490103437931742749642957 9183788789224403531116109)
      ·
        refine ⟨3443920795959151324168541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9183788789224403531116109 3443920795959151324168541)
        ·
          refine ⟨1291470298484681746563203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3443920795959151324168541 1291470298484681746563203)
          ·
            refine ⟨1937205447727022619844805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291470298484681746563203 1937205447727022619844805)
            ·
              refine ⟨363226021448816741220901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1937205447727022619844805 363226021448816741220901)
              ·
                refine ⟨68104879021653138978919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363226021448816741220901 68104879021653138978919)
                ·
                  rfl

theorem cell20_447639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_447639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447639 prefixEnd_447639 := by exact prefixLift 447639
  have htrace : WordTrace (prefixWord ++ tailWord_447639) baseStart_447639 baseEnd_447639 := by
    simpa [prefixWord, tailWord_447639, baseEnd_447639] using wordTrace_append hprefix tailTrace_447639
  have hstable : (prefixWord ++ tailWord_447639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447639).length < 2 ^ (prefixWord ++ tailWord_447639).sum := by decide
  have hdescent : baseEnd_447639 < baseStart_447639 := by decide
  rcases family_descends (prefixWord ++ tailWord_447639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447667 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_447667 : Nat := 118140960795 + 447667 * 2 ^ 59
def prefixEnd_447667 : Nat := 4983230072969 + 3 ^ 40 * 447667 * 2
def baseEnd_447667 : Nat := 204327417027915764003309

theorem tailTrace_447667 : CollatzResearch.WordTrace tailWord_447667 prefixEnd_447667 204327417027915764003309 := by
  unfold tailWord_447667
  simp only [CollatzResearch.WordTrace]
  refine ⟨16327756869186389281781255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10885171246124259521187503 16327756869186389281781255)
  ·
    refine ⟨24491635303779583922671883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16327756869186389281781255 24491635303779583922671883)
    ·
      refine ⟨36737452955669375884007825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24491635303779583922671883 36737452955669375884007825)
      ·
        refine ⟨27553089716752031913005869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36737452955669375884007825 27553089716752031913005869)
        ·
          refine ⟨10332408643782011967377201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27553089716752031913005869 10332408643782011967377201)
          ·
            refine ⟨7749306482836508975532901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10332408643782011967377201 7749306482836508975532901)
            ·
              refine ⟨1452994965531845432912419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7749306482836508975532901 1452994965531845432912419)
              ·
                refine ⟨2179492448297768149368629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452994965531845432912419 2179492448297768149368629)
                ·
                  refine ⟨204327417027915764003309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2179492448297768149368629 204327417027915764003309)
                  ·
                    rfl

theorem cell20_447667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_447667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447667 prefixEnd_447667 := by exact prefixLift 447667
  have htrace : WordTrace (prefixWord ++ tailWord_447667) baseStart_447667 baseEnd_447667 := by
    simpa [prefixWord, tailWord_447667, baseEnd_447667] using wordTrace_append hprefix tailTrace_447667
  have hstable : (prefixWord ++ tailWord_447667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447667).length < 2 ^ (prefixWord ++ tailWord_447667).sum := by decide
  have hdescent : baseEnd_447667 < baseStart_447667 := by decide
  rcases family_descends (prefixWord ++ tailWord_447667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447680 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_447680 : Nat := 118140960795 + 447680 * 2 ^ 59
def prefixEnd_447680 : Nat := 4983230072969 + 3 ^ 40 * 447680 * 2
def baseEnd_447680 : Nat := 204333350582145496569923

theorem tailTrace_447680 : CollatzResearch.WordTrace tailWord_447680 prefixEnd_447680 204333350582145496569923 := by
  unfold tailWord_447680
  simp only [CollatzResearch.WordTrace]
  refine ⟨8164115509069646251002247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10885487345426195001336329 8164115509069646251002247)
  ·
    refine ⟨12246173263604469376503371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8164115509069646251002247 12246173263604469376503371)
    ·
      refine ⟨18369259895406704064755057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12246173263604469376503371 18369259895406704064755057)
      ·
        refine ⟨13776944921555028048566293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18369259895406704064755057 13776944921555028048566293)
        ·
          refine ⟨645794293197891939776545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13776944921555028048566293 645794293197891939776545)
          ·
            refine ⟨484345719898418954832409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645794293197891939776545 484345719898418954832409)
            ·
              refine ⟨363259289923814216124307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484345719898418954832409 363259289923814216124307)
              ·
                refine ⟨544888934885721324186461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363259289923814216124307 544888934885721324186461)
                ·
                  refine ⟨204333350582145496569923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544888934885721324186461 204333350582145496569923)
                  ·
                    rfl

theorem cell20_447680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_447680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447680 prefixEnd_447680 := by exact prefixLift 447680
  have htrace : WordTrace (prefixWord ++ tailWord_447680) baseStart_447680 baseEnd_447680 := by
    simpa [prefixWord, tailWord_447680, baseEnd_447680] using wordTrace_append hprefix tailTrace_447680
  have hstable : (prefixWord ++ tailWord_447680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447680).length < 2 ^ (prefixWord ++ tailWord_447680).sum := by decide
  have hdescent : baseEnd_447680 < baseStart_447680 := by decide
  rcases family_descends (prefixWord ++ tailWord_447680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447698 : List Nat := [3, 2, 2, 2, 1, 1, 1, 8]
def baseStart_447698 : Nat := 118140960795 + 447698 * 2 ^ 59
def prefixEnd_447698 : Nat := 4983230072969 + 3 ^ 40 * 447698 * 2
def baseEnd_447698 : Nat := 68113855424205811323283

theorem tailTrace_447698 : CollatzResearch.WordTrace tailWord_447698 prefixEnd_447698 68113855424205811323283 := by
  unfold tailWord_447698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082221883018520394039937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10885925021382721050773165 4082221883018520394039937)
  ·
    refine ⟨3061666412263890295529953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4082221883018520394039937 3061666412263890295529953)
    ·
      refine ⟨2296249809197917721647465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3061666412263890295529953 2296249809197917721647465)
      ·
        refine ⟨1722187356898438291235599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2296249809197917721647465 1722187356898438291235599)
        ·
          refine ⟨2583281035347657436853399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722187356898438291235599 2583281035347657436853399)
          ·
            refine ⟨3874921553021486155280099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583281035347657436853399 3874921553021486155280099)
            ·
              refine ⟨5812382329532229232920149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874921553021486155280099 5812382329532229232920149)
              ·
                refine ⟨68113855424205811323283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5812382329532229232920149 68113855424205811323283)
                ·
                  rfl

theorem cell20_447698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_447698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447698 prefixEnd_447698 := by exact prefixLift 447698
  have htrace : WordTrace (prefixWord ++ tailWord_447698) baseStart_447698 baseEnd_447698 := by
    simpa [prefixWord, tailWord_447698, baseEnd_447698] using wordTrace_append hprefix tailTrace_447698
  have hstable : (prefixWord ++ tailWord_447698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447698).length < 2 ^ (prefixWord ++ tailWord_447698).sum := by decide
  have hdescent : baseEnd_447698 < baseStart_447698 := by decide
  rcases family_descends (prefixWord ++ tailWord_447698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447722 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_447722 : Nat := 118140960795 + 447722 * 2 ^ 59
def prefixEnd_447722 : Nat := 4983230072969 + 3 ^ 40 * 447722 * 2
def baseEnd_447722 : Nat := 204352520526580017169751

theorem tailTrace_447722 : CollatzResearch.WordTrace tailWord_447722 prefixEnd_447722 204352520526580017169751 := by
  unfold tailWord_447722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082440720996783418758355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10886508589324755783355613 4082440720996783418758355)
  ·
    refine ⟨6123661081495175128137533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082440720996783418758355 6123661081495175128137533)
    ·
      refine ⟨2296372905560690673051575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6123661081495175128137533 2296372905560690673051575)
      ·
        refine ⟨3444559358341036009577363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296372905560690673051575 3444559358341036009577363)
        ·
          refine ⟨5166839037511554014366045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444559358341036009577363 5166839037511554014366045)
          ·
            refine ⟨1937564639066832755387267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5166839037511554014366045 1937564639066832755387267)
            ·
              refine ⟨2906346958600249133080901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937564639066832755387267 2906346958600249133080901)
              ·
                refine ⟨544940054737546712452669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2906346958600249133080901 544940054737546712452669)
                ·
                  refine ⟨204352520526580017169751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544940054737546712452669 204352520526580017169751)
                  ·
                    rfl

theorem cell20_447722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_447722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447722 prefixEnd_447722 := by exact prefixLift 447722
  have htrace : WordTrace (prefixWord ++ tailWord_447722) baseStart_447722 baseEnd_447722 := by
    simpa [prefixWord, tailWord_447722, baseEnd_447722] using wordTrace_append hprefix tailTrace_447722
  have hstable : (prefixWord ++ tailWord_447722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447722).length < 2 ^ (prefixWord ++ tailWord_447722).sum := by decide
  have hdescent : baseEnd_447722 < baseStart_447722 := by decide
  rcases family_descends (prefixWord ++ tailWord_447722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447725 : List Nat := [1, 5, 1, 2, 2, 2, 1, 4, 2]
def baseStart_447725 : Nat := 118140960795 + 447725 * 2 ^ 59
def prefixEnd_447725 : Nat := 4983230072969 + 3 ^ 40 * 447725 * 2
def baseEnd_447725 : Nat := 204353889808325340069739

theorem tailTrace_447725 : CollatzResearch.WordTrace tailWord_447725 prefixEnd_447725 204353889808325340069739 := by
  unfold tailWord_447725
  simp only [CollatzResearch.WordTrace]
  refine ⟨16329872302976265187392629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10886581535317510124928419 16329872302976265187392629)
  ·
    refine ⟨1530925528404024861318059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16329872302976265187392629 1530925528404024861318059)
    ·
      refine ⟨2296388292606037291977089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530925528404024861318059 2296388292606037291977089)
      ·
        refine ⟨1722291219454527968982817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2296388292606037291977089 1722291219454527968982817)
        ·
          refine ⟨1291718414590895976737113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1722291219454527968982817 1291718414590895976737113)
          ·
            refine ⟨968788810943171982552835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291718414590895976737113 968788810943171982552835)
            ·
              refine ⟨1453183216414757973829253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968788810943171982552835 1453183216414757973829253)
              ·
                refine ⟨272471853077767120092985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1453183216414757973829253 272471853077767120092985)
                ·
                  refine ⟨204353889808325340069739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272471853077767120092985 204353889808325340069739)
                  ·
                    rfl

theorem cell20_447725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_447725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447725 prefixEnd_447725 := by exact prefixLift 447725
  have htrace : WordTrace (prefixWord ++ tailWord_447725) baseStart_447725 baseEnd_447725 := by
    simpa [prefixWord, tailWord_447725, baseEnd_447725] using wordTrace_append hprefix tailTrace_447725
  have hstable : (prefixWord ++ tailWord_447725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447725).length < 2 ^ (prefixWord ++ tailWord_447725).sum := by decide
  have hdescent : baseEnd_447725 < baseStart_447725 := by decide
  rcases family_descends (prefixWord ++ tailWord_447725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447784 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_447784 : Nat := 118140960795 + 447784 * 2 ^ 59
def prefixEnd_447784 : Nat := 4983230072969 + 3 ^ 40 * 447784 * 2
def baseEnd_447784 : Nat := 204380819015983357102831

theorem tailTrace_447784 : CollatzResearch.WordTrace tailWord_447784 prefixEnd_447784 204380819015983357102831 := by
  unfold tailWord_447784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166012104881259131895203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10888016139841678842526937 8166012104881259131895203)
  ·
    refine ⟨12249018157321888697842805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8166012104881259131895203 12249018157321888697842805)
    ·
      refine ⟨1148345452248927065422763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12249018157321888697842805 1148345452248927065422763)
      ·
        refine ⟨1722518178373390598134145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148345452248927065422763 1722518178373390598134145)
        ·
          refine ⟨1291888633780042948600609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1722518178373390598134145 1291888633780042948600609)
          ·
            refine ⟨968916475335032211450457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291888633780042948600609 968916475335032211450457)
            ·
              refine ⟨726687356501274158587843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968916475335032211450457 726687356501274158587843)
              ·
                refine ⟨1090031034751911237881765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726687356501274158587843 1090031034751911237881765)
                ·
                  refine ⟨204380819015983357102831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090031034751911237881765 204380819015983357102831)
                  ·
                    rfl

theorem cell20_447784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_447784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447784 prefixEnd_447784 := by exact prefixLift 447784
  have htrace : WordTrace (prefixWord ++ tailWord_447784) baseStart_447784 baseEnd_447784 := by
    simpa [prefixWord, tailWord_447784, baseEnd_447784] using wordTrace_append hprefix tailTrace_447784
  have hstable : (prefixWord ++ tailWord_447784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447784).length < 2 ^ (prefixWord ++ tailWord_447784).sum := by decide
  have hdescent : baseEnd_447784 < baseStart_447784 := by decide
  rcases family_descends (prefixWord ++ tailWord_447784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447814 : List Nat := [6, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_447814 : Nat := 118140960795 + 447814 * 2 ^ 59
def prefixEnd_447814 : Nat := 4983230072969 + 3 ^ 40 * 447814 * 2
def baseEnd_447814 : Nat := 204394511833436586102709

theorem tailTrace_447814 : CollatzResearch.WordTrace tailWord_447814 prefixEnd_447814 204394511833436586102709 := by
  unfold tailWord_447814
  simp only [CollatzResearch.WordTrace]
  refine ⟨510409949989182293355703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10888745599769222258254997 510409949989182293355703)
  ·
    refine ⟨765614924983773440033555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 510409949989182293355703 765614924983773440033555)
    ·
      refine ⟨1148422387475660160050333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765614924983773440033555 1148422387475660160050333)
      ·
        refine ⟨430658395303372560018875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1148422387475660160050333 430658395303372560018875)
        ·
          refine ⟨645987592955058840028313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430658395303372560018875 645987592955058840028313)
          ·
            refine ⟨484490694716294130021235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645987592955058840028313 484490694716294130021235)
            ·
              refine ⟨726736042074441195031853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484490694716294130021235 726736042074441195031853)
              ·
                refine ⟨272526015777915448136945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726736042074441195031853 272526015777915448136945)
                ·
                  refine ⟨204394511833436586102709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272526015777915448136945 204394511833436586102709)
                  ·
                    rfl

theorem cell20_447814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_447814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447814 prefixEnd_447814 := by exact prefixLift 447814
  have htrace : WordTrace (prefixWord ++ tailWord_447814) baseStart_447814 baseEnd_447814 := by
    simpa [prefixWord, tailWord_447814, baseEnd_447814] using wordTrace_append hprefix tailTrace_447814
  have hstable : (prefixWord ++ tailWord_447814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447814).length < 2 ^ (prefixWord ++ tailWord_447814).sum := by decide
  have hdescent : baseEnd_447814 < baseStart_447814 := by decide
  rcases family_descends (prefixWord ++ tailWord_447814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447833 : List Nat := [1, 2, 1, 2, 2, 2, 10]
def baseStart_447833 : Nat := 118140960795 + 447833 * 2 ^ 59
def prefixEnd_447833 : Nat := 4983230072969 + 3 ^ 40 * 447833 * 2
def baseEnd_447833 : Nat := 22711464883461884941033

theorem tailTrace_447833 : CollatzResearch.WordTrace tailWord_447833 prefixEnd_447833 22711464883461884941033 := by
  unfold tailWord_447833
  simp only [CollatzResearch.WordTrace]
  refine ⟨16333811386584999632324153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10889207591056666421549435 16333811386584999632324153)
  ·
    refine ⟨12250358539938749724243115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16333811386584999632324153 12250358539938749724243115)
    ·
      refine ⟨18375537809908124586364673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12250358539938749724243115 18375537809908124586364673)
      ·
        refine ⟨13781653357431093439773505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18375537809908124586364673 13781653357431093439773505)
        ·
          refine ⟨10336240018073320079830129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13781653357431093439773505 10336240018073320079830129)
          ·
            refine ⟨7752180013554990059872597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10336240018073320079830129 7752180013554990059872597)
            ·
              refine ⟨22711464883461884941033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7752180013554990059872597 22711464883461884941033)
              ·
                rfl

theorem cell20_447833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_447833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447833 prefixEnd_447833 := by exact prefixLift 447833
  have htrace : WordTrace (prefixWord ++ tailWord_447833) baseStart_447833 baseEnd_447833 := by
    simpa [prefixWord, tailWord_447833, baseEnd_447833] using wordTrace_append hprefix tailTrace_447833
  have hstable : (prefixWord ++ tailWord_447833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447833).length < 2 ^ (prefixWord ++ tailWord_447833).sum := by decide
  have hdescent : baseEnd_447833 < baseStart_447833 := by decide
  rcases family_descends (prefixWord ++ tailWord_447833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447843 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_447843 : Nat := 118140960795 + 447843 * 2 ^ 59
def prefixEnd_447843 : Nat := 4983230072969 + 3 ^ 40 * 447843 * 2
def baseEnd_447843 : Nat := 204407748223641374135923

theorem tailTrace_447843 : CollatzResearch.WordTrace tailWord_447843 prefixEnd_447843 204407748223641374135923 := by
  unfold tailWord_447843
  simp only [CollatzResearch.WordTrace]
  refine ⟨16334176116548771340188183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10889450744365847560125455 16334176116548771340188183)
  ·
    refine ⟨24501264174823157010282275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16334176116548771340188183 24501264174823157010282275)
    ·
      refine ⟨36751896262234735515423413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24501264174823157010282275 36751896262234735515423413)
      ·
        refine ⟨3445490274584506454570945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36751896262234735515423413 3445490274584506454570945)
        ·
          refine ⟨2584117705938379840928209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3445490274584506454570945 2584117705938379840928209)
          ·
            refine ⟨1938088279453784880696157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584117705938379840928209 1938088279453784880696157)
            ·
              refine ⟨726783104795169330261059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1938088279453784880696157 726783104795169330261059)
              ·
                refine ⟨1090174657192753995391589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726783104795169330261059 1090174657192753995391589)
                ·
                  refine ⟨204407748223641374135923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090174657192753995391589 204407748223641374135923)
                  ·
                    rfl

theorem cell20_447843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_447843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447843 prefixEnd_447843 := by exact prefixLift 447843
  have htrace : WordTrace (prefixWord ++ tailWord_447843) baseStart_447843 baseEnd_447843 := by
    simpa [prefixWord, tailWord_447843, baseEnd_447843] using wordTrace_append hprefix tailTrace_447843
  have hstable : (prefixWord ++ tailWord_447843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447843).length < 2 ^ (prefixWord ++ tailWord_447843).sum := by decide
  have hdescent : baseEnd_447843 < baseStart_447843 := by decide
  rcases family_descends (prefixWord ++ tailWord_447843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447853 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 3]
def baseStart_447853 : Nat := 118140960795 + 447853 * 2 ^ 59
def prefixEnd_447853 : Nat := 4983230072969 + 3 ^ 40 * 447853 * 2
def baseEnd_447853 : Nat := 204412312496125783802549

theorem tailTrace_447853 : CollatzResearch.WordTrace tailWord_447853 prefixEnd_447853 204412312496125783802549 := by
  unfold tailWord_447853
  simp only [CollatzResearch.WordTrace]
  refine ⟨16334540846512543048052213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10889693897675028698701475 16334540846512543048052213)
  ·
    refine ⟨1531363204360550910754895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16334540846512543048052213 1531363204360550910754895)
    ·
      refine ⟨2297044806540826366132343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531363204360550910754895 2297044806540826366132343)
      ·
        refine ⟨3445567209811239549198515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297044806540826366132343 3445567209811239549198515)
        ·
          refine ⟨5168350814716859323797773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445567209811239549198515 5168350814716859323797773)
          ·
            refine ⟨1938131555518822246424165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5168350814716859323797773 1938131555518822246424165)
            ·
              refine ⟨363399666659779171204531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1938131555518822246424165 363399666659779171204531)
              ·
                refine ⟨545099499989668756806797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363399666659779171204531 545099499989668756806797)
                ·
                  refine ⟨204412312496125783802549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545099499989668756806797 204412312496125783802549)
                  ·
                    rfl

theorem cell20_447853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_447853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447853 prefixEnd_447853 := by exact prefixLift 447853
  have htrace : WordTrace (prefixWord ++ tailWord_447853) baseStart_447853 baseEnd_447853 := by
    simpa [prefixWord, tailWord_447853, baseEnd_447853] using wordTrace_append hprefix tailTrace_447853
  have hstable : (prefixWord ++ tailWord_447853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447853).length < 2 ^ (prefixWord ++ tailWord_447853).sum := by decide
  have hdescent : baseEnd_447853 < baseStart_447853 := by decide
  rcases family_descends (prefixWord ++ tailWord_447853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447890 : List Nat := [3, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_447890 : Nat := 118140960795 + 447890 * 2 ^ 59
def prefixEnd_447890 : Nat := 4983230072969 + 3 ^ 40 * 447890 * 2
def baseEnd_447890 : Nat := 204429200304318099569065

theorem tailTrace_447890 : CollatzResearch.WordTrace tailWord_447890 prefixEnd_447890 204429200304318099569065 := by
  unfold tailWord_447890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083972586844624591787281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10890593564918998911432749 4083972586844624591787281)
  ·
    refine ⟨3062979440133468443840461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4083972586844624591787281 3062979440133468443840461)
    ·
      refine ⟨1148617290050050666440173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3062979440133468443840461 1148617290050050666440173)
      ·
        refine ⟨430731483768768999915065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1148617290050050666440173 430731483768768999915065)
        ·
          refine ⟨323048612826576749936299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430731483768768999915065 323048612826576749936299)
          ·
            refine ⟨484572919239865124904449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323048612826576749936299 484572919239865124904449)
            ·
              refine ⟨363429689429898843678337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484572919239865124904449 363429689429898843678337)
              ·
                refine ⟨272572267072424132758753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363429689429898843678337 272572267072424132758753)
                ·
                  refine ⟨204429200304318099569065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272572267072424132758753 204429200304318099569065)
                  ·
                    rfl

theorem cell20_447890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_447890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447890 prefixEnd_447890 := by exact prefixLift 447890
  have htrace : WordTrace (prefixWord ++ tailWord_447890) baseStart_447890 baseEnd_447890 := by
    simpa [prefixWord, tailWord_447890, baseEnd_447890] using wordTrace_append hprefix tailTrace_447890
  have hstable : (prefixWord ++ tailWord_447890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447890).length < 2 ^ (prefixWord ++ tailWord_447890).sum := by decide
  have hdescent : baseEnd_447890 < baseStart_447890 := by decide
  rcases family_descends (prefixWord ++ tailWord_447890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447898 : List Nat := [3, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_447898 : Nat := 118140960795 + 447898 * 2 ^ 59
def prefixEnd_447898 : Nat := 4983230072969 + 3 ^ 40 * 447898 * 2
def baseEnd_447898 : Nat := 204432851722305627302365

theorem tailTrace_447898 : CollatzResearch.WordTrace tailWord_447898 prefixEnd_447898 204432851722305627302365 := by
  unfold tailWord_447898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084045532837378933360087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10890788087566343822293565 4084045532837378933360087)
  ·
    refine ⟨6126068299256068400040131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084045532837378933360087 6126068299256068400040131)
    ·
      refine ⟨9189102448884102600060197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6126068299256068400040131 9189102448884102600060197)
      ·
        refine ⟨1722956709165769237511287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9189102448884102600060197 1722956709165769237511287)
        ·
          refine ⟨2584435063748653856266931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722956709165769237511287 2584435063748653856266931)
          ·
            refine ⟨3876652595622980784400397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584435063748653856266931 3876652595622980784400397)
            ·
              refine ⟨1453744723358617794150149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3876652595622980784400397 1453744723358617794150149)
              ·
                refine ⟨272577135629740836403153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1453744723358617794150149 272577135629740836403153)
                ·
                  refine ⟨204432851722305627302365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272577135629740836403153 204432851722305627302365)
                  ·
                    rfl

theorem cell20_447898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_447898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447898 prefixEnd_447898 := by exact prefixLift 447898
  have htrace : WordTrace (prefixWord ++ tailWord_447898) baseStart_447898 baseEnd_447898 := by
    simpa [prefixWord, tailWord_447898, baseEnd_447898] using wordTrace_append hprefix tailTrace_447898
  have hstable : (prefixWord ++ tailWord_447898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447898).length < 2 ^ (prefixWord ++ tailWord_447898).sum := by decide
  have hdescent : baseEnd_447898 < baseStart_447898 := by decide
  rcases family_descends (prefixWord ++ tailWord_447898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447909 : List Nat := [1, 3, 1, 2, 1, 1, 2, 9]
def baseStart_447909 : Nat := 118140960795 + 447909 * 2 ^ 59
def prefixEnd_447909 : Nat := 4983230072969 + 3 ^ 40 * 447909 * 2
def baseEnd_447909 : Nat := 68145957474012825978551

theorem tailTrace_447909 : CollatzResearch.WordTrace tailWord_447909 prefixEnd_447909 68145957474012825978551 := by
  unfold tailWord_447909
  simp only [CollatzResearch.WordTrace]
  refine ⟨16336583334309664612090781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10891055556206443074727187 16336583334309664612090781)
  ·
    refine ⟨6126218750366124229534043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16336583334309664612090781 6126218750366124229534043)
    ·
      refine ⟨9189328125549186344301065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6126218750366124229534043 9189328125549186344301065)
      ·
        refine ⟨6891996094161889758225799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9189328125549186344301065 6891996094161889758225799)
        ·
          refine ⟨10337994141242834637338699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891996094161889758225799 10337994141242834637338699)
          ·
            refine ⟨15506991211864251956008049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337994141242834637338699 15506991211864251956008049)
            ·
              refine ⟨11630243408898188967006037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15506991211864251956008049 11630243408898188967006037)
              ·
                refine ⟨68145957474012825978551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11630243408898188967006037 68145957474012825978551)
                ·
                  rfl

theorem cell20_447909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_447909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447909 prefixEnd_447909 := by exact prefixLift 447909
  have htrace : WordTrace (prefixWord ++ tailWord_447909) baseStart_447909 baseEnd_447909 := by
    simpa [prefixWord, tailWord_447909, baseEnd_447909] using wordTrace_append hprefix tailTrace_447909
  have hstable : (prefixWord ++ tailWord_447909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447909).length < 2 ^ (prefixWord ++ tailWord_447909).sum := by decide
  have hdescent : baseEnd_447909 < baseStart_447909 := by decide
  rcases family_descends (prefixWord ++ tailWord_447909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447933 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_447933 : Nat := 118140960795 + 447933 * 2 ^ 59
def prefixEnd_447933 : Nat := 4983230072969 + 3 ^ 40 * 447933 * 2
def baseEnd_447933 : Nat := 204448826676001061135555

theorem tailTrace_447933 : CollatzResearch.WordTrace tailWord_447933 prefixEnd_447933 204448826676001061135555 := by
  unfold tailWord_447933
  simp only [CollatzResearch.WordTrace]
  refine ⟨16337458686222716710964453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10891639124148477807309635 16337458686222716710964453)
  ·
    refine ⟨3063273503666759383305835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16337458686222716710964453 3063273503666759383305835)
    ·
      refine ⟨4594910255500139074958753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063273503666759383305835 4594910255500139074958753)
      ·
        refine ⟨3446182691625104306219065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4594910255500139074958753 3446182691625104306219065)
        ·
          refine ⟨2584637018718828229664299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3446182691625104306219065 2584637018718828229664299)
          ·
            refine ⟨3876955528078242344496449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584637018718828229664299 3876955528078242344496449)
            ·
              refine ⟨2907716646058681758372337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3876955528078242344496449 2907716646058681758372337)
              ·
                refine ⟨2180787484544011318779253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907716646058681758372337 2180787484544011318779253)
                ·
                  refine ⟨204448826676001061135555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2180787484544011318779253 204448826676001061135555)
                  ·
                    rfl

theorem cell20_447933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_447933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447933 prefixEnd_447933 := by exact prefixLift 447933
  have htrace : WordTrace (prefixWord ++ tailWord_447933) baseStart_447933 baseEnd_447933 := by
    simpa [prefixWord, tailWord_447933, baseEnd_447933] using wordTrace_append hprefix tailTrace_447933
  have hstable : (prefixWord ++ tailWord_447933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447933).length < 2 ^ (prefixWord ++ tailWord_447933).sum := by decide
  have hdescent : baseEnd_447933 < baseStart_447933 := by decide
  rcases family_descends (prefixWord ++ tailWord_447933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447950 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_447950 : Nat := 118140960795 + 447950 * 2 ^ 59
def prefixEnd_447950 : Nat := 4983230072969 + 3 ^ 40 * 447950 * 2
def baseEnd_447950 : Nat := 204456585939224557568819

theorem tailTrace_447950 : CollatzResearch.WordTrace tailWord_447950 prefixEnd_447950 204456585939224557568819 := by
  unfold tailWord_447950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042259840895141076791663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10892052484774085742888869 2042259840895141076791663)
  ·
    refine ⟨3063389761342711615187495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2042259840895141076791663 3063389761342711615187495)
    ·
      refine ⟨4595084642014067422781243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063389761342711615187495 4595084642014067422781243)
      ·
        refine ⟨6892626963021101134171865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595084642014067422781243 6892626963021101134171865)
        ·
          refine ⟨5169470222265825850628899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6892626963021101134171865 5169470222265825850628899)
          ·
            refine ⟨7754205333398738775943349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169470222265825850628899 7754205333398738775943349)
            ·
              refine ⟨726956750006131760244689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7754205333398738775943349 726956750006131760244689)
              ·
                refine ⟨545217562504598820183517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726956750006131760244689 545217562504598820183517)
                ·
                  refine ⟨204456585939224557568819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545217562504598820183517 204456585939224557568819)
                  ·
                    rfl

theorem cell20_447950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_447950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447950 prefixEnd_447950 := by exact prefixLift 447950
  have htrace : WordTrace (prefixWord ++ tailWord_447950) baseStart_447950 baseEnd_447950 := by
    simpa [prefixWord, tailWord_447950, baseEnd_447950] using wordTrace_append hprefix tailTrace_447950
  have hstable : (prefixWord ++ tailWord_447950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447950).length < 2 ^ (prefixWord ++ tailWord_447950).sum := by decide
  have hdescent : baseEnd_447950 < baseStart_447950 := by decide
  rcases family_descends (prefixWord ++ tailWord_447950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447957 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_447957 : Nat := 118140960795 + 447957 * 2 ^ 59
def prefixEnd_447957 : Nat := 4983230072969 + 3 ^ 40 * 447957 * 2
def baseEnd_447957 : Nat := 204459780929963644335457

theorem tailTrace_447957 : CollatzResearch.WordTrace tailWord_447957 prefixEnd_447957 204459780929963644335457 := by
  unfold tailWord_447957
  simp only [CollatzResearch.WordTrace]
  refine ⟨16338334038135768809838125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10892222692090512539892083 16338334038135768809838125)
  ·
    refine ⟨6126875264300913303689297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16338334038135768809838125 6126875264300913303689297)
    ·
      refine ⟨4595156448225684977766973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6126875264300913303689297 4595156448225684977766973)
      ·
        refine ⟨1723183668084631866662615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4595156448225684977766973 1723183668084631866662615)
        ·
          refine ⟨2584775502126947799993923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723183668084631866662615 2584775502126947799993923)
          ·
            refine ⟨3877163253190421699990885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584775502126947799993923 3877163253190421699990885)
            ·
              refine ⟨726968109973204068748291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3877163253190421699990885 726968109973204068748291)
              ·
                refine ⟨1090452164959806103122437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726968109973204068748291 1090452164959806103122437)
                ·
                  refine ⟨204459780929963644335457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090452164959806103122437 204459780929963644335457)
                  ·
                    rfl

theorem cell20_447957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_447957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447957 prefixEnd_447957 := by exact prefixLift 447957
  have htrace : WordTrace (prefixWord ++ tailWord_447957) baseStart_447957 baseEnd_447957 := by
    simpa [prefixWord, tailWord_447957, baseEnd_447957] using wordTrace_append hprefix tailTrace_447957
  have hstable : (prefixWord ++ tailWord_447957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447957).length < 2 ^ (prefixWord ++ tailWord_447957).sum := by decide
  have hdescent : baseEnd_447957 < baseStart_447957 := by decide
  rcases family_descends (prefixWord ++ tailWord_447957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447981 : List Nat := [1, 5, 1, 3, 2, 1, 1, 6]
def baseStart_447981 : Nat := 118140960795 + 447981 * 2 ^ 59
def prefixEnd_447981 : Nat := 4983230072969 + 3 ^ 40 * 447981 * 2
def baseEnd_447981 : Nat := 68156911727975409178453

theorem tailTrace_447981 : CollatzResearch.WordTrace tailWord_447981 prefixEnd_447981 68156911727975409178453 := by
  unfold tailWord_447981
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339209390048820908711797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10892806260032547272474531 16339209390048820908711797)
  ·
    refine ⟨1531800880317076960191731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16339209390048820908711797 1531800880317076960191731)
    ·
      refine ⟨2297701320475615440287597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531800880317076960191731 2297701320475615440287597)
      ·
        refine ⟨861637995178355790107849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2297701320475615440287597 861637995178355790107849)
        ·
          refine ⟨646228496383766842580887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861637995178355790107849 646228496383766842580887)
          ·
            refine ⟨969342744575650263871331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646228496383766842580887 969342744575650263871331)
            ·
              refine ⟨1454014116863475395806997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969342744575650263871331 1454014116863475395806997)
              ·
                refine ⟨68156911727975409178453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1454014116863475395806997 68156911727975409178453)
                ·
                  rfl

theorem cell20_447981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_447981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447981 prefixEnd_447981 := by exact prefixLift 447981
  have htrace : WordTrace (prefixWord ++ tailWord_447981) baseStart_447981 baseEnd_447981 := by
    simpa [prefixWord, tailWord_447981, baseEnd_447981] using wordTrace_append hprefix tailTrace_447981
  have hstable : (prefixWord ++ tailWord_447981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447981).length < 2 ^ (prefixWord ++ tailWord_447981).sum := by decide
  have hdescent : baseEnd_447981 < baseStart_447981 := by decide
  rcases family_descends (prefixWord ++ tailWord_447981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447998 : List Nat := [4, 2, 2, 3, 1, 2, 6]
def baseStart_447998 : Nat := 118140960795 + 447998 * 2 ^ 59
def prefixEnd_447998 : Nat := 4983230072969 + 3 ^ 40 * 447998 * 2
def baseEnd_447998 : Nat := 22719832716349969329847

theorem tailTrace_447998 : CollatzResearch.WordTrace tailWord_447998 prefixEnd_447998 22719832716349969329847 := by
  unfold tailWord_447998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042478678873404101510081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10893219620658155208053765 2042478678873404101510081)
  ·
    refine ⟨1531859009155053076132561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2042478678873404101510081 1531859009155053076132561)
    ·
      refine ⟨1148894256866289807099421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1531859009155053076132561 1148894256866289807099421)
      ·
        refine ⟨430835346324858677662283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1148894256866289807099421 430835346324858677662283)
        ·
          refine ⟨646253019487288016493425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430835346324858677662283 646253019487288016493425)
          ·
            refine ⟨484689764615466012370069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646253019487288016493425 484689764615466012370069)
            ·
              refine ⟨22719832716349969329847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 484689764615466012370069 22719832716349969329847)
              ·
                rfl

theorem cell20_447998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 6].length) (baseStart_447998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_447998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_447998 prefixEnd_447998 := by exact prefixLift 447998
  have htrace : WordTrace (prefixWord ++ tailWord_447998) baseStart_447998 baseEnd_447998 := by
    simpa [prefixWord, tailWord_447998, baseEnd_447998] using wordTrace_append hprefix tailTrace_447998
  have hstable : (prefixWord ++ tailWord_447998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447998).length < 2 ^ (prefixWord ++ tailWord_447998).sum := by decide
  have hdescent : baseEnd_447998 < baseStart_447998 := by decide
  rcases family_descends (prefixWord ++ tailWord_447998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448009 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 3]
def baseStart_448009 : Nat := 118140960795 + 448009 * 2 ^ 59
def prefixEnd_448009 : Nat := 4983230072969 + 3 ^ 40 * 448009 * 2
def baseEnd_448009 : Nat := 204483515146882574601911

theorem tailTrace_448009 : CollatzResearch.WordTrace tailWord_448009 prefixEnd_448009 204483515146882574601911 := by
  unfold tailWord_448009
  simp only [CollatzResearch.WordTrace]
  refine ⟨16340230633947381690731081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10893487089298254460487387 16340230633947381690731081)
  ·
    refine ⟨12255172975460536268048311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16340230633947381690731081 12255172975460536268048311)
    ·
      refine ⟨18382759463190804402072467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12255172975460536268048311 18382759463190804402072467)
      ·
        refine ⟨27574139194786206603108701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18382759463190804402072467 27574139194786206603108701)
        ·
          refine ⟨10340302198044827476165763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27574139194786206603108701 10340302198044827476165763)
          ·
            refine ⟨15510453297067241214248645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10340302198044827476165763 15510453297067241214248645)
            ·
              refine ⟨2908209993200107727671621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15510453297067241214248645 2908209993200107727671621)
              ·
                refine ⟨545289373725020198938429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2908209993200107727671621 545289373725020198938429)
                ·
                  refine ⟨204483515146882574601911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545289373725020198938429 204483515146882574601911)
                  ·
                    rfl

theorem cell20_448009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_448009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448009 prefixEnd_448009 := by exact prefixLift 448009
  have htrace : WordTrace (prefixWord ++ tailWord_448009) baseStart_448009 baseEnd_448009 := by
    simpa [prefixWord, tailWord_448009, baseEnd_448009] using wordTrace_append hprefix tailTrace_448009
  have hstable : (prefixWord ++ tailWord_448009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448009).length < 2 ^ (prefixWord ++ tailWord_448009).sum := by decide
  have hdescent : baseEnd_448009 < baseStart_448009 := by decide
  rcases family_descends (prefixWord ++ tailWord_448009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448012 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_448012 : Nat := 118140960795 + 448012 * 2 ^ 59
def prefixEnd_448012 : Nat := 4983230072969 + 3 ^ 40 * 448012 * 2
def baseEnd_448012 : Nat := 204484884428627897501899

theorem tailTrace_448012 : CollatzResearch.WordTrace tailWord_448012 prefixEnd_448012 204484884428627897501899 := by
  unfold tailWord_448012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8170170026468256601545145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10893560035291008802060193 8170170026468256601545145)
  ·
    refine ⟨6127627519851192451158859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8170170026468256601545145 6127627519851192451158859)
    ·
      refine ⟨9191441279776788676738289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6127627519851192451158859 9191441279776788676738289)
      ·
        refine ⟨6893580959832591507553717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9191441279776788676738289 6893580959832591507553717)
        ·
          refine ⟨646273214984305453833161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6893580959832591507553717 646273214984305453833161)
          ·
            refine ⟨484704911238229090374871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646273214984305453833161 484704911238229090374871)
            ·
              refine ⟨727057366857343635562307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484704911238229090374871 727057366857343635562307)
              ·
                refine ⟨1090586050286015453343461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727057366857343635562307 1090586050286015453343461)
                ·
                  refine ⟨204484884428627897501899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090586050286015453343461 204484884428627897501899)
                  ·
                    rfl

theorem cell20_448012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_448012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448012 prefixEnd_448012 := by exact prefixLift 448012
  have htrace : WordTrace (prefixWord ++ tailWord_448012) baseStart_448012 baseEnd_448012 := by
    simpa [prefixWord, tailWord_448012, baseEnd_448012] using wordTrace_append hprefix tailTrace_448012
  have hstable : (prefixWord ++ tailWord_448012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448012).length < 2 ^ (prefixWord ++ tailWord_448012).sum := by decide
  have hdescent : baseEnd_448012 < baseStart_448012 := by decide
  rcases family_descends (prefixWord ++ tailWord_448012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448061 : List Nat := [1, 4, 1, 3, 11]
def baseStart_448061 : Nat := 118140960795 + 448061 * 2 ^ 59
def prefixEnd_448061 : Nat := 4983230072969 + 3 ^ 40 * 448061 * 2
def baseEnd_448061 : Nat := 2524780856343228455165

theorem tailTrace_448061 : CollatzResearch.WordTrace tailWord_448061 prefixEnd_448061 2524780856343228455165 := by
  unfold tailWord_448061
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342127229758994571624037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10894751486505996381082691 16342127229758994571624037)
  ·
    refine ⟨3064148855579811482179507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16342127229758994571624037 3064148855579811482179507)
    ·
      refine ⟨4596223283369717223269261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3064148855579811482179507 4596223283369717223269261)
      ·
        refine ⟨1723583731263643958725973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4596223283369717223269261 1723583731263643958725973)
        ·
          refine ⟨2524780856343228455165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1723583731263643958725973 2524780856343228455165)
          ·
            rfl

theorem cell20_448061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 11].length) (baseStart_448061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448061 prefixEnd_448061 := by exact prefixLift 448061
  have htrace : WordTrace (prefixWord ++ tailWord_448061) baseStart_448061 baseEnd_448061 := by
    simpa [prefixWord, tailWord_448061, baseEnd_448061] using wordTrace_append hprefix tailTrace_448061
  have hstable : (prefixWord ++ tailWord_448061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448061).length < 2 ^ (prefixWord ++ tailWord_448061).sum := by decide
  have hdescent : baseEnd_448061 < baseStart_448061 := by decide
  rcases family_descends (prefixWord ++ tailWord_448061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448136 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_448136 : Nat := 118140960795 + 448136 * 2 ^ 59
def prefixEnd_448136 : Nat := 4983230072969 + 3 ^ 40 * 448136 * 2
def baseEnd_448136 : Nat := 204541481407434577368059

theorem tailTrace_448136 : CollatzResearch.WordTrace tailWord_448136 prefixEnd_448136 204541481407434577368059 := by
  unfold tailWord_448136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172431352243641190302131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10896575136324854920402841 8172431352243641190302131)
  ·
    refine ⟨12258647028365461785453197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172431352243641190302131 12258647028365461785453197)
    ·
      refine ⟨4596992635637048169544949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12258647028365461785453197 4596992635637048169544949)
      ·
        refine ⟨430968059590973265894839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4596992635637048169544949 430968059590973265894839)
        ·
          refine ⟨646452089386459898842259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430968059590973265894839 646452089386459898842259)
          ·
            refine ⟨969678134079689848263389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646452089386459898842259 969678134079689848263389)
            ·
              refine ⟨363629300279883693098771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 969678134079689848263389 363629300279883693098771)
              ·
                refine ⟨545443950419825539648157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363629300279883693098771 545443950419825539648157)
                ·
                  refine ⟨204541481407434577368059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545443950419825539648157 204541481407434577368059)
                  ·
                    rfl

theorem cell20_448136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_448136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448136 prefixEnd_448136 := by exact prefixLift 448136
  have htrace : WordTrace (prefixWord ++ tailWord_448136) baseStart_448136 baseEnd_448136 := by
    simpa [prefixWord, tailWord_448136, baseEnd_448136] using wordTrace_append hprefix tailTrace_448136
  have hstable : (prefixWord ++ tailWord_448136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448136).length < 2 ^ (prefixWord ++ tailWord_448136).sum := by decide
  have hdescent : baseEnd_448136 < baseStart_448136 := by decide
  rcases family_descends (prefixWord ++ tailWord_448136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448140 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_448140 : Nat := 118140960795 + 448140 * 2 ^ 59
def prefixEnd_448140 : Nat := 4983230072969 + 3 ^ 40 * 448140 * 2
def baseEnd_448140 : Nat := 204543307116428341234709

theorem tailTrace_448140 : CollatzResearch.WordTrace tailWord_448140 prefixEnd_448140 204543307116428341234709 := by
  unfold tailWord_448140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172504298236395531874937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10896672397648527375833249 8172504298236395531874937)
  ·
    refine ⟨6129378223677296648906203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8172504298236395531874937 6129378223677296648906203)
    ·
      refine ⟨9194067335515944973359305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129378223677296648906203 9194067335515944973359305)
      ·
        refine ⟨6895550501636958730019479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9194067335515944973359305 6895550501636958730019479)
        ·
          refine ⟨10343325752455438095029219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895550501636958730019479 10343325752455438095029219)
          ·
            refine ⟨15514988628683157142543829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10343325752455438095029219 15514988628683157142543829)
            ·
              refine ⟨363632545984761495528371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15514988628683157142543829 363632545984761495528371)
              ·
                refine ⟨545448818977142243292557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363632545984761495528371 545448818977142243292557)
                ·
                  refine ⟨204543307116428341234709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545448818977142243292557 204543307116428341234709)
                  ·
                    rfl

theorem cell20_448140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_448140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448140 prefixEnd_448140 := by exact prefixLift 448140
  have htrace : WordTrace (prefixWord ++ tailWord_448140) baseStart_448140 baseEnd_448140 := by
    simpa [prefixWord, tailWord_448140, baseEnd_448140] using wordTrace_append hprefix tailTrace_448140
  have hstable : (prefixWord ++ tailWord_448140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448140).length < 2 ^ (prefixWord ++ tailWord_448140).sum := by decide
  have hdescent : baseEnd_448140 < baseStart_448140 := by decide
  rcases family_descends (prefixWord ++ tailWord_448140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448161 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_448161 : Nat := 118140960795 + 448161 * 2 ^ 59
def prefixEnd_448161 : Nat := 4983230072969 + 3 ^ 40 * 448161 * 2
def baseEnd_448161 : Nat := 204552892088645601534623

theorem tailTrace_448161 : CollatzResearch.WordTrace tailWord_448161 prefixEnd_448161 204552892088645601534623 := by
  unfold tailWord_448161
  simp only [CollatzResearch.WordTrace]
  refine ⟨16345774529396711650264337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10897183019597807766842891 16345774529396711650264337)
  ·
    refine ⟨12259330897047533737698253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16345774529396711650264337 12259330897047533737698253)
    ·
      refine ⟨4597249086392825151636845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12259330897047533737698253 4597249086392825151636845)
      ·
        refine ⟨1723968407397309431863817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4597249086392825151636845 1723968407397309431863817)
        ·
          refine ⟨1292976305547982073897863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1723968407397309431863817 1292976305547982073897863)
          ·
            refine ⟨1939464458321973110846795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292976305547982073897863 1939464458321973110846795)
            ·
              refine ⟨2909196687482959666270193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939464458321973110846795 2909196687482959666270193)
              ·
                refine ⟨2181897515612219749702645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909196687482959666270193 2181897515612219749702645)
                ·
                  refine ⟨204552892088645601534623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2181897515612219749702645 204552892088645601534623)
                  ·
                    rfl

theorem cell20_448161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_448161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448161 prefixEnd_448161 := by exact prefixLift 448161
  have htrace : WordTrace (prefixWord ++ tailWord_448161) baseStart_448161 baseEnd_448161 := by
    simpa [prefixWord, tailWord_448161, baseEnd_448161] using wordTrace_append hprefix tailTrace_448161
  have hstable : (prefixWord ++ tailWord_448161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448161).length < 2 ^ (prefixWord ++ tailWord_448161).sum := by decide
  have hdescent : baseEnd_448161 < baseStart_448161 := by decide
  rcases family_descends (prefixWord ++ tailWord_448161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448164 : List Nat := [2, 3, 1, 2, 2, 2, 3, 3, 2]
def baseStart_448164 : Nat := 118140960795 + 448164 * 2 ^ 59
def prefixEnd_448164 : Nat := 4983230072969 + 3 ^ 40 * 448164 * 2
def baseEnd_448164 : Nat := 204554261370390924434611

theorem tailTrace_448164 : CollatzResearch.WordTrace tailWord_448164 prefixEnd_448164 204554261370390924434611 := by
  unfold tailWord_448164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172941974192921581311773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10897255965590562108415697 8172941974192921581311773)
  ·
    refine ⟨3064853240322345592991915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8172941974192921581311773 3064853240322345592991915)
    ·
      refine ⟨4597279860483518389487873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3064853240322345592991915 4597279860483518389487873)
      ·
        refine ⟨3447959895362638792115905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4597279860483518389487873 3447959895362638792115905)
        ·
          refine ⟨2585969921521979094086929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3447959895362638792115905 2585969921521979094086929)
          ·
            refine ⟨1939477441141484320565197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585969921521979094086929 1939477441141484320565197)
            ·
              refine ⟨727304040428056620211949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1939477441141484320565197 727304040428056620211949)
              ·
                refine ⟨272739015160521232579481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727304040428056620211949 272739015160521232579481)
                ·
                  refine ⟨204554261370390924434611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272739015160521232579481 204554261370390924434611)
                  ·
                    rfl

theorem cell20_448164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_448164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448164 prefixEnd_448164 := by exact prefixLift 448164
  have htrace : WordTrace (prefixWord ++ tailWord_448164) baseStart_448164 baseEnd_448164 := by
    simpa [prefixWord, tailWord_448164, baseEnd_448164] using wordTrace_append hprefix tailTrace_448164
  have hstable : (prefixWord ++ tailWord_448164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448164).length < 2 ^ (prefixWord ++ tailWord_448164).sum := by decide
  have hdescent : baseEnd_448164 < baseStart_448164 := by decide
  rcases family_descends (prefixWord ++ tailWord_448164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448181 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 4]
def baseStart_448181 : Nat := 118140960795 + 448181 * 2 ^ 59
def prefixEnd_448181 : Nat := 4983230072969 + 3 ^ 40 * 448181 * 2
def baseEnd_448181 : Nat := 204562020633614420867875

theorem tailTrace_448181 : CollatzResearch.WordTrace tailWord_448181 prefixEnd_448181 204562020633614420867875 := by
  unfold tailWord_448181
  simp only [CollatzResearch.WordTrace]
  refine ⟨16346503989324255065992397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10897669326216170043994931 16346503989324255065992397)
  ·
    refine ⟨6129938995996595649747149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16346503989324255065992397 6129938995996595649747149)
    ·
      refine ⟨2298727123498723368655181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6129938995996595649747149 2298727123498723368655181)
      ·
        refine ⟨862022671312021263245693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2298727123498723368655181 862022671312021263245693)
        ·
          refine ⟨323258501742007973717135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 862022671312021263245693 323258501742007973717135)
          ·
            refine ⟨484887752613011960575703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323258501742007973717135 484887752613011960575703)
            ·
              refine ⟨727331628919517940863555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484887752613011960575703 727331628919517940863555)
              ·
                refine ⟨1090997443379276911295333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727331628919517940863555 1090997443379276911295333)
                ·
                  refine ⟨204562020633614420867875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090997443379276911295333 204562020633614420867875)
                  ·
                    rfl

theorem cell20_448181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_448181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448181 prefixEnd_448181 := by exact prefixLift 448181
  have htrace : WordTrace (prefixWord ++ tailWord_448181) baseStart_448181 baseEnd_448181 := by
    simpa [prefixWord, tailWord_448181, baseEnd_448181] using wordTrace_append hprefix tailTrace_448181
  have hstable : (prefixWord ++ tailWord_448181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448181).length < 2 ^ (prefixWord ++ tailWord_448181).sum := by decide
  have hdescent : baseEnd_448181 < baseStart_448181 := by decide
  rcases family_descends (prefixWord ++ tailWord_448181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448185 : List Nat := [1, 2, 1, 4, 1, 1, 2, 6, 2]
def baseStart_448185 : Nat := 118140960795 + 448185 * 2 ^ 59
def prefixEnd_448185 : Nat := 4983230072969 + 3 ^ 40 * 448185 * 2
def baseEnd_448185 : Nat := 204563846342608184734525

theorem tailTrace_448185 : CollatzResearch.WordTrace tailWord_448185 prefixEnd_448185 204563846342608184734525 := by
  unfold tailWord_448185
  simp only [CollatzResearch.WordTrace]
  refine ⟨16346649881309763749138009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10897766587539842499425339 16346649881309763749138009)
  ·
    refine ⟨12259987410982322811853507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16346649881309763749138009 12259987410982322811853507)
    ·
      refine ⟨18389981116473484217780261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12259987410982322811853507 18389981116473484217780261)
      ·
        refine ⟨3448121459338778290833799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18389981116473484217780261 3448121459338778290833799)
        ·
          refine ⟨5172182189008167436250699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448121459338778290833799 5172182189008167436250699)
          ·
            refine ⟨7758273283512251154376049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172182189008167436250699 7758273283512251154376049)
            ·
              refine ⟨5818704962634188365782037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7758273283512251154376049 5818704962634188365782037)
              ·
                refine ⟨272751795123477579646033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5818704962634188365782037 272751795123477579646033)
                ·
                  refine ⟨204563846342608184734525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272751795123477579646033 204563846342608184734525)
                  ·
                    rfl

theorem cell20_448185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_448185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448185 prefixEnd_448185 := by exact prefixLift 448185
  have htrace : WordTrace (prefixWord ++ tailWord_448185) baseStart_448185 baseEnd_448185 := by
    simpa [prefixWord, tailWord_448185, baseEnd_448185] using wordTrace_append hprefix tailTrace_448185
  have hstable : (prefixWord ++ tailWord_448185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448185).length < 2 ^ (prefixWord ++ tailWord_448185).sum := by decide
  have hdescent : baseEnd_448185 < baseStart_448185 := by decide
  rcases family_descends (prefixWord ++ tailWord_448185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448199 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 3]
def baseStart_448199 : Nat := 118140960795 + 448199 * 2 ^ 59
def prefixEnd_448199 : Nat := 4983230072969 + 3 ^ 40 * 448199 * 2
def baseEnd_448199 : Nat := 204570236324086358267801

theorem tailTrace_448199 : CollatzResearch.WordTrace tailWord_448199 prefixEnd_448199 204570236324086358267801 := by
  unfold tailWord_448199
  simp only [CollatzResearch.WordTrace]
  refine ⟨16347160503259044140147651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10898107002172696093431767 16347160503259044140147651)
  ·
    refine ⟨24520740754888566210221477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16347160503259044140147651 24520740754888566210221477)
    ·
      refine ⟨4597638891541606164416527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24520740754888566210221477 4597638891541606164416527)
      ·
        refine ⟨6896458337312409246624791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4597638891541606164416527 6896458337312409246624791)
        ·
          refine ⟨10344687505968613869937187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6896458337312409246624791 10344687505968613869937187)
          ·
            refine ⟨15517031258952920804905781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10344687505968613869937187 15517031258952920804905781)
            ·
              refine ⟨1454721680526836325459917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15517031258952920804905781 1454721680526836325459917)
              ·
                refine ⟨545520630197563622047469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1454721680526836325459917 545520630197563622047469)
                ·
                  refine ⟨204570236324086358267801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545520630197563622047469 204570236324086358267801)
                  ·
                    rfl

theorem cell20_448199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_448199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448199 prefixEnd_448199 := by exact prefixLift 448199
  have htrace : WordTrace (prefixWord ++ tailWord_448199) baseStart_448199 baseEnd_448199 := by
    simpa [prefixWord, tailWord_448199, baseEnd_448199] using wordTrace_append hprefix tailTrace_448199
  have hstable : (prefixWord ++ tailWord_448199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448199).length < 2 ^ (prefixWord ++ tailWord_448199).sum := by decide
  have hdescent : baseEnd_448199 < baseStart_448199 := by decide
  rcases family_descends (prefixWord ++ tailWord_448199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448206 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_448206 : Nat := 118140960795 + 448206 * 2 ^ 59
def prefixEnd_448206 : Nat := 4983230072969 + 3 ^ 40 * 448206 * 2
def baseEnd_448206 : Nat := 204573431314825445034439

theorem tailTrace_448206 : CollatzResearch.WordTrace tailWord_448206 prefixEnd_448206 204573431314825445034439 := by
  unfold tailWord_448206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043426976779210541956559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10898277209489122890434981 2043426976779210541956559)
  ·
    refine ⟨3065140465168815812934839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2043426976779210541956559 3065140465168815812934839)
    ·
      refine ⟨4597710697753223719402259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3065140465168815812934839 4597710697753223719402259)
      ·
        refine ⟨6896566046629835579103389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4597710697753223719402259 6896566046629835579103389)
        ·
          refine ⟨2586212267486188342163771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6896566046629835579103389 2586212267486188342163771)
          ·
            refine ⟨3879318401229282513245657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586212267486188342163771 3879318401229282513245657)
            ·
              refine ⟨2909488800921961884934243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3879318401229282513245657 2909488800921961884934243)
              ·
                refine ⟨4364233201382942827401365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909488800921961884934243 4364233201382942827401365)
                ·
                  refine ⟨204573431314825445034439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4364233201382942827401365 204573431314825445034439)
                  ·
                    rfl

theorem cell20_448206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_448206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448206 prefixEnd_448206 := by exact prefixLift 448206
  have htrace : WordTrace (prefixWord ++ tailWord_448206) baseStart_448206 baseEnd_448206 := by
    simpa [prefixWord, tailWord_448206, baseEnd_448206] using wordTrace_append hprefix tailTrace_448206
  have hstable : (prefixWord ++ tailWord_448206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448206).length < 2 ^ (prefixWord ++ tailWord_448206).sum := by decide
  have hdescent : baseEnd_448206 < baseStart_448206 := by decide
  rcases family_descends (prefixWord ++ tailWord_448206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448223 : List Nat := [1, 1, 2, 3, 2, 2, 2, 5, 2]
def baseStart_448223 : Nat := 118140960795 + 448223 * 2 ^ 59
def prefixEnd_448223 : Nat := 4983230072969 + 3 ^ 40 * 448223 * 2
def baseEnd_448223 : Nat := 204581190578048941467703

theorem tailTrace_448223 : CollatzResearch.WordTrace tailWord_448223 prefixEnd_448223 204581190578048941467703 := by
  unfold tailWord_448223
  simp only [CollatzResearch.WordTrace]
  refine ⟨16348035855172096239021323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10898690570114730826014215 16348035855172096239021323)
  ·
    refine ⟨24522053782758144358531985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16348035855172096239021323 24522053782758144358531985)
    ·
      refine ⟨18391540337068608268898989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24522053782758144358531985 18391540337068608268898989)
      ·
        refine ⟨6896827626400728100837121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18391540337068608268898989 6896827626400728100837121)
        ·
          refine ⟨5172620719800546075627841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6896827626400728100837121 5172620719800546075627841)
          ·
            refine ⟨3879465539850409556720881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5172620719800546075627841 3879465539850409556720881)
            ·
              refine ⟨2909599154887807167540661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3879465539850409556720881 2909599154887807167540661)
              ·
                refine ⟨272774920770731921956937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2909599154887807167540661 272774920770731921956937)
                ·
                  refine ⟨204581190578048941467703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272774920770731921956937 204581190578048941467703)
                  ·
                    rfl

theorem cell20_448223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 2].length) (baseStart_448223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448223 prefixEnd_448223 := by exact prefixLift 448223
  have htrace : WordTrace (prefixWord ++ tailWord_448223) baseStart_448223 baseEnd_448223 := by
    simpa [prefixWord, tailWord_448223, baseEnd_448223] using wordTrace_append hprefix tailTrace_448223
  have hstable : (prefixWord ++ tailWord_448223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448223).length < 2 ^ (prefixWord ++ tailWord_448223).sum := by decide
  have hdescent : baseEnd_448223 < baseStart_448223 := by decide
  rcases family_descends (prefixWord ++ tailWord_448223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448289 : List Nat := [1, 2, 3, 2, 1, 4, 7]
def baseStart_448289 : Nat := 118140960795 + 448289 * 2 ^ 59
def prefixEnd_448289 : Nat := 4983230072969 + 3 ^ 40 * 448289 * 2
def baseEnd_448289 : Nat := 22734590530716227251937

theorem tailTrace_448289 : CollatzResearch.WordTrace tailWord_448289 prefixEnd_448289 22734590530716227251937 := by
  unfold tailWord_448289
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350443072932989510923921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10900295381955326340615947 16350443072932989510923921)
  ·
    refine ⟨12262832304699742133192941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16350443072932989510923921 12262832304699742133192941)
    ·
      refine ⟨4598562114262403299947353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12262832304699742133192941 4598562114262403299947353)
      ·
        refine ⟨3448921585696802474960515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4598562114262403299947353 3448921585696802474960515)
        ·
          refine ⟨5173382378545203712440773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448921585696802474960515 5173382378545203712440773)
          ·
            refine ⟨970009195977225696082645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5173382378545203712440773 970009195977225696082645)
            ·
              refine ⟨22734590530716227251937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 970009195977225696082645 22734590530716227251937)
              ·
                rfl

theorem cell20_448289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_448289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448289 prefixEnd_448289 := by exact prefixLift 448289
  have htrace : WordTrace (prefixWord ++ tailWord_448289) baseStart_448289 baseEnd_448289 := by
    simpa [prefixWord, tailWord_448289, baseEnd_448289] using wordTrace_append hprefix tailTrace_448289
  have hstable : (prefixWord ++ tailWord_448289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448289).length < 2 ^ (prefixWord ++ tailWord_448289).sum := by decide
  have hdescent : baseEnd_448289 < baseStart_448289 := by decide
  rcases family_descends (prefixWord ++ tailWord_448289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448292 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_448292 : Nat := 118140960795 + 448292 * 2 ^ 59
def prefixEnd_448292 : Nat := 4983230072969 + 3 ^ 40 * 448292 * 2
def baseEnd_448292 : Nat := 204612684058191368167421

theorem tailTrace_448292 : CollatzResearch.WordTrace tailWord_448292 prefixEnd_448292 204612684058191368167421 := by
  unfold tailWord_448292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8175276245961060511641565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10900368327948080682188753 8175276245961060511641565)
  ·
    refine ⟨3065728592235397691865587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8175276245961060511641565 3065728592235397691865587)
    ·
      refine ⟨4598592888353096537798381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3065728592235397691865587 4598592888353096537798381)
      ·
        refine ⟨1724472333132411201674393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4598592888353096537798381 1724472333132411201674393)
        ·
          refine ⟨1293354249849308401255795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724472333132411201674393 1293354249849308401255795)
          ·
            refine ⟨1940031374773962601883693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293354249849308401255795 1940031374773962601883693)
            ·
              refine ⟨727511765540235975706385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1940031374773962601883693 727511765540235975706385)
              ·
                refine ⟨545633824155176981779789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727511765540235975706385 545633824155176981779789)
                ·
                  refine ⟨204612684058191368167421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545633824155176981779789 204612684058191368167421)
                  ·
                    rfl

theorem cell20_448292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_448292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448292 prefixEnd_448292 := by exact prefixLift 448292
  have htrace : WordTrace (prefixWord ++ tailWord_448292) baseStart_448292 baseEnd_448292 := by
    simpa [prefixWord, tailWord_448292, baseEnd_448292] using wordTrace_append hprefix tailTrace_448292
  have hstable : (prefixWord ++ tailWord_448292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448292).length < 2 ^ (prefixWord ++ tailWord_448292).sum := by decide
  have hdescent : baseEnd_448292 < baseStart_448292 := by decide
  rcases family_descends (prefixWord ++ tailWord_448292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448303 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_448303 : Nat := 118140960795 + 448303 * 2 ^ 59
def prefixEnd_448303 : Nat := 4983230072969 + 3 ^ 40 * 448303 * 2
def baseEnd_448303 : Nat := 204617704757924218800709

theorem tailTrace_448303 : CollatzResearch.WordTrace tailWord_448303 prefixEnd_448303 204617704757924218800709 := by
  unfold tailWord_448303
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350953694882269901933563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10900635796588179934622375 16350953694882269901933563)
  ·
    refine ⟨24526430542323404852900345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16350953694882269901933563 24526430542323404852900345)
    ·
      refine ⟨18394822906742553639675259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24526430542323404852900345 18394822906742553639675259)
      ·
        refine ⟨27592234360113830459512889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18394822906742553639675259 27592234360113830459512889)
        ·
          refine ⟨20694175770085372844634667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27592234360113830459512889 20694175770085372844634667)
          ·
            refine ⟨31041263655128059266952001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20694175770085372844634667 31041263655128059266952001)
            ·
              refine ⟨23280947741346044450214001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31041263655128059266952001 23280947741346044450214001)
              ·
                refine ⟨17460710806009533337660501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23280947741346044450214001 17460710806009533337660501)
                ·
                  refine ⟨204617704757924218800709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17460710806009533337660501 204617704757924218800709)
                  ·
                    rfl

theorem cell20_448303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_448303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448303 prefixEnd_448303 := by exact prefixLift 448303
  have htrace : WordTrace (prefixWord ++ tailWord_448303) baseStart_448303 baseEnd_448303 := by
    simpa [prefixWord, tailWord_448303, baseEnd_448303] using wordTrace_append hprefix tailTrace_448303
  have hstable : (prefixWord ++ tailWord_448303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448303).length < 2 ^ (prefixWord ++ tailWord_448303).sum := by decide
  have hdescent : baseEnd_448303 < baseStart_448303 := by decide
  rcases family_descends (prefixWord ++ tailWord_448303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448309 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 3]
def baseStart_448309 : Nat := 118140960795 + 448309 * 2 ^ 59
def prefixEnd_448309 : Nat := 4983230072969 + 3 ^ 40 * 448309 * 2
def baseEnd_448309 : Nat := 204620443321414864600685

theorem tailTrace_448309 : CollatzResearch.WordTrace tailWord_448309 prefixEnd_448309 204620443321414864600685 := by
  unfold tailWord_448309
  simp only [CollatzResearch.WordTrace]
  refine ⟨16351172532860532926651981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10900781688573688617767987 16351172532860532926651981)
  ·
    refine ⟨6131689699822699847494493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16351172532860532926651981 6131689699822699847494493)
    ·
      refine ⟨2299383637433512442810435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6131689699822699847494493 2299383637433512442810435)
      ·
        refine ⟨3449075456150268664215653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299383637433512442810435 3449075456150268664215653)
        ·
          refine ⟨646701648028175374540435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3449075456150268664215653 646701648028175374540435)
          ·
            refine ⟨970052472042263061810653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646701648028175374540435 970052472042263061810653)
            ·
              refine ⟨363769677015848648178995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 970052472042263061810653 363769677015848648178995)
              ·
                refine ⟨545654515523772972268493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363769677015848648178995 545654515523772972268493)
                ·
                  refine ⟨204620443321414864600685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545654515523772972268493 204620443321414864600685)
                  ·
                    rfl

theorem cell20_448309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_448309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448309 prefixEnd_448309 := by exact prefixLift 448309
  have htrace : WordTrace (prefixWord ++ tailWord_448309) baseStart_448309 baseEnd_448309 := by
    simpa [prefixWord, tailWord_448309, baseEnd_448309] using wordTrace_append hprefix tailTrace_448309
  have hstable : (prefixWord ++ tailWord_448309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448309).length < 2 ^ (prefixWord ++ tailWord_448309).sum := by decide
  have hdescent : baseEnd_448309 < baseStart_448309 := by decide
  rcases family_descends (prefixWord ++ tailWord_448309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448333 : List Nat := [1, 6, 1, 2, 1, 1, 3, 3, 2]
def baseStart_448333 : Nat := 118140960795 + 448333 * 2 ^ 59
def prefixEnd_448333 : Nat := 4983230072969 + 3 ^ 40 * 448333 * 2
def baseEnd_448333 : Nat := 204631397575377447800587

theorem tailTrace_448333 : CollatzResearch.WordTrace tailWord_448333 prefixEnd_448333 204631397575377447800587 := by
  unfold tailWord_448333
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352047884773585025525653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10901365256515723350350435 16352047884773585025525653)
  ·
    refine ⟨766502244598761798071515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16352047884773585025525653 766502244598761798071515)
    ·
      refine ⟨1149753366898142697107273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766502244598761798071515 1149753366898142697107273)
      ·
        refine ⟨862315025173607022830455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1149753366898142697107273 862315025173607022830455)
        ·
          refine ⟨1293472537760410534245683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862315025173607022830455 1293472537760410534245683)
          ·
            refine ⟨1940208806640615801368525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293472537760410534245683 1940208806640615801368525)
            ·
              refine ⟨727578302490230925513197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1940208806640615801368525 727578302490230925513197)
              ·
                refine ⟨272841863433836597067449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727578302490230925513197 272841863433836597067449)
                ·
                  refine ⟨204631397575377447800587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272841863433836597067449 204631397575377447800587)
                  ·
                    rfl

theorem cell20_448333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_448333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448333 prefixEnd_448333 := by exact prefixLift 448333
  have htrace : WordTrace (prefixWord ++ tailWord_448333) baseStart_448333 baseEnd_448333 := by
    simpa [prefixWord, tailWord_448333, baseEnd_448333] using wordTrace_append hprefix tailTrace_448333
  have hstable : (prefixWord ++ tailWord_448333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448333).length < 2 ^ (prefixWord ++ tailWord_448333).sum := by decide
  have hdescent : baseEnd_448333 < baseStart_448333 := by decide
  rcases family_descends (prefixWord ++ tailWord_448333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448354 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_448354 : Nat := 118140960795 + 448354 * 2 ^ 59
def prefixEnd_448354 : Nat := 4983230072969 + 3 ^ 40 * 448354 * 2
def baseEnd_448354 : Nat := 204640982547594708100501

theorem tailTrace_448354 : CollatzResearch.WordTrace tailWord_448354 prefixEnd_448354 204640982547594708100501 := by
  unfold tailWord_448354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088203454424376403010029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10901875878465003741360077 4088203454424376403010029)
  ·
    refine ⟨1533076295409141151128761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4088203454424376403010029 1533076295409141151128761)
    ·
      refine ⟨1149807221556855863346571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1533076295409141151128761 1149807221556855863346571)
      ·
        refine ⟨1724710832335283795019857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149807221556855863346571 1724710832335283795019857)
        ·
          refine ⟨1293533124251462846264893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724710832335283795019857 1293533124251462846264893)
          ·
            refine ⟨485074921594298567349335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1293533124251462846264893 485074921594298567349335)
            ·
              refine ⟨727612382391447851024003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485074921594298567349335 727612382391447851024003)
              ·
                refine ⟨1091418573587171776536005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727612382391447851024003 1091418573587171776536005)
                ·
                  refine ⟨204640982547594708100501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091418573587171776536005 204640982547594708100501)
                  ·
                    rfl

theorem cell20_448354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_448354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448354 prefixEnd_448354 := by exact prefixLift 448354
  have htrace : WordTrace (prefixWord ++ tailWord_448354) baseStart_448354 baseEnd_448354 := by
    simpa [prefixWord, tailWord_448354, baseEnd_448354] using wordTrace_append hprefix tailTrace_448354
  have hstable : (prefixWord ++ tailWord_448354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448354).length < 2 ^ (prefixWord ++ tailWord_448354).sum := by decide
  have hdescent : baseEnd_448354 < baseStart_448354 := by decide
  rcases family_descends (prefixWord ++ tailWord_448354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448365 : List Nat := [1, 5, 1, 1, 1, 1, 3, 7]
def baseStart_448365 : Nat := 118140960795 + 448365 * 2 ^ 59
def prefixEnd_448365 : Nat := 4983230072969 + 3 ^ 40 * 448365 * 2
def baseEnd_448365 : Nat := 68215334415775852911263

theorem tailTrace_448365 : CollatzResearch.WordTrace tailWord_448365 prefixEnd_448365 68215334415775852911263 := by
  unfold tailWord_448365
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353215020657654490690549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10902143347105102993793699 16353215020657654490690549)
  ·
    refine ⟨1533113908186655108502239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16353215020657654490690549 1533113908186655108502239)
    ·
      refine ⟨2299670862279982662753359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533113908186655108502239 2299670862279982662753359)
      ·
        refine ⟨3449506293419973994130039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299670862279982662753359 3449506293419973994130039)
        ·
          refine ⟨5174259440129960991195059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449506293419973994130039 5174259440129960991195059)
          ·
            refine ⟨7761389160194941486792589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174259440129960991195059 7761389160194941486792589)
            ·
              refine ⟨2910520935073103057547221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7761389160194941486792589 2910520935073103057547221)
              ·
                refine ⟨68215334415775852911263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2910520935073103057547221 68215334415775852911263)
                ·
                  rfl

theorem cell20_448365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_448365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448365 prefixEnd_448365 := by exact prefixLift 448365
  have htrace : WordTrace (prefixWord ++ tailWord_448365) baseStart_448365 baseEnd_448365 := by
    simpa [prefixWord, tailWord_448365, baseEnd_448365] using wordTrace_append hprefix tailTrace_448365
  have hstable : (prefixWord ++ tailWord_448365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448365).length < 2 ^ (prefixWord ++ tailWord_448365).sum := by decide
  have hdescent : baseEnd_448365 < baseStart_448365 := by decide
  rcases family_descends (prefixWord ++ tailWord_448365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448379 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_448379 : Nat := 118140960795 + 448379 * 2 ^ 59
def prefixEnd_448379 : Nat := 4983230072969 + 3 ^ 40 * 448379 * 2
def baseEnd_448379 : Nat := 204652393228805732267065

theorem tailTrace_448379 : CollatzResearch.WordTrace tailWord_448379 prefixEnd_448379 204652393228805732267065 := by
  unfold tailWord_448379
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353725642606934881700191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10902483761737956587800127 16353725642606934881700191)
  ·
    refine ⟨24530588463910402322550287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16353725642606934881700191 24530588463910402322550287)
    ·
      refine ⟨36795882695865603483825431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24530588463910402322550287 36795882695865603483825431)
      ·
        refine ⟨55193824043798405225738147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36795882695865603483825431 55193824043798405225738147)
        ·
          refine ⟨82790736065697607838607221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55193824043798405225738147 82790736065697607838607221)
          ·
            refine ⟨7761631506159150734869427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82790736065697607838607221 7761631506159150734869427)
            ·
              refine ⟨11642447259238726102304141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761631506159150734869427 11642447259238726102304141)
              ·
                refine ⟨4365917722214522288364053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11642447259238726102304141 4365917722214522288364053)
                ·
                  refine ⟨204652393228805732267065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4365917722214522288364053 204652393228805732267065)
                  ·
                    rfl

theorem cell20_448379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_448379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448379 prefixEnd_448379 := by exact prefixLift 448379
  have htrace : WordTrace (prefixWord ++ tailWord_448379) baseStart_448379 baseEnd_448379 := by
    simpa [prefixWord, tailWord_448379, baseEnd_448379] using wordTrace_append hprefix tailTrace_448379
  have hstable : (prefixWord ++ tailWord_448379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448379).length < 2 ^ (prefixWord ++ tailWord_448379).sum := by decide
  have hdescent : baseEnd_448379 < baseStart_448379 := by decide
  rcases family_descends (prefixWord ++ tailWord_448379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448420 : List Nat := [2, 3, 1, 2, 1, 5, 1, 5]
def baseStart_448420 : Nat := 118140960795 + 448420 * 2 ^ 59
def prefixEnd_448420 : Nat := 4983230072969 + 3 ^ 40 * 448420 * 2
def baseEnd_448420 : Nat := 68223702248663937300077

theorem tailTrace_448420 : CollatzResearch.WordTrace tailWord_448420 prefixEnd_448420 68223702248663937300077 := by
  unfold tailWord_448420
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177610517729199441971357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10903480690305599255961809 8177610517729199441971357)
  ·
    refine ⟨3066603944148449790739259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8177610517729199441971357 3066603944148449790739259)
    ·
      refine ⟨4599905916222674686108889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066603944148449790739259 4599905916222674686108889)
      ·
        refine ⟨3449929437167006014581667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4599905916222674686108889 3449929437167006014581667)
        ·
          refine ⟨5174894155750509021872501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449929437167006014581667 5174894155750509021872501)
          ·
            refine ⟨485146327101610220800547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5174894155750509021872501 485146327101610220800547)
            ·
              refine ⟨727719490652415331200821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485146327101610220800547 727719490652415331200821)
              ·
                refine ⟨68223702248663937300077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 727719490652415331200821 68223702248663937300077)
                ·
                  rfl

theorem cell20_448420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_448420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448420 prefixEnd_448420 := by exact prefixLift 448420
  have htrace : WordTrace (prefixWord ++ tailWord_448420) baseStart_448420 baseEnd_448420 := by
    simpa [prefixWord, tailWord_448420, baseEnd_448420] using wordTrace_append hprefix tailTrace_448420
  have hstable : (prefixWord ++ tailWord_448420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448420).length < 2 ^ (prefixWord ++ tailWord_448420).sum := by decide
  have hdescent : baseEnd_448420 < baseStart_448420 := by decide
  rcases family_descends (prefixWord ++ tailWord_448420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448448 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_448448 : Nat := 118140960795 + 448448 * 2 ^ 59
def prefixEnd_448448 : Nat := 4983230072969 + 3 ^ 40 * 448448 * 2
def baseEnd_448448 : Nat := 204683886708948158966783

theorem tailTrace_448448 : CollatzResearch.WordTrace tailWord_448448 prefixEnd_448448 204683886708948158966783 := by
  unfold tailWord_448448
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178121139678479832980999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10904161519571306443974665 8178121139678479832980999)
  ·
    refine ⟨12267181709517719749471499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8178121139678479832980999 12267181709517719749471499)
    ·
      refine ⟨18400772564276579624207249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12267181709517719749471499 18400772564276579624207249)
      ·
        refine ⟨13800579423207434718155437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18400772564276579624207249 13800579423207434718155437)
        ·
          refine ⟨5175217283702788019308289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13800579423207434718155437 5175217283702788019308289)
          ·
            refine ⟨3881412962777091014481217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175217283702788019308289 3881412962777091014481217)
            ·
              refine ⟨2911059722082818260860913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881412962777091014481217 2911059722082818260860913)
              ·
                refine ⟨2183294791562113695645685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911059722082818260860913 2183294791562113695645685)
                ·
                  refine ⟨204683886708948158966783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2183294791562113695645685 204683886708948158966783)
                  ·
                    rfl

theorem cell20_448448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_448448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448448 prefixEnd_448448 := by exact prefixLift 448448
  have htrace : WordTrace (prefixWord ++ tailWord_448448) baseStart_448448 baseEnd_448448 := by
    simpa [prefixWord, tailWord_448448, baseEnd_448448] using wordTrace_append hprefix tailTrace_448448
  have hstable : (prefixWord ++ tailWord_448448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448448).length < 2 ^ (prefixWord ++ tailWord_448448).sum := by decide
  have hdescent : baseEnd_448448 < baseStart_448448 := by decide
  rcases family_descends (prefixWord ++ tailWord_448448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448455 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_448455 : Nat := 118140960795 + 448455 * 2 ^ 59
def prefixEnd_448455 : Nat := 4983230072969 + 3 ^ 40 * 448455 * 2
def baseEnd_448455 : Nat := 204687081699687245733421

theorem tailTrace_448455 : CollatzResearch.WordTrace tailWord_448455 prefixEnd_448455 204687081699687245733421 := by
  unfold tailWord_448455
  simp only [CollatzResearch.WordTrace]
  refine ⟨16356497590331599861466819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10904331726887733240977879 16356497590331599861466819)
  ·
    refine ⟨24534746385497399792200229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16356497590331599861466819 24534746385497399792200229)
    ·
      refine ⟨4600264947280762461037543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24534746385497399792200229 4600264947280762461037543)
      ·
        refine ⟨6900397420921143691556315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4600264947280762461037543 6900397420921143691556315)
        ·
          refine ⟨10350596131381715537334473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6900397420921143691556315 10350596131381715537334473)
          ·
            refine ⟨7762947098536286653000855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10350596131381715537334473 7762947098536286653000855)
            ·
              refine ⟨11644420647804429979501283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7762947098536286653000855 11644420647804429979501283)
              ·
                refine ⟨17466630971706644969251925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11644420647804429979501283 17466630971706644969251925)
                ·
                  refine ⟨204687081699687245733421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17466630971706644969251925 204687081699687245733421)
                  ·
                    rfl

theorem cell20_448455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_448455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448455 prefixEnd_448455 := by exact prefixLift 448455
  have htrace : WordTrace (prefixWord ++ tailWord_448455) baseStart_448455 baseEnd_448455 := by
    simpa [prefixWord, tailWord_448455, baseEnd_448455] using wordTrace_append hprefix tailTrace_448455
  have hstable : (prefixWord ++ tailWord_448455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448455).length < 2 ^ (prefixWord ++ tailWord_448455).sum := by decide
  have hdescent : baseEnd_448455 < baseStart_448455 := by decide
  rcases family_descends (prefixWord ++ tailWord_448455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448472 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_448472 : Nat := 118140960795 + 448472 * 2 ^ 59
def prefixEnd_448472 : Nat := 4983230072969 + 3 ^ 40 * 448472 * 2
def baseEnd_448472 : Nat := 204694840962910742166685

theorem tailTrace_448472 : CollatzResearch.WordTrace tailWord_448472 prefixEnd_448472 204694840962910742166685 := by
  unfold tailWord_448472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178558815635005882417835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10904745087513341176557113 8178558815635005882417835)
  ·
    refine ⟨12267838223452508823626753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8178558815635005882417835 12267838223452508823626753)
    ·
      refine ⟨9200878667589381617720065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12267838223452508823626753 9200878667589381617720065)
      ·
        refine ⟨6900659000692036213290049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9200878667589381617720065 6900659000692036213290049)
        ·
          refine ⟨5175494250519027159967537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6900659000692036213290049 5175494250519027159967537)
          ·
            refine ⟨3881620687889270369975653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175494250519027159967537 3881620687889270369975653)
            ·
              refine ⟨727803878979238194370435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3881620687889270369975653 727803878979238194370435)
              ·
                refine ⟨1091705818468857291555653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727803878979238194370435 1091705818468857291555653)
                ·
                  refine ⟨204694840962910742166685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091705818468857291555653 204694840962910742166685)
                  ·
                    rfl

theorem cell20_448472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_448472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448472 prefixEnd_448472 := by exact prefixLift 448472
  have htrace : WordTrace (prefixWord ++ tailWord_448472) baseStart_448472 baseEnd_448472 := by
    simpa [prefixWord, tailWord_448472, baseEnd_448472] using wordTrace_append hprefix tailTrace_448472
  have hstable : (prefixWord ++ tailWord_448472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448472).length < 2 ^ (prefixWord ++ tailWord_448472).sum := by decide
  have hdescent : baseEnd_448472 < baseStart_448472 := by decide
  rcases family_descends (prefixWord ++ tailWord_448472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448502 : List Nat := [5, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_448502 : Nat := 118140960795 + 448502 * 2 ^ 59
def prefixEnd_448502 : Nat := 4983230072969 + 3 ^ 40 * 448502 * 2
def baseEnd_448502 : Nat := 204708533780363971166563

theorem tailTrace_448502 : CollatzResearch.WordTrace tailWord_448502 prefixEnd_448502 204708533780363971166563 := by
  unfold tailWord_448502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022388238822582930526735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10905474547440884592285173 1022388238822582930526735)
  ·
    refine ⟨1533582358233874395790103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022388238822582930526735 1533582358233874395790103)
    ·
      refine ⟨2300373537350811593685155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533582358233874395790103 2300373537350811593685155)
      ·
        refine ⟨3450560306026217390527733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300373537350811593685155 3450560306026217390527733)
        ·
          refine ⟨323490028689957880361975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3450560306026217390527733 323490028689957880361975)
          ·
            refine ⟨485235043034936820542963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323490028689957880361975 485235043034936820542963)
            ·
              refine ⟨727852564552405230814445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485235043034936820542963 727852564552405230814445)
              ·
                refine ⟨272944711707151961555417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727852564552405230814445 272944711707151961555417)
                ·
                  refine ⟨204708533780363971166563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272944711707151961555417 204708533780363971166563)
                  ·
                    rfl

theorem cell20_448502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_448502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448502 prefixEnd_448502 := by exact prefixLift 448502
  have htrace : WordTrace (prefixWord ++ tailWord_448502) baseStart_448502 baseEnd_448502 := by
    simpa [prefixWord, tailWord_448502, baseEnd_448502] using wordTrace_append hprefix tailTrace_448502
  have hstable : (prefixWord ++ tailWord_448502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448502).length < 2 ^ (prefixWord ++ tailWord_448502).sum := by decide
  have hdescent : baseEnd_448502 < baseStart_448502 := by decide
  rcases family_descends (prefixWord ++ tailWord_448502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448517 : List Nat := [1, 3, 1, 1, 2, 6, 6]
def baseStart_448517 : Nat := 118140960795 + 448517 * 2 ^ 59
def prefixEnd_448517 : Nat := 4983230072969 + 3 ^ 40 * 448517 * 2
def baseEnd_448517 : Nat := 22746153354343398407389

theorem tailTrace_448517 : CollatzResearch.WordTrace tailWord_448517 prefixEnd_448517 22746153354343398407389 := by
  unfold tailWord_448517
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358758916106984450223805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10905839277404656300149203 16358758916106984450223805)
  ·
    refine ⟨6134534593540119168833927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16358758916106984450223805 6134534593540119168833927)
    ·
      refine ⟨9201801890310178753250891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6134534593540119168833927 9201801890310178753250891)
      ·
        refine ⟨13802702835465268129876337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201801890310178753250891 13802702835465268129876337)
        ·
          refine ⟨10352027126598951097407253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13802702835465268129876337 10352027126598951097407253)
          ·
            refine ⟨485251271559325832690965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10352027126598951097407253 485251271559325832690965)
            ·
              refine ⟨22746153354343398407389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 485251271559325832690965 22746153354343398407389)
              ·
                rfl

theorem cell20_448517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 6].length) (baseStart_448517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448517 prefixEnd_448517 := by exact prefixLift 448517
  have htrace : WordTrace (prefixWord ++ tailWord_448517) baseStart_448517 baseEnd_448517 := by
    simpa [prefixWord, tailWord_448517, baseEnd_448517] using wordTrace_append hprefix tailTrace_448517
  have hstable : (prefixWord ++ tailWord_448517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448517).length < 2 ^ (prefixWord ++ tailWord_448517).sum := by decide
  have hdescent : baseEnd_448517 < baseStart_448517 := by decide
  rcases family_descends (prefixWord ++ tailWord_448517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448524 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_448524 : Nat := 118140960795 + 448524 * 2 ^ 59
def prefixEnd_448524 : Nat := 4983230072969 + 3 ^ 40 * 448524 * 2
def baseEnd_448524 : Nat := 204718575179829672433139

theorem tailTrace_448524 : CollatzResearch.WordTrace tailWord_448524 prefixEnd_448524 204718575179829672433139 := by
  unfold tailWord_448524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8179507113540812322864313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10906009484721083097152417 8179507113540812322864313)
  ·
    refine ⟨6134630335155609242148235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8179507113540812322864313 6134630335155609242148235)
    ·
      refine ⟨9201945502733413863222353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6134630335155609242148235 9201945502733413863222353)
      ·
        refine ⟨6901459127050060397416765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9201945502733413863222353 6901459127050060397416765)
        ·
          refine ⟨2588047172643772649031287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6901459127050060397416765 2588047172643772649031287)
          ·
            refine ⟨3882070758965658973546931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588047172643772649031287 3882070758965658973546931)
            ·
              refine ⟨5823106138448488460320397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882070758965658973546931 5823106138448488460320397)
              ·
                refine ⟨2183664801918183172620149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5823106138448488460320397 2183664801918183172620149)
                ·
                  refine ⟨204718575179829672433139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2183664801918183172620149 204718575179829672433139)
                  ·
                    rfl

theorem cell20_448524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_448524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448524 prefixEnd_448524 := by exact prefixLift 448524
  have htrace : WordTrace (prefixWord ++ tailWord_448524) baseStart_448524 baseEnd_448524 := by
    simpa [prefixWord, tailWord_448524, baseEnd_448524] using wordTrace_append hprefix tailTrace_448524
  have hstable : (prefixWord ++ tailWord_448524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448524).length < 2 ^ (prefixWord ++ tailWord_448524).sum := by decide
  have hdescent : baseEnd_448524 < baseStart_448524 := by decide
  rcases family_descends (prefixWord ++ tailWord_448524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448576 : List Nat := [2, 1, 1, 2, 2, 12]
def baseStart_448576 : Nat := 118140960795 + 448576 * 2 ^ 59
def prefixEnd_448576 : Nat := 4983230072969 + 3 ^ 40 * 448576 * 2
def baseEnd_448576 : Nat := 7583048496175874174059

theorem tailTrace_448576 : CollatzResearch.WordTrace tailWord_448576 prefixEnd_448576 7583048496175874174059 := by
  unfold tailWord_448576
  simp only [CollatzResearch.WordTrace]
  refine ⟨8180455411446618763310791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10907273881928825017747721 8180455411446618763310791)
  ·
    refine ⟨12270683117169928144966187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8180455411446618763310791 12270683117169928144966187)
    ·
      refine ⟨18406024675754892217449281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12270683117169928144966187 18406024675754892217449281)
      ·
        refine ⟨13804518506816169163086961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18406024675754892217449281 13804518506816169163086961)
        ·
          refine ⟨10353388880112126872315221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13804518506816169163086961 10353388880112126872315221)
          ·
            refine ⟨7583048496175874174059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10353388880112126872315221 7583048496175874174059)
            ·
              rfl

theorem cell20_448576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 12].length) (baseStart_448576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448576 prefixEnd_448576 := by exact prefixLift 448576
  have htrace : WordTrace (prefixWord ++ tailWord_448576) baseStart_448576 baseEnd_448576 := by
    simpa [prefixWord, tailWord_448576, baseEnd_448576] using wordTrace_append hprefix tailTrace_448576
  have hstable : (prefixWord ++ tailWord_448576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448576).length < 2 ^ (prefixWord ++ tailWord_448576).sum := by decide
  have hdescent : baseEnd_448576 < baseStart_448576 := by decide
  rcases family_descends (prefixWord ++ tailWord_448576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448641 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 4]
def baseStart_448641 : Nat := 118140960795 + 448641 * 2 ^ 59
def prefixEnd_448641 : Nat := 4983230072969 + 3 ^ 40 * 448641 * 2
def baseEnd_448641 : Nat := 204771977167897265532661

theorem tailTrace_448641 : CollatzResearch.WordTrace tailWord_448641 prefixEnd_448641 204771977167897265532661 := by
  unfold tailWord_448641
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363281567657753627737777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10908854378438502418491851 16363281567657753627737777)
  ·
    refine ⟨12272461175743315220803333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16363281567657753627737777 12272461175743315220803333)
    ·
      refine ⟨2301086470451871603900625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12272461175743315220803333 2301086470451871603900625)
      ·
        refine ⟨1725814852838903702925469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2301086470451871603900625 1725814852838903702925469)
        ·
          refine ⟨647180569814588888597051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1725814852838903702925469 647180569814588888597051)
          ·
            refine ⟨970770854721883332895577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647180569814588888597051 970770854721883332895577)
            ·
              refine ⟨728078141041412499671683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970770854721883332895577 728078141041412499671683)
              ·
                refine ⟨1092117211562118749507525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728078141041412499671683 1092117211562118749507525)
                ·
                  refine ⟨204771977167897265532661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092117211562118749507525 204771977167897265532661)
                  ·
                    rfl

theorem cell20_448641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_448641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448641 prefixEnd_448641 := by exact prefixLift 448641
  have htrace : WordTrace (prefixWord ++ tailWord_448641) baseStart_448641 baseEnd_448641 := by
    simpa [prefixWord, tailWord_448641, baseEnd_448641] using wordTrace_append hprefix tailTrace_448641
  have hstable : (prefixWord ++ tailWord_448641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448641).length < 2 ^ (prefixWord ++ tailWord_448641).sum := by decide
  have hdescent : baseEnd_448641 < baseStart_448641 := by decide
  rcases family_descends (prefixWord ++ tailWord_448641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448669 : List Nat := [1, 4, 2, 1, 1, 4, 1, 6]
def baseStart_448669 : Nat := 118140960795 + 448669 * 2 ^ 59
def prefixEnd_448669 : Nat := 4983230072969 + 3 ^ 40 * 448669 * 2
def baseEnd_448669 : Nat := 68261585710284537533071

theorem tailTrace_448669 : CollatzResearch.WordTrace tailWord_448669 prefixEnd_448669 68261585710284537533071 := by
  unfold tailWord_448669
  simp only [CollatzResearch.WordTrace]
  refine ⟨16364302811556314409757061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10909535207704209606504707 16364302811556314409757061)
  ·
    refine ⟨3068306777166808951829449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16364302811556314409757061 3068306777166808951829449)
    ·
      refine ⟨2301230082875106713872087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3068306777166808951829449 2301230082875106713872087)
      ·
        refine ⟨3451845124312660070808131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301230082875106713872087 3451845124312660070808131)
        ·
          refine ⟨5177767686468990106212197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451845124312660070808131 5177767686468990106212197)
          ·
            refine ⟨970831441212935644914787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5177767686468990106212197 970831441212935644914787)
            ·
              refine ⟨1456247161819403467372181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970831441212935644914787 1456247161819403467372181)
              ·
                refine ⟨68261585710284537533071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1456247161819403467372181 68261585710284537533071)
                ·
                  rfl

theorem cell20_448669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_448669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448669 prefixEnd_448669 := by exact prefixLift 448669
  have htrace : WordTrace (prefixWord ++ tailWord_448669) baseStart_448669 baseEnd_448669 := by
    simpa [prefixWord, tailWord_448669, baseEnd_448669] using wordTrace_append hprefix tailTrace_448669
  have hstable : (prefixWord ++ tailWord_448669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448669).length < 2 ^ (prefixWord ++ tailWord_448669).sum := by decide
  have hdescent : baseEnd_448669 < baseStart_448669 := by decide
  rcases family_descends (prefixWord ++ tailWord_448669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448692 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 4]
def baseStart_448692 : Nat := 118140960795 + 448692 * 2 ^ 59
def prefixEnd_448692 : Nat := 4983230072969 + 3 ^ 40 * 448692 * 2
def baseEnd_448692 : Nat := 204795254957567754832453

theorem tailTrace_448692 : CollatzResearch.WordTrace tailWord_448692 prefixEnd_448692 204795254957567754832453 := by
  unfold tailWord_448692
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182570845236494668922165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10910094460315326225229553 8182570845236494668922165)
  ·
    refine ⟨767116016740921375211453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8182570845236494668922165 767116016740921375211453)
    ·
      refine ⟨287668506277845515704295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 767116016740921375211453 287668506277845515704295)
      ·
        refine ⟨431502759416768273556443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287668506277845515704295 431502759416768273556443)
        ·
          refine ⟨647254139125152410334665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431502759416768273556443 647254139125152410334665)
          ·
            refine ⟨485440604343864307750999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647254139125152410334665 485440604343864307750999)
            ·
              refine ⟨728160906515796461626499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485440604343864307750999 728160906515796461626499)
              ·
                refine ⟨1092241359773694692439749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728160906515796461626499 1092241359773694692439749)
                ·
                  refine ⟨204795254957567754832453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092241359773694692439749 204795254957567754832453)
                  ·
                    rfl

theorem cell20_448692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_448692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448692 prefixEnd_448692 := by exact prefixLift 448692
  have htrace : WordTrace (prefixWord ++ tailWord_448692) baseStart_448692 baseEnd_448692 := by
    simpa [prefixWord, tailWord_448692, baseEnd_448692] using wordTrace_append hprefix tailTrace_448692
  have hstable : (prefixWord ++ tailWord_448692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448692).length < 2 ^ (prefixWord ++ tailWord_448692).sum := by decide
  have hdescent : baseEnd_448692 < baseStart_448692 := by decide
  rcases family_descends (prefixWord ++ tailWord_448692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448706 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_448706 : Nat := 118140960795 + 448706 * 2 ^ 59
def prefixEnd_448706 : Nat := 4983230072969 + 3 ^ 40 * 448706 * 2
def baseEnd_448706 : Nat := 204801644939045928365729

theorem tailTrace_448706 : CollatzResearch.WordTrace tailWord_448706 prefixEnd_448706 204801644939045928365729 := by
  unfold tailWord_448706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091413078105567432213493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10910434874948179819235981 4091413078105567432213493)
  ·
    refine ⟨383569976072396946770015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4091413078105567432213493 383569976072396946770015)
    ·
      refine ⟨575354964108595420155023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383569976072396946770015 575354964108595420155023)
      ·
        refine ⟨863032446162893130232535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575354964108595420155023 863032446162893130232535)
        ·
          refine ⟨1294548669244339695348803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863032446162893130232535 1294548669244339695348803)
          ·
            refine ⟨1941823003866509543023205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294548669244339695348803 1941823003866509543023205)
            ·
              refine ⟨364091813224970539316851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1941823003866509543023205 364091813224970539316851)
              ·
                refine ⟨546137719837455808975277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364091813224970539316851 546137719837455808975277)
                ·
                  refine ⟨204801644939045928365729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546137719837455808975277 204801644939045928365729)
                  ·
                    rfl

theorem cell20_448706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_448706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448706 prefixEnd_448706 := by exact prefixLift 448706
  have htrace : WordTrace (prefixWord ++ tailWord_448706) baseStart_448706 baseEnd_448706 := by
    simpa [prefixWord, tailWord_448706, baseEnd_448706] using wordTrace_append hprefix tailTrace_448706
  have hstable : (prefixWord ++ tailWord_448706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448706).length < 2 ^ (prefixWord ++ tailWord_448706).sum := by decide
  have hdescent : baseEnd_448706 < baseStart_448706 := by decide
  rcases family_descends (prefixWord ++ tailWord_448706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448721 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_448721 : Nat := 118140960795 + 448721 * 2 ^ 59
def prefixEnd_448721 : Nat := 4983230072969 + 3 ^ 40 * 448721 * 2
def baseEnd_448721 : Nat := 204808491347772542865667

theorem tailTrace_448721 : CollatzResearch.WordTrace tailWord_448721 prefixEnd_448721 204808491347772542865667 := by
  unfold tailWord_448721
  simp only [CollatzResearch.WordTrace]
  refine ⟨16366199407367927290650017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10910799604911951527100011 16366199407367927290650017)
  ·
    refine ⟨12274649555525945467987513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16366199407367927290650017 12274649555525945467987513)
    ·
      refine ⟨9205987166644459100990635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12274649555525945467987513 9205987166644459100990635)
      ·
        refine ⟨13808980749966688651485953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205987166644459100990635 13808980749966688651485953)
        ·
          refine ⟨10356735562475016488614465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13808980749966688651485953 10356735562475016488614465)
          ·
            refine ⟨7767551671856262366460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10356735562475016488614465 7767551671856262366460849)
            ·
              refine ⟨5825663753892196774845637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7767551671856262366460849 5825663753892196774845637)
              ·
                refine ⟨1092311953854786895283557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5825663753892196774845637 1092311953854786895283557)
                ·
                  refine ⟨204808491347772542865667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092311953854786895283557 204808491347772542865667)
                  ·
                    rfl

theorem cell20_448721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_448721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448721 prefixEnd_448721 := by exact prefixLift 448721
  have htrace : WordTrace (prefixWord ++ tailWord_448721) baseStart_448721 baseEnd_448721 := by
    simpa [prefixWord, tailWord_448721, baseEnd_448721] using wordTrace_append hprefix tailTrace_448721
  have hstable : (prefixWord ++ tailWord_448721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448721).length < 2 ^ (prefixWord ++ tailWord_448721).sum := by decide
  have hdescent : baseEnd_448721 < baseStart_448721 := by decide
  rcases family_descends (prefixWord ++ tailWord_448721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448776 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_448776 : Nat := 118140960795 + 448776 * 2 ^ 59
def prefixEnd_448776 : Nat := 4983230072969 + 3 ^ 40 * 448776 * 2
def baseEnd_448776 : Nat := 204833594846436796032109

theorem tailTrace_448776 : CollatzResearch.WordTrace tailWord_448776 prefixEnd_448776 204833594846436796032109 := by
  unfold tailWord_448776
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184102711084335841951091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10912136948112447789268121 8184102711084335841951091)
  ·
    refine ⟨12276154066626503762926637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8184102711084335841951091 12276154066626503762926637)
    ·
      refine ⟨4603557774984938911097489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12276154066626503762926637 4603557774984938911097489)
      ·
        refine ⟨3452668331238704183323117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4603557774984938911097489 3452668331238704183323117)
        ·
          refine ⟨1294750624214514068746169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3452668331238704183323117 1294750624214514068746169)
          ·
            refine ⟨971062968160885551559627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294750624214514068746169 971062968160885551559627)
            ·
              refine ⟨1456594452241328327339441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971062968160885551559627 1456594452241328327339441)
              ·
                refine ⟨1092445839180996245504581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456594452241328327339441 1092445839180996245504581)
                ·
                  refine ⟨204833594846436796032109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092445839180996245504581 204833594846436796032109)
                  ·
                    rfl

theorem cell20_448776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_448776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448776 prefixEnd_448776 := by exact prefixLift 448776
  have htrace : WordTrace (prefixWord ++ tailWord_448776) baseStart_448776 baseEnd_448776 := by
    simpa [prefixWord, tailWord_448776, baseEnd_448776] using wordTrace_append hprefix tailTrace_448776
  have hstable : (prefixWord ++ tailWord_448776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448776).length < 2 ^ (prefixWord ++ tailWord_448776).sum := by decide
  have hdescent : baseEnd_448776 < baseStart_448776 := by decide
  rcases family_descends (prefixWord ++ tailWord_448776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448835 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_448835 : Nat := 118140960795 + 448835 * 2 ^ 59
def prefixEnd_448835 : Nat := 4983230072969 + 3 ^ 40 * 448835 * 2
def baseEnd_448835 : Nat := 204860524054094813065201

theorem tailTrace_448835 : CollatzResearch.WordTrace tailWord_448835 prefixEnd_448835 204860524054094813065201 := by
  unfold tailWord_448835
  simp only [CollatzResearch.WordTrace]
  refine ⟨16370357328954924760299959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10913571552636616506866639 16370357328954924760299959)
  ·
    refine ⟨24555535993432387140449939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16370357328954924760299959 24555535993432387140449939)
    ·
      refine ⟨36833303990148580710674909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555535993432387140449939 36833303990148580710674909)
      ·
        refine ⟨13812488996305717766503091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36833303990148580710674909 13812488996305717766503091)
        ·
          refine ⟨20718733494458576649754637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13812488996305717766503091 20718733494458576649754637)
          ·
            refine ⟨7769525060421966243657989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20718733494458576649754637 7769525060421966243657989)
            ·
              refine ⟨1456785948829118670685873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7769525060421966243657989 1456785948829118670685873)
              ·
                refine ⟨1092589461621839003014405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456785948829118670685873 1092589461621839003014405)
                ·
                  refine ⟨204860524054094813065201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092589461621839003014405 204860524054094813065201)
                  ·
                    rfl

theorem cell20_448835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_448835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448835 prefixEnd_448835 := by exact prefixLift 448835
  have htrace : WordTrace (prefixWord ++ tailWord_448835) baseStart_448835 baseEnd_448835 := by
    simpa [prefixWord, tailWord_448835, baseEnd_448835] using wordTrace_append hprefix tailTrace_448835
  have hstable : (prefixWord ++ tailWord_448835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448835).length < 2 ^ (prefixWord ++ tailWord_448835).sum := by decide
  have hdescent : baseEnd_448835 < baseStart_448835 := by decide
  rcases family_descends (prefixWord ++ tailWord_448835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448880 : List Nat := [2, 1, 1, 1, 4, 3, 1, 7]
def baseStart_448880 : Nat := 118140960795 + 448880 * 2 ^ 59
def prefixEnd_448880 : Nat := 4983230072969 + 3 ^ 40 * 448880 * 2
def baseEnd_448880 : Nat := 68293687760091552188339

theorem tailTrace_448880 : CollatzResearch.WordTrace tailWord_448880 prefixEnd_448880 68293687760091552188339 := by
  unfold tailWord_448880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185999306895948722844047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10914665742527931630458729 8185999306895948722844047)
  ·
    refine ⟨12278998960343923084266071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8185999306895948722844047 12278998960343923084266071)
    ·
      refine ⟨18418498440515884626399107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12278998960343923084266071 18418498440515884626399107)
      ·
        refine ⟨27627747660773826939598661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18418498440515884626399107 27627747660773826939598661)
        ·
          refine ⟨5180202686395092551174749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27627747660773826939598661 5180202686395092551174749)
          ·
            refine ⟨1942576007398159706690531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5180202686395092551174749 1942576007398159706690531)
            ·
              refine ⟨2913864011097239560035797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942576007398159706690531 2913864011097239560035797)
              ·
                refine ⟨68293687760091552188339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2913864011097239560035797 68293687760091552188339)
                ·
                  rfl

theorem cell20_448880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_448880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448880 prefixEnd_448880 := by exact prefixLift 448880
  have htrace : WordTrace (prefixWord ++ tailWord_448880) baseStart_448880 baseEnd_448880 := by
    simpa [prefixWord, tailWord_448880, baseEnd_448880] using wordTrace_append hprefix tailTrace_448880
  have hstable : (prefixWord ++ tailWord_448880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448880).length < 2 ^ (prefixWord ++ tailWord_448880).sum := by decide
  have hdescent : baseEnd_448880 < baseStart_448880 := by decide
  rcases family_descends (prefixWord ++ tailWord_448880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448887 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_448887 : Nat := 118140960795 + 448887 * 2 ^ 59
def prefixEnd_448887 : Nat := 4983230072969 + 3 ^ 40 * 448887 * 2
def baseEnd_448887 : Nat := 204884258271013743331655

theorem tailTrace_448887 : CollatzResearch.WordTrace tailWord_448887 prefixEnd_448887 204884258271013743331655 := by
  unfold tailWord_448887
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372253924766537641192915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10914835949844358427461943 16372253924766537641192915)
  ·
    refine ⟨24558380887149806461789373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16372253924766537641192915 24558380887149806461789373)
    ·
      refine ⟨9209392832681177423171015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24558380887149806461789373 9209392832681177423171015)
      ·
        refine ⟨13814089249021766134756523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9209392832681177423171015 13814089249021766134756523)
        ·
          refine ⟨20721133873532649202134785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13814089249021766134756523 20721133873532649202134785)
          ·
            refine ⟨15540850405149486901601089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20721133873532649202134785 15540850405149486901601089)
            ·
              refine ⟨11655637803862115176200817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15540850405149486901601089 11655637803862115176200817)
              ·
                refine ⟨8741728352896586382150613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11655637803862115176200817 8741728352896586382150613)
                ·
                  refine ⟨204884258271013743331655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8741728352896586382150613 204884258271013743331655)
                  ·
                    rfl

theorem cell20_448887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_448887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448887 prefixEnd_448887 := by exact prefixLift 448887
  have htrace : WordTrace (prefixWord ++ tailWord_448887) baseStart_448887 baseEnd_448887 := by
    simpa [prefixWord, tailWord_448887, baseEnd_448887] using wordTrace_append hprefix tailTrace_448887
  have hstable : (prefixWord ++ tailWord_448887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448887).length < 2 ^ (prefixWord ++ tailWord_448887).sum := by decide
  have hdescent : baseEnd_448887 < baseStart_448887 := by decide
  rcases family_descends (prefixWord ++ tailWord_448887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448897 : List Nat := [1, 2, 4, 3, 1, 1, 2, 6]
def baseStart_448897 : Nat := 118140960795 + 448897 * 2 ^ 59
def prefixEnd_448897 : Nat := 4983230072969 + 3 ^ 40 * 448897 * 2
def baseEnd_448897 : Nat := 68296274181166050999427

theorem tailTrace_448897 : CollatzResearch.WordTrace tailWord_448897 prefixEnd_448897 68296274181166050999427 := by
  unfold tailWord_448897
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372618654730309349056945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10915079103153539566037963 16372618654730309349056945)
  ·
    refine ⟨12279463991047732011792709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16372618654730309349056945 12279463991047732011792709)
    ·
      refine ⟨2302399498321449752211133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12279463991047732011792709 2302399498321449752211133)
      ·
        refine ⟨863399811870543657079175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2302399498321449752211133 863399811870543657079175)
        ·
          refine ⟨1295099717805815485618763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863399811870543657079175 1295099717805815485618763)
          ·
            refine ⟨1942649576708723228428145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295099717805815485618763 1942649576708723228428145)
            ·
              refine ⟨1456987182531542421321109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1942649576708723228428145 1456987182531542421321109)
              ·
                refine ⟨68296274181166050999427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1456987182531542421321109 68296274181166050999427)
                ·
                  rfl

theorem cell20_448897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_448897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448897 prefixEnd_448897 := by exact prefixLift 448897
  have htrace : WordTrace (prefixWord ++ tailWord_448897) baseStart_448897 baseEnd_448897 := by
    simpa [prefixWord, tailWord_448897, baseEnd_448897] using wordTrace_append hprefix tailTrace_448897
  have hstable : (prefixWord ++ tailWord_448897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448897).length < 2 ^ (prefixWord ++ tailWord_448897).sum := by decide
  have hdescent : baseEnd_448897 < baseStart_448897 := by decide
  rcases family_descends (prefixWord ++ tailWord_448897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448935 : List Nat := [1, 1, 6, 1, 1, 2, 3, 5]
def baseStart_448935 : Nat := 118140960795 + 448935 * 2 ^ 59
def prefixEnd_448935 : Nat := 4983230072969 + 3 ^ 40 * 448935 * 2
def baseEnd_448935 : Nat := 68302055592979636577153

theorem tailTrace_448935 : CollatzResearch.WordTrace tailWord_448935 prefixEnd_448935 68302055592979636577153 := by
  unfold tailWord_448935
  simp only [CollatzResearch.WordTrace]
  refine ⟨16374004628592641838940259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10916003085728427892626839 16374004628592641838940259)
  ·
    refine ⟨24561006942888962758410389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16374004628592641838940259 24561006942888962758410389)
    ·
      refine ⟨1151297200447920129300487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24561006942888962758410389 1151297200447920129300487)
      ·
        refine ⟨1726945800671880193950731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151297200447920129300487 1726945800671880193950731)
        ·
          refine ⟨2590418701007820290926097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726945800671880193950731 2590418701007820290926097)
          ·
            refine ⟨1942814025755865218194573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2590418701007820290926097 1942814025755865218194573)
            ·
              refine ⟨728555259658449456822965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942814025755865218194573 728555259658449456822965)
              ·
                refine ⟨68302055592979636577153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 728555259658449456822965 68302055592979636577153)
                ·
                  rfl

theorem cell20_448935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_448935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448935 prefixEnd_448935 := by exact prefixLift 448935
  have htrace : WordTrace (prefixWord ++ tailWord_448935) baseStart_448935 baseEnd_448935 := by
    simpa [prefixWord, tailWord_448935, baseEnd_448935] using wordTrace_append hprefix tailTrace_448935
  have hstable : (prefixWord ++ tailWord_448935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448935).length < 2 ^ (prefixWord ++ tailWord_448935).sum := by decide
  have hdescent : baseEnd_448935 < baseStart_448935 := by decide
  rcases family_descends (prefixWord ++ tailWord_448935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448948 : List Nat := [2, 5, 2, 2, 1, 1, 3, 4]
def baseStart_448948 : Nat := 118140960795 + 448948 * 2 ^ 59
def prefixEnd_448948 : Nat := 4983230072969 + 3 ^ 40 * 448948 * 2
def baseEnd_448948 : Nat := 68304033444389547432691

theorem tailTrace_448948 : CollatzResearch.WordTrace tailWord_448948 prefixEnd_448948 68304033444389547432691 := by
  unfold tailWord_448948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187239388772772529581749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10916319185030363372775665 8187239388772772529581749)
  ·
    refine ⟨767553692697447424648289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8187239388772772529581749 767553692697447424648289)
    ·
      refine ⟨575665269523085568486217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 767553692697447424648289 575665269523085568486217)
      ·
        refine ⟨431748952142314176364663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575665269523085568486217 431748952142314176364663)
        ·
          refine ⟨647623428213471264546995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431748952142314176364663 647623428213471264546995)
          ·
            refine ⟨971435142320206896820493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647623428213471264546995 971435142320206896820493)
            ·
              refine ⟨364288178370077586307685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971435142320206896820493 364288178370077586307685)
              ·
                refine ⟨68304033444389547432691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364288178370077586307685 68304033444389547432691)
                ·
                  rfl

theorem cell20_448948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_448948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448948 prefixEnd_448948 := by exact prefixLift 448948
  have htrace : WordTrace (prefixWord ++ tailWord_448948) baseStart_448948 baseEnd_448948 := by
    simpa [prefixWord, tailWord_448948, baseEnd_448948] using wordTrace_append hprefix tailTrace_448948
  have hstable : (prefixWord ++ tailWord_448948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448948).length < 2 ^ (prefixWord ++ tailWord_448948).sum := by decide
  have hdescent : baseEnd_448948 < baseStart_448948 := by decide
  rcases family_descends (prefixWord ++ tailWord_448948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448963 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_448963 : Nat := 118140960795 + 448963 * 2 ^ 59
def prefixEnd_448963 : Nat := 4983230072969 + 3 ^ 40 * 448963 * 2
def baseEnd_448963 : Nat := 204918946741895256798011

theorem tailTrace_448963 : CollatzResearch.WordTrace tailWord_448963 prefixEnd_448963 204918946741895256798011 := by
  unfold tailWord_448963
  simp only [CollatzResearch.WordTrace]
  refine ⟨16375025872491202620959543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10916683914994135080639695 16375025872491202620959543)
  ·
    refine ⟨24562538808736803931439315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16375025872491202620959543 24562538808736803931439315)
    ·
      refine ⟨36843808213105205897158973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24562538808736803931439315 36843808213105205897158973)
      ·
        refine ⟨13816428079914452211434615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36843808213105205897158973 13816428079914452211434615)
        ·
          refine ⟨20724642119871678317151923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13816428079914452211434615 20724642119871678317151923)
          ·
            refine ⟨31086963179807517475727885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20724642119871678317151923 31086963179807517475727885)
            ·
              refine ⟨11657611192427819053397957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31086963179807517475727885 11657611192427819053397957)
              ·
                refine ⟨2185802098580216072512117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11657611192427819053397957 2185802098580216072512117)
                ·
                  refine ⟨204918946741895256798011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185802098580216072512117 204918946741895256798011)
                  ·
                    rfl

theorem cell20_448963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_448963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_448963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_448963 prefixEnd_448963 := by exact prefixLift 448963
  have htrace : WordTrace (prefixWord ++ tailWord_448963) baseStart_448963 baseEnd_448963 := by
    simpa [prefixWord, tailWord_448963, baseEnd_448963] using wordTrace_append hprefix tailTrace_448963
  have hstable : (prefixWord ++ tailWord_448963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448963).length < 2 ^ (prefixWord ++ tailWord_448963).sum := by decide
  have hdescent : baseEnd_448963 < baseStart_448963 := by decide
  rcases family_descends (prefixWord ++ tailWord_448963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449038 : List Nat := [4, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_449038 : Nat := 118140960795 + 449038 * 2 ^ 59
def prefixEnd_449038 : Nat := 4983230072969 + 3 ^ 40 * 449038 * 2
def baseEnd_449038 : Nat := 204953178785528329297705

theorem tailTrace_449038 : CollatzResearch.WordTrace tailWord_449038 prefixEnd_449038 204953178785528329297705 := by
  unfold tailWord_449038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047220168402436303742471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10918507564812993619959845 2047220168402436303742471)
  ·
    refine ⟨3070830252603654455613707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2047220168402436303742471 3070830252603654455613707)
    ·
      refine ⟨4606245378905481683420561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070830252603654455613707 4606245378905481683420561)
      ·
        refine ⟨3454684034179111262565421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4606245378905481683420561 3454684034179111262565421)
        ·
          refine ⟨1295506512817166723462033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3454684034179111262565421 1295506512817166723462033)
          ·
            refine ⟨971629884612875042596525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295506512817166723462033 971629884612875042596525)
            ·
              refine ⟨364361206729828140973697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971629884612875042596525 364361206729828140973697)
              ·
                refine ⟨273270905047371105730273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364361206729828140973697 273270905047371105730273)
                ·
                  refine ⟨204953178785528329297705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273270905047371105730273 204953178785528329297705)
                  ·
                    rfl

theorem cell20_449038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_449038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449038 prefixEnd_449038 := by exact prefixLift 449038
  have htrace : WordTrace (prefixWord ++ tailWord_449038) baseStart_449038 baseEnd_449038 := by
    simpa [prefixWord, tailWord_449038, baseEnd_449038] using wordTrace_append hprefix tailTrace_449038
  have hstable : (prefixWord ++ tailWord_449038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449038).length < 2 ^ (prefixWord ++ tailWord_449038).sum := by decide
  have hdescent : baseEnd_449038 < baseStart_449038 := by decide
  rcases family_descends (prefixWord ++ tailWord_449038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449052 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_449052 : Nat := 118140960795 + 449052 * 2 ^ 59
def prefixEnd_449052 : Nat := 4983230072969 + 3 ^ 40 * 449052 * 2
def baseEnd_449052 : Nat := 204959568767006502830981

theorem tailTrace_449052 : CollatzResearch.WordTrace tailWord_449052 prefixEnd_449052 204959568767006502830981 := by
  unfold tailWord_449052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189135984584385410474705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10918847979445847213966273 8189135984584385410474705)
  ·
    refine ⟨6141851988438289057856029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8189135984584385410474705 6141851988438289057856029)
    ·
      refine ⟨2303194495664358396696011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6141851988438289057856029 2303194495664358396696011)
      ·
        refine ⟨3454791743496537595044017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303194495664358396696011 3454791743496537595044017)
        ·
          refine ⟨2591093807622403196283013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3454791743496537595044017 2591093807622403196283013)
          ·
            refine ⟨485830088929200599303065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2591093807622403196283013 485830088929200599303065)
            ·
              refine ⟨364372566696900449477299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485830088929200599303065 364372566696900449477299)
              ·
                refine ⟨546558850045350674215949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364372566696900449477299 546558850045350674215949)
                ·
                  refine ⟨204959568767006502830981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546558850045350674215949 204959568767006502830981)
                  ·
                    rfl

theorem cell20_449052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_449052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449052 prefixEnd_449052 := by exact prefixLift 449052
  have htrace : WordTrace (prefixWord ++ tailWord_449052) baseStart_449052 baseEnd_449052 := by
    simpa [prefixWord, tailWord_449052, baseEnd_449052] using wordTrace_append hprefix tailTrace_449052
  have hstable : (prefixWord ++ tailWord_449052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449052).length < 2 ^ (prefixWord ++ tailWord_449052).sum := by decide
  have hdescent : baseEnd_449052 < baseStart_449052 := by decide
  rcases family_descends (prefixWord ++ tailWord_449052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449080 : List Nat := [2, 1, 2, 1, 4, 1, 2, 5, 2]
def baseStart_449080 : Nat := 118140960795 + 449080 * 2 ^ 59
def prefixEnd_449080 : Nat := 4983230072969 + 3 ^ 40 * 449080 * 2
def baseEnd_449080 : Nat := 204972348729962849897533

theorem tailTrace_449080 : CollatzResearch.WordTrace tailWord_449080 prefixEnd_449080 204972348729962849897533 := by
  unfold tailWord_449080
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189646606533665801484347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10919528808711554401979129 8189646606533665801484347)
  ·
    refine ⟨12284469909800498702226521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8189646606533665801484347 12284469909800498702226521)
    ·
      refine ⟨9213352432350374026669891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12284469909800498702226521 9213352432350374026669891)
      ·
        refine ⟨13820028648525561040004837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9213352432350374026669891 13820028648525561040004837)
        ·
          refine ⟨2591255371598542695000907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13820028648525561040004837 2591255371598542695000907)
          ·
            refine ⟨3886883057397814042501361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591255371598542695000907 3886883057397814042501361)
            ·
              refine ⟨2915162293048360531876021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886883057397814042501361 2915162293048360531876021)
              ·
                refine ⟨273296464973283799863377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2915162293048360531876021 273296464973283799863377)
                ·
                  refine ⟨204972348729962849897533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273296464973283799863377 204972348729962849897533)
                  ·
                    rfl

theorem cell20_449080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_449080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449080 prefixEnd_449080 := by exact prefixLift 449080
  have htrace : WordTrace (prefixWord ++ tailWord_449080) baseStart_449080 baseEnd_449080 := by
    simpa [prefixWord, tailWord_449080, baseEnd_449080] using wordTrace_append hprefix tailTrace_449080
  have hstable : (prefixWord ++ tailWord_449080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449080).length < 2 ^ (prefixWord ++ tailWord_449080).sum := by decide
  have hdescent : baseEnd_449080 < baseStart_449080 := by decide
  rcases family_descends (prefixWord ++ tailWord_449080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449156 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_449156 : Nat := 118140960795 + 449156 * 2 ^ 59
def prefixEnd_449156 : Nat := 4983230072969 + 3 ^ 40 * 449156 * 2
def baseEnd_449156 : Nat := 205007037200844363363889

theorem tailTrace_449156 : CollatzResearch.WordTrace tailWord_449156 prefixEnd_449156 205007037200844363363889 := by
  unfold tailWord_449156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191032580395998291367661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10921376773861331055156881 8191032580395998291367661)
  ·
    refine ⟨3071637217648499359262873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8191032580395998291367661 3071637217648499359262873)
    ·
      refine ⟨2303727913236374519447155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3071637217648499359262873 2303727913236374519447155)
      ·
        refine ⟨3455591869854561779170733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303727913236374519447155 3455591869854561779170733)
        ·
          refine ⟨1295846951195460667189025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3455591869854561779170733 1295846951195460667189025)
          ·
            refine ⟨971885213396595500391769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295846951195460667189025 971885213396595500391769)
            ·
              refine ⟨728913910047446625293827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971885213396595500391769 728913910047446625293827)
              ·
                refine ⟨1093370865071169937940741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728913910047446625293827 1093370865071169937940741)
                ·
                  refine ⟨205007037200844363363889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093370865071169937940741 205007037200844363363889)
                  ·
                    rfl

theorem cell20_449156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_449156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449156 prefixEnd_449156 := by exact prefixLift 449156
  have htrace : WordTrace (prefixWord ++ tailWord_449156) baseStart_449156 baseEnd_449156 := by
    simpa [prefixWord, tailWord_449156, baseEnd_449156] using wordTrace_append hprefix tailTrace_449156
  have hstable : (prefixWord ++ tailWord_449156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449156).length < 2 ^ (prefixWord ++ tailWord_449156).sum := by decide
  have hdescent : baseEnd_449156 < baseStart_449156 := by decide
  rcases family_descends (prefixWord ++ tailWord_449156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449180 : List Nat := [2, 2, 3, 2, 2, 3, 2, 4]
def baseStart_449180 : Nat := 118140960795 + 449180 * 2 ^ 59
def prefixEnd_449180 : Nat := 4983230072969 + 3 ^ 40 * 449180 * 2
def baseEnd_449180 : Nat := 68339330484935648854597

theorem tailTrace_449180 : CollatzResearch.WordTrace tailWord_449180 prefixEnd_449180 68339330484935648854597 := by
  unfold tailWord_449180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191470256352524340804497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10921960341803365787739329 8191470256352524340804497)
  ·
    refine ⟨6143602692264393255603373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8191470256352524340804497 6143602692264393255603373)
    ·
      refine ⟨2303851009599147470851265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6143602692264393255603373 2303851009599147470851265)
      ·
        refine ⟨1727888257199360603138449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2303851009599147470851265 1727888257199360603138449)
        ·
          refine ⟨1295916192899520452353837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1727888257199360603138449 1295916192899520452353837)
          ·
            refine ⟨485968572337320169632689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1295916192899520452353837 485968572337320169632689)
            ·
              refine ⟨364476429252990127224517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485968572337320169632689 364476429252990127224517)
              ·
                refine ⟨68339330484935648854597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364476429252990127224517 68339330484935648854597)
                ·
                  rfl

theorem cell20_449180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_449180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449180 prefixEnd_449180 := by exact prefixLift 449180
  have htrace : WordTrace (prefixWord ++ tailWord_449180) baseStart_449180 baseEnd_449180 := by
    simpa [prefixWord, tailWord_449180, baseEnd_449180] using wordTrace_append hprefix tailTrace_449180
  have hstable : (prefixWord ++ tailWord_449180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449180).length < 2 ^ (prefixWord ++ tailWord_449180).sum := by decide
  have hdescent : baseEnd_449180 < baseStart_449180 := by decide
  rcases family_descends (prefixWord ++ tailWord_449180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449215 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_449215 : Nat := 118140960795 + 449215 * 2 ^ 59
def prefixEnd_449215 : Nat := 4983230072969 + 3 ^ 40 * 449215 * 2
def baseEnd_449215 : Nat := 205033966408502380396981

theorem tailTrace_449215 : CollatzResearch.WordTrace tailWord_449215 prefixEnd_449215 205033966408502380396981 := by
  unfold tailWord_449215
  simp only [CollatzResearch.WordTrace]
  refine ⟨16384217067578249659133099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10922811378385499772755399 16384217067578249659133099)
  ·
    refine ⟨24576325601367374488699649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16384217067578249659133099 24576325601367374488699649)
    ·
      refine ⟨18432244201025530866524737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24576325601367374488699649 18432244201025530866524737)
      ·
        refine ⟨13824183150769148149893553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18432244201025530866524737 13824183150769148149893553)
        ·
          refine ⟨10368137363076861112420165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13824183150769148149893553 10368137363076861112420165)
          ·
            refine ⟨1944025755576911458578781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10368137363076861112420165 1944025755576911458578781)
            ·
              refine ⟨729009658341341796967043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1944025755576911458578781 729009658341341796967043)
              ·
                refine ⟨1093514487512012695450565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729009658341341796967043 1093514487512012695450565)
                ·
                  refine ⟨205033966408502380396981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093514487512012695450565 205033966408502380396981)
                  ·
                    rfl

theorem cell20_449215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_449215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449215 prefixEnd_449215 := by exact prefixLift 449215
  have htrace : WordTrace (prefixWord ++ tailWord_449215) baseStart_449215 baseEnd_449215 := by
    simpa [prefixWord, tailWord_449215, baseEnd_449215] using wordTrace_append hprefix tailTrace_449215
  have hstable : (prefixWord ++ tailWord_449215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449215).length < 2 ^ (prefixWord ++ tailWord_449215).sum := by decide
  have hdescent : baseEnd_449215 < baseStart_449215 := by decide
  rcases family_descends (prefixWord ++ tailWord_449215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449266 : List Nat := [3, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_449266 : Nat := 118140960795 + 449266 * 2 ^ 59
def prefixEnd_449266 : Nat := 4983230072969 + 3 ^ 40 * 449266 * 2
def baseEnd_449266 : Nat := 205057244198172869696773

theorem tailTrace_449266 : CollatzResearch.WordTrace tailWord_449266 prefixEnd_449266 205057244198172869696773 := by
  unfold tailWord_449266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096519297598371342309913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10924051460262323579493101 4096519297598371342309913)
  ·
    refine ⟨3072389473198778506732435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4096519297598371342309913 3072389473198778506732435)
    ·
      refine ⟨4608584209798167760098653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3072389473198778506732435 4608584209798167760098653)
      ·
        refine ⟨1728219078674312910036995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4608584209798167760098653 1728219078674312910036995)
        ·
          refine ⟨2592328618011469365055493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728219078674312910036995 2592328618011469365055493)
          ·
            refine ⟨486061615877150505947905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2592328618011469365055493 486061615877150505947905)
            ·
              refine ⟨364546211907862879460929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486061615877150505947905 364546211907862879460929)
              ·
                refine ⟨273409658930897159595697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364546211907862879460929 273409658930897159595697)
                ·
                  refine ⟨205057244198172869696773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273409658930897159595697 205057244198172869696773)
                  ·
                    rfl

theorem cell20_449266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_449266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449266 prefixEnd_449266 := by exact prefixLift 449266
  have htrace : WordTrace (prefixWord ++ tailWord_449266) baseStart_449266 baseEnd_449266 := by
    simpa [prefixWord, tailWord_449266, baseEnd_449266] using wordTrace_append hprefix tailTrace_449266
  have hstable : (prefixWord ++ tailWord_449266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449266).length < 2 ^ (prefixWord ++ tailWord_449266).sum := by decide
  have hdescent : baseEnd_449266 < baseStart_449266 := by decide
  rcases family_descends (prefixWord ++ tailWord_449266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449284 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_449284 : Nat := 118140960795 + 449284 * 2 ^ 59
def prefixEnd_449284 : Nat := 4983230072969 + 3 ^ 40 * 449284 * 2
def baseEnd_449284 : Nat := 205065459888644807096699

theorem tailTrace_449284 : CollatzResearch.WordTrace tailWord_449284 prefixEnd_449284 205065459888644807096699 := by
  unfold tailWord_449284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8193366852164137221697453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10924489136218849628929937 8193366852164137221697453)
  ·
    refine ⟨3072512569561551458136545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8193366852164137221697453 3072512569561551458136545)
    ·
      refine ⟨2304384427171163593602409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3072512569561551458136545 2304384427171163593602409)
      ·
        refine ⟨1728288320378372695201807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2304384427171163593602409 1728288320378372695201807)
        ·
          refine ⟨2592432480567559042802711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728288320378372695201807 2592432480567559042802711)
          ·
            refine ⟨3888648720851338564204067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592432480567559042802711 3888648720851338564204067)
            ·
              refine ⟨5832973081277007846306101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888648720851338564204067 5832973081277007846306101)
              ·
                refine ⟨546841226369719485591197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5832973081277007846306101 546841226369719485591197)
                ·
                  refine ⟨205065459888644807096699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546841226369719485591197 205065459888644807096699)
                  ·
                    rfl

theorem cell20_449284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_449284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449284 prefixEnd_449284 := by exact prefixLift 449284
  have htrace : WordTrace (prefixWord ++ tailWord_449284) baseStart_449284 baseEnd_449284 := by
    simpa [prefixWord, tailWord_449284, baseEnd_449284] using wordTrace_append hprefix tailTrace_449284
  have hstable : (prefixWord ++ tailWord_449284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449284).length < 2 ^ (prefixWord ++ tailWord_449284).sum := by decide
  have hdescent : baseEnd_449284 < baseStart_449284 := by decide
  rcases family_descends (prefixWord ++ tailWord_449284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449308 : List Nat := [2, 2, 3, 1, 1, 3, 1, 5, 2]
def baseStart_449308 : Nat := 118140960795 + 449308 * 2 ^ 59
def prefixEnd_449308 : Nat := 4983230072969 + 3 ^ 40 * 449308 * 2
def baseEnd_449308 : Nat := 205076414142607390296601

theorem tailTrace_449308 : CollatzResearch.WordTrace tailWord_449308 prefixEnd_449308 205076414142607390296601 := by
  unfold tailWord_449308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8193804528120663271134289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10925072704160884361512385 8193804528120663271134289)
  ·
    refine ⟨6145353396090497453350717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8193804528120663271134289 6145353396090497453350717)
    ·
      refine ⟨2304507523533936545006519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6145353396090497453350717 2304507523533936545006519)
      ·
        refine ⟨3456761285300904817509779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304507523533936545006519 3456761285300904817509779)
        ·
          refine ⟨5185141927951357226264669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456761285300904817509779 5185141927951357226264669)
          ·
            refine ⟨1944428222981758959849251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5185141927951357226264669 1944428222981758959849251)
            ·
              refine ⟨2916642334472638439773877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944428222981758959849251 2916642334472638439773877)
              ·
                refine ⟨273435218856809853728801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2916642334472638439773877 273435218856809853728801)
                ·
                  refine ⟨205076414142607390296601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273435218856809853728801 205076414142607390296601)
                  ·
                    rfl

theorem cell20_449308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_449308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449308 prefixEnd_449308 := by exact prefixLift 449308
  have htrace : WordTrace (prefixWord ++ tailWord_449308) baseStart_449308 baseEnd_449308 := by
    simpa [prefixWord, tailWord_449308, baseEnd_449308] using wordTrace_append hprefix tailTrace_449308
  have hstable : (prefixWord ++ tailWord_449308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449308).length < 2 ^ (prefixWord ++ tailWord_449308).sum := by decide
  have hdescent : baseEnd_449308 < baseStart_449308 := by decide
  rcases family_descends (prefixWord ++ tailWord_449308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449329 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_449329 : Nat := 118140960795 + 449329 * 2 ^ 59
def prefixEnd_449329 : Nat := 4983230072969 + 3 ^ 40 * 449329 * 2
def baseEnd_449329 : Nat := 205085999114824650596515

theorem tailTrace_449329 : CollatzResearch.WordTrace tailWord_449329 prefixEnd_449329 205085999114824650596515 := by
  unfold tailWord_449329
  simp only [CollatzResearch.WordTrace]
  refine ⟨16388374989165247128783041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10925583326110164752522027 16388374989165247128783041)
  ·
    refine ⟨12291281241873935346587281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16388374989165247128783041 12291281241873935346587281)
    ·
      refine ⟨9218460931405451509940461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12291281241873935346587281 9218460931405451509940461)
      ·
        refine ⟨3456922849277044316227673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9218460931405451509940461 3456922849277044316227673)
        ·
          refine ⟨2592692136957783237170755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3456922849277044316227673 2592692136957783237170755)
          ·
            refine ⟨3889038205436674855756133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592692136957783237170755 3889038205436674855756133)
            ·
              refine ⟨729194663519376535454275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3889038205436674855756133 729194663519376535454275)
              ·
                refine ⟨1093791995279064803181413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729194663519376535454275 1093791995279064803181413)
                ·
                  refine ⟨205085999114824650596515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093791995279064803181413 205085999114824650596515)
                  ·
                    rfl

theorem cell20_449329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_449329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449329 prefixEnd_449329 := by exact prefixLift 449329
  have htrace : WordTrace (prefixWord ++ tailWord_449329) baseStart_449329 baseEnd_449329 := by
    simpa [prefixWord, tailWord_449329, baseEnd_449329] using wordTrace_append hprefix tailTrace_449329
  have hstable : (prefixWord ++ tailWord_449329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449329).length < 2 ^ (prefixWord ++ tailWord_449329).sum := by decide
  have hdescent : baseEnd_449329 < baseStart_449329 := by decide
  rcases family_descends (prefixWord ++ tailWord_449329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449353 : List Nat := [1, 2, 1, 1, 2, 7, 2, 4]
def baseStart_449353 : Nat := 118140960795 + 449353 * 2 ^ 59
def prefixEnd_449353 : Nat := 4983230072969 + 3 ^ 40 * 449353 * 2
def baseEnd_449353 : Nat := 68365651122929077932139

theorem tailTrace_449353 : CollatzResearch.WordTrace tailWord_449353 prefixEnd_449353 68365651122929077932139 := by
  unfold tailWord_449353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389250341078299227656713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10926166894052199485104475 16389250341078299227656713)
  ·
    refine ⟨12291937755808724420742535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16389250341078299227656713 12291937755808724420742535)
    ·
      refine ⟨18437906633713086631113803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12291937755808724420742535 18437906633713086631113803)
      ·
        refine ⟨27656859950569629946670705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18437906633713086631113803 27656859950569629946670705)
        ·
          refine ⟨20742644962927222460003029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27656859950569629946670705 20742644962927222460003029)
          ·
            refine ⟨486155741318606776406321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20742644962927222460003029 486155741318606776406321)
            ·
              refine ⟨364616805988955082304741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486155741318606776406321 364616805988955082304741)
              ·
                refine ⟨68365651122929077932139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364616805988955082304741 68365651122929077932139)
                ·
                  rfl

theorem cell20_449353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_449353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449353 prefixEnd_449353 := by exact prefixLift 449353
  have htrace : WordTrace (prefixWord ++ tailWord_449353) baseStart_449353 baseEnd_449353 := by
    simpa [prefixWord, tailWord_449353, baseEnd_449353] using wordTrace_append hprefix tailTrace_449353
  have hstable : (prefixWord ++ tailWord_449353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449353).length < 2 ^ (prefixWord ++ tailWord_449353).sum := by decide
  have hdescent : baseEnd_449353 < baseStart_449353 := by decide
  rcases family_descends (prefixWord ++ tailWord_449353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449381 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_449381 : Nat := 118140960795 + 449381 * 2 ^ 59
def prefixEnd_449381 : Nat := 4983230072969 + 3 ^ 40 * 449381 * 2
def baseEnd_449381 : Nat := 205109733331743580862969

theorem tailTrace_449381 : CollatzResearch.WordTrace tailWord_449381 prefixEnd_449381 205109733331743580862969 := by
  unfold tailWord_449381
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390271584976860009675997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10926847723317906673117331 16390271584976860009675997)
  ·
    refine ⟨6146351844366322503628499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16390271584976860009675997 6146351844366322503628499)
    ·
      refine ⟨9219527766549483755442749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146351844366322503628499 9219527766549483755442749)
      ·
        refine ⟨3457322912456056408291031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9219527766549483755442749 3457322912456056408291031)
        ·
          refine ⟨5185984368684084612436547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457322912456056408291031 5185984368684084612436547)
          ·
            refine ⟨7778976553026126918654821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185984368684084612436547 7778976553026126918654821)
            ·
              refine ⟨1458558103692398797247779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7778976553026126918654821 1458558103692398797247779)
              ·
                refine ⟨2187837155538598195871669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458558103692398797247779 2187837155538598195871669)
                ·
                  refine ⟨205109733331743580862969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187837155538598195871669 205109733331743580862969)
                  ·
                    rfl

theorem cell20_449381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_449381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449381 prefixEnd_449381 := by exact prefixLift 449381
  have htrace : WordTrace (prefixWord ++ tailWord_449381) baseStart_449381 baseEnd_449381 := by
    simpa [prefixWord, tailWord_449381, baseEnd_449381] using wordTrace_append hprefix tailTrace_449381
  have hstable : (prefixWord ++ tailWord_449381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449381).length < 2 ^ (prefixWord ++ tailWord_449381).sum := by decide
  have hdescent : baseEnd_449381 < baseStart_449381 := by decide
  rcases family_descends (prefixWord ++ tailWord_449381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449384 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_449384 : Nat := 118140960795 + 449384 * 2 ^ 59
def prefixEnd_449384 : Nat := 4983230072969 + 3 ^ 40 * 449384 * 2
def baseEnd_449384 : Nat := 205111102613488903762957

theorem tailTrace_449384 : CollatzResearch.WordTrace tailWord_449384 prefixEnd_449384 205111102613488903762957 := by
  unfold tailWord_449384
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195190501982995761017603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10926920669310661014690137 8195190501982995761017603)
  ·
    refine ⟨12292785752974493641526405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195190501982995761017603 12292785752974493641526405)
    ·
      refine ⟨2304897328682717557786201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12292785752974493641526405 2304897328682717557786201)
      ·
        refine ⟨1728672996512038168339651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2304897328682717557786201 1728672996512038168339651)
        ·
          refine ⟨2593009494768057252509477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728672996512038168339651 2593009494768057252509477)
          ·
            refine ⟨486189280269010734845527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2593009494768057252509477 486189280269010734845527)
            ·
              refine ⟨729283920403516102268291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486189280269010734845527 729283920403516102268291)
              ·
                refine ⟨1093925880605274153402437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729283920403516102268291 1093925880605274153402437)
                ·
                  refine ⟨205111102613488903762957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093925880605274153402437 205111102613488903762957)
                  ·
                    rfl

theorem cell20_449384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_449384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449384 prefixEnd_449384 := by exact prefixLift 449384
  have htrace : WordTrace (prefixWord ++ tailWord_449384) baseStart_449384 baseEnd_449384 := by
    simpa [prefixWord, tailWord_449384, baseEnd_449384] using wordTrace_append hprefix tailTrace_449384
  have hstable : (prefixWord ++ tailWord_449384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449384).length < 2 ^ (prefixWord ++ tailWord_449384).sum := by decide
  have hdescent : baseEnd_449384 < baseStart_449384 := by decide
  rcases family_descends (prefixWord ++ tailWord_449384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449395 : List Nat := [1, 1, 1, 2, 2, 1, 5, 7]
def baseStart_449395 : Nat := 118140960795 + 449395 * 2 ^ 59
def prefixEnd_449395 : Nat := 4983230072969 + 3 ^ 40 * 449395 * 2
def baseEnd_449395 : Nat := 68372041104407251465415

theorem tailTrace_449395 : CollatzResearch.WordTrace tailWord_449395 prefixEnd_449395 68372041104407251465415 := by
  unfold tailWord_449395
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390782206926140400685639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10927188137950760267123759 16390782206926140400685639)
  ·
    refine ⟨24586173310389210601028459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16390782206926140400685639 24586173310389210601028459)
    ·
      refine ⟨36879259965583815901542689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24586173310389210601028459 36879259965583815901542689)
      ·
        refine ⟨27659444974187861926157017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36879259965583815901542689 27659444974187861926157017)
        ·
          refine ⟨20744583730640896444617763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27659444974187861926157017 20744583730640896444617763)
          ·
            refine ⟨31116875595961344666926645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20744583730640896444617763 31116875595961344666926645)
            ·
              refine ⟨2917207087121376062524373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31116875595961344666926645 2917207087121376062524373)
              ·
                refine ⟨68372041104407251465415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2917207087121376062524373 68372041104407251465415)
                ·
                  rfl

theorem cell20_449395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_449395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449395 prefixEnd_449395 := by exact prefixLift 449395
  have htrace : WordTrace (prefixWord ++ tailWord_449395) baseStart_449395 baseEnd_449395 := by
    simpa [prefixWord, tailWord_449395, baseEnd_449395] using wordTrace_append hprefix tailTrace_449395
  have hstable : (prefixWord ++ tailWord_449395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449395).length < 2 ^ (prefixWord ++ tailWord_449395).sum := by decide
  have hdescent : baseEnd_449395 < baseStart_449395 := by decide
  rcases family_descends (prefixWord ++ tailWord_449395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449439 : List Nat := [1, 1, 2, 5, 2, 1, 4, 2, 2]
def baseStart_449439 : Nat := 118140960795 + 449439 * 2 ^ 59
def prefixEnd_449439 : Nat := 4983230072969 + 3 ^ 40 * 449439 * 2
def baseEnd_449439 : Nat := 205136206112153156929399

theorem tailTrace_449439 : CollatzResearch.WordTrace tailWord_449439 prefixEnd_449439 205136206112153156929399 := by
  unfold tailWord_449439
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392387018766735915287371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10928258012511157276858247 16392387018766735915287371)
  ·
    refine ⟨24588580528150103872931057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16392387018766735915287371 24588580528150103872931057)
    ·
      refine ⟨18441435396112577904698293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24588580528150103872931057 18441435396112577904698293)
      ·
        refine ⟨1728884568385554178565465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18441435396112577904698293 1728884568385554178565465)
        ·
          refine ⟨1296663426289165633924099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1728884568385554178565465 1296663426289165633924099)
          ·
            refine ⟨1944995139433748450886149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296663426289165633924099 1944995139433748450886149)
            ·
              refine ⟨364686588643827834541153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1944995139433748450886149 364686588643827834541153)
              ·
                refine ⟨273514941482870875905865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364686588643827834541153 273514941482870875905865)
                ·
                  refine ⟨205136206112153156929399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273514941482870875905865 205136206112153156929399)
                  ·
                    rfl

theorem cell20_449439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 2].length) (baseStart_449439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449439 prefixEnd_449439 := by exact prefixLift 449439
  have htrace : WordTrace (prefixWord ++ tailWord_449439) baseStart_449439 baseEnd_449439 := by
    simpa [prefixWord, tailWord_449439, baseEnd_449439] using wordTrace_append hprefix tailTrace_449439
  have hstable : (prefixWord ++ tailWord_449439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449439).length < 2 ^ (prefixWord ++ tailWord_449439).sum := by decide
  have hdescent : baseEnd_449439 < baseStart_449439 := by decide
  rcases family_descends (prefixWord ++ tailWord_449439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449460 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_449460 : Nat := 118140960795 + 449460 * 2 ^ 59
def prefixEnd_449460 : Nat := 4983230072969 + 3 ^ 40 * 449460 * 2
def baseEnd_449460 : Nat := 205145791084370417229313

theorem tailTrace_449460 : CollatzResearch.WordTrace tailWord_449460 prefixEnd_449460 205145791084370417229313 := by
  unfold tailWord_449460
  simp only [CollatzResearch.WordTrace]
  refine ⟨8196576475845328250900917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10928768634460437667867889 8196576475845328250900917)
  ·
    refine ⟨768429044610499523521961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8196576475845328250900917 768429044610499523521961)
    ·
      refine ⟨576321783457874642641471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 768429044610499523521961 576321783457874642641471)
      ·
        refine ⟨864482675186811963962207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576321783457874642641471 864482675186811963962207)
        ·
          refine ⟨1296724012780217945943311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864482675186811963962207 1296724012780217945943311)
          ·
            refine ⟨1945086019170326918914967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296724012780217945943311 1945086019170326918914967)
            ·
              refine ⟨2917629028755490378372451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945086019170326918914967 2917629028755490378372451)
              ·
                refine ⟨4376443543133235567558677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917629028755490378372451 4376443543133235567558677)
                ·
                  refine ⟨205145791084370417229313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4376443543133235567558677 205145791084370417229313)
                  ·
                    rfl

theorem cell20_449460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_449460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449460 prefixEnd_449460 := by exact prefixLift 449460
  have htrace : WordTrace (prefixWord ++ tailWord_449460) baseStart_449460 baseEnd_449460 := by
    simpa [prefixWord, tailWord_449460, baseEnd_449460] using wordTrace_append hprefix tailTrace_449460
  have hstable : (prefixWord ++ tailWord_449460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449460).length < 2 ^ (prefixWord ++ tailWord_449460).sum := by decide
  have hdescent : baseEnd_449460 < baseStart_449460 := by decide
  rcases family_descends (prefixWord ++ tailWord_449460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449464 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_449464 : Nat := 118140960795 + 449464 * 2 ^ 59
def prefixEnd_449464 : Nat := 4983230072969 + 3 ^ 40 * 449464 * 2
def baseEnd_449464 : Nat := 205147616793364181095963

theorem tailTrace_449464 : CollatzResearch.WordTrace tailWord_449464 prefixEnd_449464 205147616793364181095963 := by
  unfold tailWord_449464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8196649421838082592473723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10928865895784110123298297 8196649421838082592473723)
  ·
    refine ⟨12294974132757123888710585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8196649421838082592473723 12294974132757123888710585)
    ·
      refine ⟨9221230599567842916532939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12294974132757123888710585 9221230599567842916532939)
      ·
        refine ⟨13831845899351764374799409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9221230599567842916532939 13831845899351764374799409)
        ·
          refine ⟨10373884424513823281099557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13831845899351764374799409 10373884424513823281099557)
          ·
            refine ⟨1945103329596341865206167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10373884424513823281099557 1945103329596341865206167)
            ·
              refine ⟨2917654994394512797809251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945103329596341865206167 2917654994394512797809251)
              ·
                refine ⟨4376482491591769196713877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917654994394512797809251 4376482491591769196713877)
                ·
                  refine ⟨205147616793364181095963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4376482491591769196713877 205147616793364181095963)
                  ·
                    rfl

theorem cell20_449464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_449464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449464 prefixEnd_449464 := by exact prefixLift 449464
  have htrace : WordTrace (prefixWord ++ tailWord_449464) baseStart_449464 baseEnd_449464 := by
    simpa [prefixWord, tailWord_449464, baseEnd_449464] using wordTrace_append hprefix tailTrace_449464
  have hstable : (prefixWord ++ tailWord_449464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449464).length < 2 ^ (prefixWord ++ tailWord_449464).sum := by decide
  have hdescent : baseEnd_449464 < baseStart_449464 := by decide
  rcases family_descends (prefixWord ++ tailWord_449464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449495 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 3]
def baseStart_449495 : Nat := 118140960795 + 449495 * 2 ^ 59
def prefixEnd_449495 : Nat := 4983230072969 + 3 ^ 40 * 449495 * 2
def baseEnd_449495 : Nat := 205161766038065851062503

theorem tailTrace_449495 : CollatzResearch.WordTrace tailWord_449495 prefixEnd_449495 205161766038065851062503 := by
  unfold tailWord_449495
  simp only [CollatzResearch.WordTrace]
  refine ⟨16394429506563857479325939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10929619671042571652883959 16394429506563857479325939)
  ·
    refine ⟨24591644259845786218988909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16394429506563857479325939 24591644259845786218988909)
    ·
      refine ⟨9221866597442169832120841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24591644259845786218988909 9221866597442169832120841)
      ·
        refine ⟨6916399948081627374090631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9221866597442169832120841 6916399948081627374090631)
        ·
          refine ⟨10374599922122441061135947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6916399948081627374090631 10374599922122441061135947)
          ·
            refine ⟨15561899883183661591703921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10374599922122441061135947 15561899883183661591703921)
            ·
              refine ⟨11671424912387746193777941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15561899883183661591703921 11671424912387746193777941)
              ·
                refine ⟨547098042768175602833341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11671424912387746193777941 547098042768175602833341)
                ·
                  refine ⟨205161766038065851062503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547098042768175602833341 205161766038065851062503)
                  ·
                    rfl

theorem cell20_449495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_449495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449495 prefixEnd_449495 := by exact prefixLift 449495
  have htrace : WordTrace (prefixWord ++ tailWord_449495) baseStart_449495 baseEnd_449495 := by
    simpa [prefixWord, tailWord_449495, baseEnd_449495] using wordTrace_append hprefix tailTrace_449495
  have hstable : (prefixWord ++ tailWord_449495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449495).length < 2 ^ (prefixWord ++ tailWord_449495).sum := by decide
  have hdescent : baseEnd_449495 < baseStart_449495 := by decide
  rcases family_descends (prefixWord ++ tailWord_449495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449498 : List Nat := [3, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_449498 : Nat := 118140960795 + 449498 * 2 ^ 59
def prefixEnd_449498 : Nat := 4983230072969 + 3 ^ 40 * 449498 * 2
def baseEnd_449498 : Nat := 205163135319811173962491

theorem tailTrace_449498 : CollatzResearch.WordTrace tailWord_449498 prefixEnd_449498 205163135319811173962491 := by
  unfold tailWord_449498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098634731388247247921287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10929692617035325994456765 4098634731388247247921287)
  ·
    refine ⟨6147952097082370871881931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4098634731388247247921287 6147952097082370871881931)
    ·
      refine ⟨9221928145623556307822897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6147952097082370871881931 9221928145623556307822897)
      ·
        refine ⟨6916446109217667230867173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9221928145623556307822897 6916446109217667230867173)
        ·
          refine ⟨1296833645478312605787595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6916446109217667230867173 1296833645478312605787595)
          ·
            refine ⟨1945250468217468908681393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296833645478312605787595 1945250468217468908681393)
            ·
              refine ⟨1458937851163101681511045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945250468217468908681393 1458937851163101681511045)
              ·
                refine ⟨273550847093081565283321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1458937851163101681511045 273550847093081565283321)
                ·
                  refine ⟨205163135319811173962491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273550847093081565283321 205163135319811173962491)
                  ·
                    rfl

theorem cell20_449498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_449498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449498 prefixEnd_449498 := by exact prefixLift 449498
  have htrace : WordTrace (prefixWord ++ tailWord_449498) baseStart_449498 baseEnd_449498 := by
    simpa [prefixWord, tailWord_449498, baseEnd_449498] using wordTrace_append hprefix tailTrace_449498
  have hstable : (prefixWord ++ tailWord_449498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449498).length < 2 ^ (prefixWord ++ tailWord_449498).sum := by decide
  have hdescent : baseEnd_449498 < baseStart_449498 := by decide
  rcases family_descends (prefixWord ++ tailWord_449498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449547 : List Nat := [1, 1, 1, 1, 6, 2, 8]
def baseStart_449547 : Nat := 118140960795 + 449547 * 2 ^ 59
def prefixEnd_449547 : Nat := 4983230072969 + 3 ^ 40 * 449547 * 2
def baseEnd_449547 : Nat := 22798388917220531258773

theorem tailTrace_449547 : CollatzResearch.WordTrace tailWord_449547 prefixEnd_449547 22798388917220531258773 := by
  unfold tailWord_449547
  simp only [CollatzResearch.WordTrace]
  refine ⟨16396326102375470360218895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10930884068250313573479263 16396326102375470360218895)
  ·
    refine ⟨24594489153563205540328343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16396326102375470360218895 24594489153563205540328343)
    ·
      refine ⟨36891733730344808310492515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24594489153563205540328343 36891733730344808310492515)
      ·
        refine ⟨55337600595517212465738773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36891733730344808310492515 55337600595517212465738773)
        ·
          refine ⟨2593950027914869334331505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55337600595517212465738773 2593950027914869334331505)
          ·
            refine ⟨1945462520936152000748629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593950027914869334331505 1945462520936152000748629)
            ·
              refine ⟨22798388917220531258773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1945462520936152000748629 22798388917220531258773)
              ·
                rfl

theorem cell20_449547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_449547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449547 prefixEnd_449547 := by exact prefixLift 449547
  have htrace : WordTrace (prefixWord ++ tailWord_449547) baseStart_449547 baseEnd_449547 := by
    simpa [prefixWord, tailWord_449547, baseEnd_449547] using wordTrace_append hprefix tailTrace_449547
  have hstable : (prefixWord ++ tailWord_449547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449547).length < 2 ^ (prefixWord ++ tailWord_449547).sum := by decide
  have hdescent : baseEnd_449547 < baseStart_449547 := by decide
  rcases family_descends (prefixWord ++ tailWord_449547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449557 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_449557 : Nat := 118140960795 + 449557 * 2 ^ 59
def prefixEnd_449557 : Nat := 4983230072969 + 3 ^ 40 * 449557 * 2
def baseEnd_449557 : Nat := 205190064527469190995583

theorem tailTrace_449557 : CollatzResearch.WordTrace tailWord_449557 prefixEnd_449557 205190064527469190995583 := by
  unfold tailWord_449557
  simp only [CollatzResearch.WordTrace]
  refine ⟨16396690832339242068082925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10931127221559494712055283 16396690832339242068082925)
  ·
    refine ⟨6148759062127215775531097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16396690832339242068082925 6148759062127215775531097)
    ·
      refine ⟨4611569296595411831648323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6148759062127215775531097 4611569296595411831648323)
      ·
        refine ⟨6917353944893117747472485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4611569296595411831648323 6917353944893117747472485)
        ·
          refine ⟨1297003864667459577651091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6917353944893117747472485 1297003864667459577651091)
          ·
            refine ⟨1945505797001189366476637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297003864667459577651091 1945505797001189366476637)
            ·
              refine ⟨729564673875446012428739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1945505797001189366476637 729564673875446012428739)
              ·
                refine ⟨1094347010813169018643109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729564673875446012428739 1094347010813169018643109)
                ·
                  refine ⟨205190064527469190995583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094347010813169018643109 205190064527469190995583)
                  ·
                    rfl

theorem cell20_449557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_449557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449557 prefixEnd_449557 := by exact prefixLift 449557
  have htrace : WordTrace (prefixWord ++ tailWord_449557) baseStart_449557 baseEnd_449557 := by
    simpa [prefixWord, tailWord_449557, baseEnd_449557] using wordTrace_append hprefix tailTrace_449557
  have hstable : (prefixWord ++ tailWord_449557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449557).length < 2 ^ (prefixWord ++ tailWord_449557).sum := by decide
  have hdescent : baseEnd_449557 < baseStart_449557 := by decide
  rcases family_descends (prefixWord ++ tailWord_449557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449567 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 3]
def baseStart_449567 : Nat := 118140960795 + 449567 * 2 ^ 59
def prefixEnd_449567 : Nat := 4983230072969 + 3 ^ 40 * 449567 * 2
def baseEnd_449567 : Nat := 205194628799953600662209

theorem tailTrace_449567 : CollatzResearch.WordTrace tailWord_449567 prefixEnd_449567 205194628799953600662209 := by
  unfold tailWord_449567
  simp only [CollatzResearch.WordTrace]
  refine ⟨16397055562303013775946955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10931370374868675850631303 16397055562303013775946955)
  ·
    refine ⟨24595583343454520663920433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16397055562303013775946955 24595583343454520663920433)
    ·
      refine ⟨18446687507590890497940325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24595583343454520663920433 18446687507590890497940325)
      ·
        refine ⟨3458753907673291968363811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18446687507590890497940325 3458753907673291968363811)
        ·
          refine ⟨5188130861509937952545717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458753907673291968363811 5188130861509937952545717)
          ·
            refine ⟨486387268266556683051161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5188130861509937952545717 486387268266556683051161)
            ·
              refine ⟨364790451199917512288371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486387268266556683051161 364790451199917512288371)
              ·
                refine ⟨547185676799876268432557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364790451199917512288371 547185676799876268432557)
                ·
                  refine ⟨205194628799953600662209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547185676799876268432557 205194628799953600662209)
                  ·
                    rfl

theorem cell20_449567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 3].length) (baseStart_449567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449567 prefixEnd_449567 := by exact prefixLift 449567
  have htrace : WordTrace (prefixWord ++ tailWord_449567) baseStart_449567 baseEnd_449567 := by
    simpa [prefixWord, tailWord_449567, baseEnd_449567] using wordTrace_append hprefix tailTrace_449567
  have hstable : (prefixWord ++ tailWord_449567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449567).length < 2 ^ (prefixWord ++ tailWord_449567).sum := by decide
  have hdescent : baseEnd_449567 < baseStart_449567 := by decide
  rcases family_descends (prefixWord ++ tailWord_449567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449585 : List Nat := [1, 2, 2, 3, 1, 2, 1, 8]
def baseStart_449585 : Nat := 118140960795 + 449585 * 2 ^ 59
def prefixEnd_449585 : Nat := 4983230072969 + 3 ^ 40 * 449585 * 2
def baseEnd_449585 : Nat := 68400948163475179354045

theorem tailTrace_449585 : CollatzResearch.WordTrace tailWord_449585 prefixEnd_449585 68400948163475179354045 := by
  unfold tailWord_449585
  simp only [CollatzResearch.WordTrace]
  refine ⟨16397712076237802850102209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10931808050825201900068139 16397712076237802850102209)
  ·
    refine ⟨12298284057178352137576657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16397712076237802850102209 12298284057178352137576657)
    ·
      refine ⟨9223713042883764103182493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12298284057178352137576657 9223713042883764103182493)
      ·
        refine ⟨3458892391081411538693435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9223713042883764103182493 3458892391081411538693435)
        ·
          refine ⟨5188338586622117308040153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458892391081411538693435 5188338586622117308040153)
          ·
            refine ⟨3891253939966587981030115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5188338586622117308040153 3891253939966587981030115)
            ·
              refine ⟨5836880909949881971545173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891253939966587981030115 5836880909949881971545173)
              ·
                refine ⟨68400948163475179354045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5836880909949881971545173 68400948163475179354045)
                ·
                  rfl

theorem cell20_449585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_449585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449585 prefixEnd_449585 := by exact prefixLift 449585
  have htrace : WordTrace (prefixWord ++ tailWord_449585) baseStart_449585 baseEnd_449585 := by
    simpa [prefixWord, tailWord_449585, baseEnd_449585] using wordTrace_append hprefix tailTrace_449585
  have hstable : (prefixWord ++ tailWord_449585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449585).length < 2 ^ (prefixWord ++ tailWord_449585).sum := by decide
  have hdescent : baseEnd_449585 < baseStart_449585 := by decide
  rcases family_descends (prefixWord ++ tailWord_449585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449650 : List Nat := [3, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_449650 : Nat := 118140960795 + 449650 * 2 ^ 59
def prefixEnd_449650 : Nat := 4983230072969 + 3 ^ 40 * 449650 * 2
def baseEnd_449650 : Nat := 205232512261574200895203

theorem tailTrace_449650 : CollatzResearch.WordTrace tailWord_449650 prefixEnd_449650 205232512261574200895203 := by
  unfold tailWord_449650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100020705250579737804601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10933388547334879300812269 4100020705250579737804601)
  ·
    refine ⟨3075015528937934803353451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4100020705250579737804601 3075015528937934803353451)
    ·
      refine ⟨4612523293406902205030177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075015528937934803353451 4612523293406902205030177)
      ·
        refine ⟨3459392470055176653772633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4612523293406902205030177 3459392470055176653772633)
        ·
          refine ⟨2594544352541382490329475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3459392470055176653772633 2594544352541382490329475)
          ·
            refine ⟨3891816528812073735494213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594544352541382490329475 3891816528812073735494213)
            ·
              refine ⟨729715599152263825405165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3891816528812073735494213 729715599152263825405165)
              ·
                refine ⟨273643349682098934526937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729715599152263825405165 273643349682098934526937)
                ·
                  refine ⟨205232512261574200895203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273643349682098934526937 205232512261574200895203)
                  ·
                    rfl

theorem cell20_449650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_449650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449650 prefixEnd_449650 := by exact prefixLift 449650
  have htrace : WordTrace (prefixWord ++ tailWord_449650) baseStart_449650 baseEnd_449650 := by
    simpa [prefixWord, tailWord_449650, baseEnd_449650] using wordTrace_append hprefix tailTrace_449650
  have hstable : (prefixWord ++ tailWord_449650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449650).length < 2 ^ (prefixWord ++ tailWord_449650).sum := by decide
  have hdescent : baseEnd_449650 < baseStart_449650 := by decide
  rcases family_descends (prefixWord ++ tailWord_449650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449661 : List Nat := [1, 4, 1, 1, 3, 1, 9]
def baseStart_449661 : Nat := 118140960795 + 449661 * 2 ^ 59
def prefixEnd_449661 : Nat := 4983230072969 + 3 ^ 40 * 449661 * 2
def baseEnd_449661 : Nat := 22804170329034116836499

theorem tailTrace_449661 : CollatzResearch.WordTrace tailWord_449661 prefixEnd_449661 22804170329034116836499 := by
  unfold tailWord_449661
  simp only [CollatzResearch.WordTrace]
  refine ⟨16400484023962467829868837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10933656015974978553245891 16400484023962467829868837)
  ·
    refine ⟨3075090754492962718100407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16400484023962467829868837 3075090754492962718100407)
    ·
      refine ⟨4612636131739444077150611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075090754492962718100407 4612636131739444077150611)
      ·
        refine ⟨6918954197609166115725917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612636131739444077150611 6918954197609166115725917)
        ·
          refine ⟨2594607824103437293397219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6918954197609166115725917 2594607824103437293397219)
          ·
            refine ⟨3891911736155155940095829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594607824103437293397219 3891911736155155940095829)
            ·
              refine ⟨22804170329034116836499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3891911736155155940095829 22804170329034116836499)
              ·
                rfl

theorem cell20_449661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_449661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449661 prefixEnd_449661 := by exact prefixLift 449661
  have htrace : WordTrace (prefixWord ++ tailWord_449661) baseStart_449661 baseEnd_449661 := by
    simpa [prefixWord, tailWord_449661, baseEnd_449661] using wordTrace_append hprefix tailTrace_449661
  have hstable : (prefixWord ++ tailWord_449661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449661).length < 2 ^ (prefixWord ++ tailWord_449661).sum := by decide
  have hdescent : baseEnd_449661 < baseStart_449661 := by decide
  rcases family_descends (prefixWord ++ tailWord_449661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449726 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_449726 : Nat := 118140960795 + 449726 * 2 ^ 59
def prefixEnd_449726 : Nat := 4983230072969 + 3 ^ 40 * 449726 * 2
def baseEnd_449726 : Nat := 205267200732455714361559

theorem tailTrace_449726 : CollatzResearch.WordTrace tailWord_449726 prefixEnd_449726 205267200732455714361559 := by
  unfold tailWord_449726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050356846090872991373129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10935236512484655953990021 2050356846090872991373129)
  ·
    refine ⟨1537767634568154743529847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2050356846090872991373129 1537767634568154743529847)
    ·
      refine ⟨2306651451852232115294771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537767634568154743529847 2306651451852232115294771)
      ·
        refine ⟨3459977177778348172942157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306651451852232115294771 3459977177778348172942157)
        ·
          refine ⟨1297491441666880564853309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3459977177778348172942157 1297491441666880564853309)
          ·
            refine ⟨486559290625080211819991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1297491441666880564853309 486559290625080211819991)
            ·
              refine ⟨729838935937620317729987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486559290625080211819991 729838935937620317729987)
              ·
                refine ⟨1094758403906430476594981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729838935937620317729987 1094758403906430476594981)
                ·
                  refine ⟨205267200732455714361559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094758403906430476594981 205267200732455714361559)
                  ·
                    rfl

theorem cell20_449726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_449726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449726 prefixEnd_449726 := by exact prefixLift 449726
  have htrace : WordTrace (prefixWord ++ tailWord_449726) baseStart_449726 baseEnd_449726 := by
    simpa [prefixWord, tailWord_449726, baseEnd_449726] using wordTrace_append hprefix tailTrace_449726
  have hstable : (prefixWord ++ tailWord_449726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449726).length < 2 ^ (prefixWord ++ tailWord_449726).sum := by decide
  have hdescent : baseEnd_449726 < baseStart_449726 := by decide
  rcases family_descends (prefixWord ++ tailWord_449726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449775 : List Nat := [1, 1, 2, 1, 7, 8]
def baseStart_449775 : Nat := 118140960795 + 449775 * 2 ^ 59
def prefixEnd_449775 : Nat := 4983230072969 + 3 ^ 40 * 449775 * 2
def baseEnd_449775 : Nat := 7603317246949234138075

theorem tailTrace_449775 : CollatzResearch.WordTrace tailWord_449775 prefixEnd_449775 7603317246949234138075 := by
  unfold tailWord_449775
  simp only [CollatzResearch.WordTrace]
  refine ⟨16404641945549465299518779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10936427963699643533012519 16404641945549465299518779)
  ·
    refine ⟨24606962918324197949278169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16404641945549465299518779 24606962918324197949278169)
    ·
      refine ⟨18455222188743148461958627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24606962918324197949278169 18455222188743148461958627)
      ·
        refine ⟨27682833283114722692937941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455222188743148461958627 27682833283114722692937941)
        ·
          refine ⟨648816405073001313115733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27682833283114722692937941 648816405073001313115733)
          ·
            refine ⟨7603317246949234138075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 648816405073001313115733 7603317246949234138075)
            ·
              rfl

theorem cell20_449775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 8].length) (baseStart_449775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449775 prefixEnd_449775 := by exact prefixLift 449775
  have htrace : WordTrace (prefixWord ++ tailWord_449775) baseStart_449775 baseEnd_449775 := by
    simpa [prefixWord, tailWord_449775, baseEnd_449775] using wordTrace_append hprefix tailTrace_449775
  have hstable : (prefixWord ++ tailWord_449775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449775).length < 2 ^ (prefixWord ++ tailWord_449775).sum := by decide
  have hdescent : baseEnd_449775 < baseStart_449775 := by decide
  rcases family_descends (prefixWord ++ tailWord_449775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449785 : List Nat := [1, 2, 1, 3, 1, 1, 5, 4, 2]
def baseStart_449785 : Nat := 118140960795 + 449785 * 2 ^ 59
def prefixEnd_449785 : Nat := 4983230072969 + 3 ^ 40 * 449785 * 2
def baseEnd_449785 : Nat := 205294129940113731394651

theorem tailTrace_449785 : CollatzResearch.WordTrace tailWord_449785 prefixEnd_449785 205294129940113731394651 := by
  unfold tailWord_449785
  simp only [CollatzResearch.WordTrace]
  refine ⟨16405006675513237007382809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10936671117008824671588539 16405006675513237007382809)
  ·
    refine ⟨12303755006634927755537107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16405006675513237007382809 12303755006634927755537107)
    ·
      refine ⟨18455632509952391633305661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12303755006634927755537107 18455632509952391633305661)
      ·
        refine ⟨6920862191232146862489623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18455632509952391633305661 6920862191232146862489623)
        ·
          refine ⟨10381293286848220293734435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920862191232146862489623 10381293286848220293734435)
          ·
            refine ⟨15571939930272330440601653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10381293286848220293734435 15571939930272330440601653)
            ·
              refine ⟨1459869368463030978806405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15571939930272330440601653 1459869368463030978806405)
              ·
                refine ⟨273725506586818308526201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1459869368463030978806405 273725506586818308526201)
                ·
                  refine ⟨205294129940113731394651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273725506586818308526201 205294129940113731394651)
                  ·
                    rfl

theorem cell20_449785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_449785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449785 prefixEnd_449785 := by exact prefixLift 449785
  have htrace : WordTrace (prefixWord ++ tailWord_449785) baseStart_449785 baseEnd_449785 := by
    simpa [prefixWord, tailWord_449785, baseEnd_449785] using wordTrace_append hprefix tailTrace_449785
  have hstable : (prefixWord ++ tailWord_449785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449785).length < 2 ^ (prefixWord ++ tailWord_449785).sum := by decide
  have hdescent : baseEnd_449785 < baseStart_449785 := by decide
  rcases family_descends (prefixWord ++ tailWord_449785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449806 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_449806 : Nat := 118140960795 + 449806 * 2 ^ 59
def prefixEnd_449806 : Nat := 4983230072969 + 3 ^ 40 * 449806 * 2
def baseEnd_449806 : Nat := 205303714912330991694565

theorem tailTrace_449806 : CollatzResearch.WordTrace tailWord_449806 prefixEnd_449806 205303714912330991694565 := by
  unfold tailWord_449806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050721576054644699237159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10937181738958105062598181 2050721576054644699237159)
  ·
    refine ⟨3076082364081967048855739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2050721576054644699237159 3076082364081967048855739)
    ·
      refine ⟨4614123546122950573283609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076082364081967048855739 4614123546122950573283609)
      ·
        refine ⟨3460592659592212929962707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4614123546122950573283609 3460592659592212929962707)
        ·
          refine ⟨5190888989388319394944061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460592659592212929962707 5190888989388319394944061)
          ·
            refine ⟨1946583371020619773104023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5190888989388319394944061 1946583371020619773104023)
            ·
              refine ⟨2919875056530929659656035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946583371020619773104023 2919875056530929659656035)
              ·
                refine ⟨4379812584796394489484053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919875056530929659656035 4379812584796394489484053)
                ·
                  refine ⟨205303714912330991694565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4379812584796394489484053 205303714912330991694565)
                  ·
                    rfl

theorem cell20_449806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_449806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449806 prefixEnd_449806 := by exact prefixLift 449806
  have htrace : WordTrace (prefixWord ++ tailWord_449806) baseStart_449806 baseEnd_449806 := by
    simpa [prefixWord, tailWord_449806, baseEnd_449806] using wordTrace_append hprefix tailTrace_449806
  have hstable : (prefixWord ++ tailWord_449806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449806).length < 2 ^ (prefixWord ++ tailWord_449806).sum := by decide
  have hdescent : baseEnd_449806 < baseStart_449806 := by decide
  rcases family_descends (prefixWord ++ tailWord_449806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449868 : List Nat := [2, 2, 1, 3, 2, 2, 4, 4]
def baseStart_449868 : Nat := 118140960795 + 449868 * 2 ^ 59
def prefixEnd_449868 : Nat := 4983230072969 + 3 ^ 40 * 449868 * 2
def baseEnd_449868 : Nat := 68444004467244777209215

theorem tailTrace_449868 : CollatzResearch.WordTrace tailWord_449868 prefixEnd_449868 68444004467244777209215 := by
  unfold tailWord_449868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204016967106271091327129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10938689289475028121769505 8204016967106271091327129)
  ·
    refine ⟨6153012725329703318495347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8204016967106271091327129 6153012725329703318495347)
    ·
      refine ⟨9229519087994554977743021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6153012725329703318495347 9229519087994554977743021)
      ·
        refine ⟨3461069657997958116653633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9229519087994554977743021 3461069657997958116653633)
        ·
          refine ⟨2595802243498468587490225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461069657997958116653633 2595802243498468587490225)
          ·
            refine ⟨1946851682623851440617669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2595802243498468587490225 1946851682623851440617669)
            ·
              refine ⟨365034690491972145115813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1946851682623851440617669 365034690491972145115813)
              ·
                refine ⟨68444004467244777209215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365034690491972145115813 68444004467244777209215)
                ·
                  rfl

theorem cell20_449868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_449868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449868 prefixEnd_449868 := by exact prefixLift 449868
  have htrace : WordTrace (prefixWord ++ tailWord_449868) baseStart_449868 baseEnd_449868 := by
    simpa [prefixWord, tailWord_449868, baseEnd_449868] using wordTrace_append hprefix tailTrace_449868
  have hstable : (prefixWord ++ tailWord_449868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449868).length < 2 ^ (prefixWord ++ tailWord_449868).sum := by decide
  have hdescent : baseEnd_449868 < baseStart_449868 := by decide
  rcases family_descends (prefixWord ++ tailWord_449868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449895 : List Nat := [1, 1, 5, 1, 4, 1, 3, 2, 2]
def baseStart_449895 : Nat := 118140960795 + 449895 * 2 ^ 59
def prefixEnd_449895 : Nat := 4983230072969 + 3 ^ 40 * 449895 * 2
def baseEnd_449895 : Nat := 205344336937442237727535

theorem tailTrace_449895 : CollatzResearch.WordTrace tailWord_449895 prefixEnd_449895 205344336937442237727535 := by
  unfold tailWord_449895
  simp only [CollatzResearch.WordTrace]
  refine ⟨16409018705114725793887139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10939345803409817195924759 16409018705114725793887139)
  ·
    refine ⟨24613528057672088690830709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16409018705114725793887139 24613528057672088690830709)
    ·
      refine ⟨2307518255406758314765379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24613528057672088690830709 2307518255406758314765379)
      ·
        refine ⟨3461277383110137472148069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307518255406758314765379 3461277383110137472148069)
        ·
          refine ⟨648989509333150776027763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3461277383110137472148069 648989509333150776027763)
          ·
            refine ⟨973484263999726164041645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648989509333150776027763 973484263999726164041645)
            ·
              refine ⟨365056598999897311515617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 973484263999726164041645 365056598999897311515617)
              ·
                refine ⟨273792449249922983636713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365056598999897311515617 273792449249922983636713)
                ·
                  refine ⟨205344336937442237727535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273792449249922983636713 205344336937442237727535)
                  ·
                    rfl

theorem cell20_449895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 2].length) (baseStart_449895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449895 prefixEnd_449895 := by exact prefixLift 449895
  have htrace : WordTrace (prefixWord ++ tailWord_449895) baseStart_449895 baseEnd_449895 := by
    simpa [prefixWord, tailWord_449895, baseEnd_449895] using wordTrace_append hprefix tailTrace_449895
  have hstable : (prefixWord ++ tailWord_449895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449895).length < 2 ^ (prefixWord ++ tailWord_449895).sum := by decide
  have hdescent : baseEnd_449895 < baseStart_449895 := by decide
  rcases family_descends (prefixWord ++ tailWord_449895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449927 : List Nat := [1, 1, 4, 2, 2, 2, 2, 6]
def baseStart_449927 : Nat := 118140960795 + 449927 * 2 ^ 59
def prefixEnd_449927 : Nat := 4983230072969 + 3 ^ 40 * 449927 * 2
def baseEnd_449927 : Nat := 68452980869797449553579

theorem tailTrace_449927 : CollatzResearch.WordTrace tailWord_449927 prefixEnd_449927 68452980869797449553579 := by
  unfold tailWord_449927
  simp only [CollatzResearch.WordTrace]
  refine ⟨16410185840998795259052035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10940123893999196839368023 16410185840998795259052035)
  ·
    refine ⟨24615278761498192888578053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16410185840998795259052035 24615278761498192888578053)
    ·
      refine ⟨4615364767780911166608385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24615278761498192888578053 4615364767780911166608385)
      ·
        refine ⟨3461523575835683374956289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4615364767780911166608385 3461523575835683374956289)
        ·
          refine ⟨2596142681876762531217217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461523575835683374956289 2596142681876762531217217)
          ·
            refine ⟨1947107011407571898412913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596142681876762531217217 1947107011407571898412913)
            ·
              refine ⟨1460330258555678923809685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947107011407571898412913 1460330258555678923809685)
              ·
                refine ⟨68452980869797449553579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1460330258555678923809685 68452980869797449553579)
                ·
                  rfl

theorem cell20_449927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_449927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449927 prefixEnd_449927 := by exact prefixLift 449927
  have htrace : WordTrace (prefixWord ++ tailWord_449927) baseStart_449927 baseEnd_449927 := by
    simpa [prefixWord, tailWord_449927, baseEnd_449927] using wordTrace_append hprefix tailTrace_449927
  have hstable : (prefixWord ++ tailWord_449927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449927).length < 2 ^ (prefixWord ++ tailWord_449927).sum := by decide
  have hdescent : baseEnd_449927 < baseStart_449927 := by decide
  rcases family_descends (prefixWord ++ tailWord_449927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449944 : List Nat := [2, 1, 2, 5, 3, 7]
def baseStart_449944 : Nat := 118140960795 + 449944 * 2 ^ 59
def prefixEnd_449944 : Nat := 4983230072969 + 3 ^ 40 * 449944 * 2
def baseEnd_449944 : Nat := 7606174143430216484963

theorem tailTrace_449944 : CollatzResearch.WordTrace tailWord_449944 prefixEnd_449944 7606174143430216484963 := by
  unfold tailWord_449944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205402940968603581210443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10940537254624804774947257 8205402940968603581210443)
  ·
    refine ⟨12308104411452905371815665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8205402940968603581210443 12308104411452905371815665)
    ·
      refine ⟨9231078308589679028861749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12308104411452905371815665 9231078308589679028861749)
      ·
        refine ⟨865413591430282408955789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9231078308589679028861749 865413591430282408955789)
        ·
          refine ⟨324530096786355903358421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 865413591430282408955789 324530096786355903358421)
          ·
            refine ⟨7606174143430216484963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 324530096786355903358421 7606174143430216484963)
            ·
              rfl

theorem cell20_449944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 7].length) (baseStart_449944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449944 prefixEnd_449944 := by exact prefixLift 449944
  have htrace : WordTrace (prefixWord ++ tailWord_449944) baseStart_449944 baseEnd_449944 := by
    simpa [prefixWord, tailWord_449944, baseEnd_449944] using wordTrace_append hprefix tailTrace_449944
  have hstable : (prefixWord ++ tailWord_449944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449944).length < 2 ^ (prefixWord ++ tailWord_449944).sum := by decide
  have hdescent : baseEnd_449944 < baseStart_449944 := by decide
  rcases family_descends (prefixWord ++ tailWord_449944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449951 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 3]
def baseStart_449951 : Nat := 118140960795 + 449951 * 2 ^ 59
def prefixEnd_449951 : Nat := 4983230072969 + 3 ^ 40 * 449951 * 2
def baseEnd_449951 : Nat := 205369896863354931860639

theorem tailTrace_449951 : CollatzResearch.WordTrace tailWord_449951 prefixEnd_449951 205369896863354931860639 := by
  unfold tailWord_449951
  simp only [CollatzResearch.WordTrace]
  refine ⟨16411061192911847357925707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10940707461941231571950471 16411061192911847357925707)
  ·
    refine ⟨24616591789367771036888561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16411061192911847357925707 24616591789367771036888561)
    ·
      refine ⟨18462443842025828277666421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24616591789367771036888561 18462443842025828277666421)
      ·
        refine ⟨1730854110189921401031227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18462443842025828277666421 1730854110189921401031227)
        ·
          refine ⟨2596281165284882101546841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730854110189921401031227 2596281165284882101546841)
          ·
            refine ⟨1947210873963661576160131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596281165284882101546841 1947210873963661576160131)
            ·
              refine ⟨2920816310945492364240197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947210873963661576160131 2920816310945492364240197)
              ·
                refine ⟨547653058302279818295037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2920816310945492364240197 547653058302279818295037)
                ·
                  refine ⟨205369896863354931860639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547653058302279818295037 205369896863354931860639)
                  ·
                    rfl

theorem cell20_449951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_449951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449951 prefixEnd_449951 := by exact prefixLift 449951
  have htrace : WordTrace (prefixWord ++ tailWord_449951) baseStart_449951 baseEnd_449951 := by
    simpa [prefixWord, tailWord_449951, baseEnd_449951] using wordTrace_append hprefix tailTrace_449951
  have hstable : (prefixWord ++ tailWord_449951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449951).length < 2 ^ (prefixWord ++ tailWord_449951).sum := by decide
  have hdescent : baseEnd_449951 < baseStart_449951 := by decide
  rcases family_descends (prefixWord ++ tailWord_449951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449954 : List Nat := [3, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_449954 : Nat := 118140960795 + 449954 * 2 ^ 59
def prefixEnd_449954 : Nat := 4983230072969 + 3 ^ 40 * 449954 * 2
def baseEnd_449954 : Nat := 205371266145100254760627

theorem tailTrace_449954 : CollatzResearch.WordTrace tailWord_449954 prefixEnd_449954 205371266145100254760627 := by
  unfold tailWord_449954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102792652975244717571229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10940780407933985913523277 4102792652975244717571229)
  ·
    refine ⟨1538547244865716769089211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4102792652975244717571229 1538547244865716769089211)
    ·
      refine ⟨2307820867298575153633817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538547244865716769089211 2307820867298575153633817)
      ·
        refine ⟨1730865650473931365225363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2307820867298575153633817 1730865650473931365225363)
        ·
          refine ⟨2596298475710897047838045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730865650473931365225363 2596298475710897047838045)
          ·
            refine ⟨973611928391586392939267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2596298475710897047838045 973611928391586392939267)
            ·
              refine ⟨1460417892587379589408901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973611928391586392939267 1460417892587379589408901)
              ·
                refine ⟨273828354860133673014169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1460417892587379589408901 273828354860133673014169)
                ·
                  refine ⟨205371266145100254760627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273828354860133673014169 205371266145100254760627)
                  ·
                    rfl

theorem cell20_449954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_449954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_449954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_449954 prefixEnd_449954 := by exact prefixLift 449954
  have htrace : WordTrace (prefixWord ++ tailWord_449954) baseStart_449954 baseEnd_449954 := by
    simpa [prefixWord, tailWord_449954, baseEnd_449954] using wordTrace_append hprefix tailTrace_449954
  have hstable : (prefixWord ++ tailWord_449954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449954).length < 2 ^ (prefixWord ++ tailWord_449954).sum := by decide
  have hdescent : baseEnd_449954 < baseStart_449954 := by decide
  rcases family_descends (prefixWord ++ tailWord_449954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450006 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_450006 : Nat := 118140960795 + 450006 * 2 ^ 59
def prefixEnd_450006 : Nat := 4983230072969 + 3 ^ 40 * 450006 * 2
def baseEnd_450006 : Nat := 205395000362019185027081

theorem tailTrace_450006 : CollatzResearch.WordTrace tailWord_450006 prefixEnd_450006 205395000362019185027081 := by
  unfold tailWord_450006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025816700482036984448617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10942044805141727834118581 1025816700482036984448617)
  ·
    refine ⟨769362525361527738336463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1025816700482036984448617 769362525361527738336463)
    ·
      refine ⟨1154043788042291607504695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769362525361527738336463 1154043788042291607504695)
      ·
        refine ⟨1731065682063437411257043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154043788042291607504695 1731065682063437411257043)
        ·
          refine ⟨2596598523095156116885565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731065682063437411257043 2596598523095156116885565)
          ·
            refine ⟨973724446160683543832087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2596598523095156116885565 973724446160683543832087)
            ·
              refine ⟨1460586669241025315748131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973724446160683543832087 1460586669241025315748131)
              ·
                refine ⟨2190880003861537973622197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460586669241025315748131 2190880003861537973622197)
                ·
                  refine ⟨205395000362019185027081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2190880003861537973622197 205395000362019185027081)
                  ·
                    rfl

theorem cell20_450006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_450006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450006 prefixEnd_450006 := by exact prefixLift 450006
  have htrace : WordTrace (prefixWord ++ tailWord_450006) baseStart_450006 baseEnd_450006 := by
    simpa [prefixWord, tailWord_450006, baseEnd_450006] using wordTrace_append hprefix tailTrace_450006
  have hstable : (prefixWord ++ tailWord_450006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450006).length < 2 ^ (prefixWord ++ tailWord_450006).sum := by decide
  have hdescent : baseEnd_450006 < baseStart_450006 := by decide
  rcases family_descends (prefixWord ++ tailWord_450006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450013 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_450013 : Nat := 118140960795 + 450013 * 2 ^ 59
def prefixEnd_450013 : Nat := 4983230072969 + 3 ^ 40 * 450013 * 2
def baseEnd_450013 : Nat := 205398195352758271793719

theorem tailTrace_450013 : CollatzResearch.WordTrace tailWord_450013 prefixEnd_450013 205398195352758271793719 := by
  unfold tailWord_450013
  simp only [CollatzResearch.WordTrace]
  refine ⟨16413322518687231946682693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10942215012458154631121795 16413322518687231946682693)
  ·
    refine ⟨3077497972253855990003005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16413322518687231946682693 3077497972253855990003005)
    ·
      refine ⟨1154061739595195996251127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3077497972253855990003005 1154061739595195996251127)
      ·
        refine ⟨1731092609392793994376691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154061739595195996251127 1731092609392793994376691)
        ·
          refine ⟨2596638914089190991565037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731092609392793994376691 2596638914089190991565037)
          ·
            refine ⟨973739592783446621836889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2596638914089190991565037 973739592783446621836889)
            ·
              refine ⟨730304694587584966377667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973739592783446621836889 730304694587584966377667)
              ·
                refine ⟨1095457041881377449566501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730304694587584966377667 1095457041881377449566501)
                ·
                  refine ⟨205398195352758271793719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095457041881377449566501 205398195352758271793719)
                  ·
                    rfl

theorem cell20_450013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_450013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450013 prefixEnd_450013 := by exact prefixLift 450013
  have htrace : WordTrace (prefixWord ++ tailWord_450013) baseStart_450013 baseEnd_450013 := by
    simpa [prefixWord, tailWord_450013, baseEnd_450013] using wordTrace_append hprefix tailTrace_450013
  have hstable : (prefixWord ++ tailWord_450013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450013).length < 2 ^ (prefixWord ++ tailWord_450013).sum := by decide
  have hdescent : baseEnd_450013 < baseStart_450013 := by decide
  rcases family_descends (prefixWord ++ tailWord_450013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450037 : List Nat := [1, 3, 5, 1, 1, 1, 4, 4]
def baseStart_450037 : Nat := 118140960795 + 450037 * 2 ^ 59
def prefixEnd_450037 : Nat := 4983230072969 + 3 ^ 40 * 450037 * 2
def baseEnd_450037 : Nat := 68469716535573618331207

theorem tailTrace_450037 : CollatzResearch.WordTrace tailWord_450037 prefixEnd_450037 68469716535573618331207 := by
  unfold tailWord_450037
  simp only [CollatzResearch.WordTrace]
  refine ⟨16414197870600284045556365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10942798580400189363704243 16414197870600284045556365)
  ·
    refine ⟨6155324201475106517083637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16414197870600284045556365 6155324201475106517083637)
    ·
      refine ⟨577061643888291235976591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6155324201475106517083637 577061643888291235976591)
      ·
        refine ⟨865592465832436853964887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577061643888291235976591 865592465832436853964887)
        ·
          refine ⟨1298388698748655280947331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865592465832436853964887 1298388698748655280947331)
          ·
            refine ⟨1947583048122982921420997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298388698748655280947331 1947583048122982921420997)
            ·
              refine ⟨365171821523059297766437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1947583048122982921420997 365171821523059297766437)
              ·
                refine ⟨68469716535573618331207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365171821523059297766437 68469716535573618331207)
                ·
                  rfl

theorem cell20_450037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_450037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450037 prefixEnd_450037 := by exact prefixLift 450037
  have htrace : WordTrace (prefixWord ++ tailWord_450037) baseStart_450037 baseEnd_450037 := by
    simpa [prefixWord, tailWord_450037, baseEnd_450037] using wordTrace_append hprefix tailTrace_450037
  have hstable : (prefixWord ++ tailWord_450037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450037).length < 2 ^ (prefixWord ++ tailWord_450037).sum := by decide
  have hdescent : baseEnd_450037 < baseStart_450037 := by decide
  rcases family_descends (prefixWord ++ tailWord_450037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450082 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_450082 : Nat := 118140960795 + 450082 * 2 ^ 59
def prefixEnd_450082 : Nat := 4983230072969 + 3 ^ 40 * 450082 * 2
def baseEnd_450082 : Nat := 205429688832900698493437

theorem tailTrace_450082 : CollatzResearch.WordTrace tailWord_450082 prefixEnd_450082 205429688832900698493437 := by
  unfold tailWord_450082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4103959788859314182736125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10943892770291504487296333 4103959788859314182736125)
  ·
    refine ⟨1538984920822242818526047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4103959788859314182736125 1538984920822242818526047)
    ·
      refine ⟨2308477381233364227789071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538984920822242818526047 2308477381233364227789071)
      ·
        refine ⟨3462716071850046341683607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308477381233364227789071 3462716071850046341683607)
        ·
          refine ⟨5194074107775069512525411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462716071850046341683607 5194074107775069512525411)
          ·
            refine ⟨7791111161662604268788117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194074107775069512525411 7791111161662604268788117)
            ·
              refine ⟨365208335702934575099443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7791111161662604268788117 365208335702934575099443)
              ·
                refine ⟨547812503554401862649165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365208335702934575099443 547812503554401862649165)
                ·
                  refine ⟨205429688832900698493437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547812503554401862649165 205429688832900698493437)
                  ·
                    rfl

theorem cell20_450082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_450082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450082 prefixEnd_450082 := by exact prefixLift 450082
  have htrace : WordTrace (prefixWord ++ tailWord_450082) baseStart_450082 baseEnd_450082 := by
    simpa [prefixWord, tailWord_450082, baseEnd_450082] using wordTrace_append hprefix tailTrace_450082
  have hstable : (prefixWord ++ tailWord_450082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450082).length < 2 ^ (prefixWord ++ tailWord_450082).sum := by decide
  have hdescent : baseEnd_450082 < baseStart_450082 := by decide
  rcases family_descends (prefixWord ++ tailWord_450082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450148 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_450148 : Nat := 118140960795 + 450148 * 2 ^ 59
def prefixEnd_450148 : Nat := 4983230072969 + 3 ^ 40 * 450148 * 2
def baseEnd_450148 : Nat := 205459813031297802293167

theorem tailTrace_450148 : CollatzResearch.WordTrace tailWord_450148 prefixEnd_450148 205459813031297802293167 := by
  unfold tailWord_450148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8209123186599075001423549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10945497582132100001898065 8209123186599075001423549)
  ·
    refine ⟨3078421194974653125533831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8209123186599075001423549 3078421194974653125533831)
    ·
      refine ⟨4617631792461979688300747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3078421194974653125533831 4617631792461979688300747)
      ·
        refine ⟨6926447688692969532451121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617631792461979688300747 6926447688692969532451121)
        ·
          refine ⟨5194835766519727149338341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6926447688692969532451121 5194835766519727149338341)
          ·
            refine ⟨974031706222448840500939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5194835766519727149338341 974031706222448840500939)
            ·
              refine ⟨1461047559333673260751409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974031706222448840500939 1461047559333673260751409)
              ·
                refine ⟨1095785669500254945563557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461047559333673260751409 1095785669500254945563557)
                ·
                  refine ⟨205459813031297802293167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095785669500254945563557 205459813031297802293167)
                  ·
                    rfl

theorem cell20_450148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_450148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450148 prefixEnd_450148 := by exact prefixLift 450148
  have htrace : WordTrace (prefixWord ++ tailWord_450148) baseStart_450148 baseEnd_450148 := by
    simpa [prefixWord, tailWord_450148, baseEnd_450148] using wordTrace_append hprefix tailTrace_450148
  have hstable : (prefixWord ++ tailWord_450148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450148).length < 2 ^ (prefixWord ++ tailWord_450148).sum := by decide
  have hdescent : baseEnd_450148 < baseStart_450148 := by decide
  rcases family_descends (prefixWord ++ tailWord_450148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450169 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_450169 : Nat := 118140960795 + 450169 * 2 ^ 59
def prefixEnd_450169 : Nat := 4983230072969 + 3 ^ 40 * 450169 * 2
def baseEnd_450169 : Nat := 205469398003515062593081

theorem tailTrace_450169 : CollatzResearch.WordTrace tailWord_450169 prefixEnd_450169 205469398003515062593081 := by
  unfold tailWord_450169
  simp only [CollatzResearch.WordTrace]
  refine ⟨16419012306122070589361561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10946008204081380392907707 16419012306122070589361561)
  ·
    refine ⟨12314259229591552942021171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16419012306122070589361561 12314259229591552942021171)
    ·
      refine ⟨18471388844387329413031757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12314259229591552942021171 18471388844387329413031757)
      ·
        refine ⟨6926770816645248529886909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18471388844387329413031757 6926770816645248529886909)
        ·
          refine ⟨2597539056241968198707591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6926770816645248529886909 2597539056241968198707591)
          ·
            refine ⟨3896308584362952298061387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597539056241968198707591 3896308584362952298061387)
            ·
              refine ⟨5844462876544428447092081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896308584362952298061387 5844462876544428447092081)
              ·
                refine ⟨4383347157408321335319061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5844462876544428447092081 4383347157408321335319061)
                ·
                  refine ⟨205469398003515062593081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4383347157408321335319061 205469398003515062593081)
                  ·
                    rfl

theorem cell20_450169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_450169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450169 prefixEnd_450169 := by exact prefixLift 450169
  have htrace : WordTrace (prefixWord ++ tailWord_450169) baseStart_450169 baseEnd_450169 := by
    simpa [prefixWord, tailWord_450169, baseEnd_450169] using wordTrace_append hprefix tailTrace_450169
  have hstable : (prefixWord ++ tailWord_450169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450169).length < 2 ^ (prefixWord ++ tailWord_450169).sum := by decide
  have hdescent : baseEnd_450169 < baseStart_450169 := by decide
  rcases family_descends (prefixWord ++ tailWord_450169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450176 : List Nat := [2, 1, 1, 2, 1, 4, 9]
def baseStart_450176 : Nat := 118140960795 + 450176 * 2 ^ 59
def prefixEnd_450176 : Nat := 4983230072969 + 3 ^ 40 * 450176 * 2
def baseEnd_450176 : Nat := 22830288110472683262191

theorem tailTrace_450176 : CollatzResearch.WordTrace tailWord_450176 prefixEnd_450176 22830288110472683262191 := by
  unfold tailWord_450176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8209633808548355392433191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10946178411397807189910921 8209633808548355392433191)
  ·
    refine ⟨12314450712822533088649787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8209633808548355392433191 12314450712822533088649787)
    ·
      refine ⟨18471676069233799632974681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12314450712822533088649787 18471676069233799632974681)
      ·
        refine ⟨13853757051925349724731011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18471676069233799632974681 13853757051925349724731011)
        ·
          refine ⟨20780635577888024587096517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13853757051925349724731011 20780635577888024587096517)
          ·
            refine ⟨3896369170854004610080597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20780635577888024587096517 3896369170854004610080597)
            ·
              refine ⟨22830288110472683262191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3896369170854004610080597 22830288110472683262191)
              ·
                rfl

theorem cell20_450176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 9].length) (baseStart_450176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450176 prefixEnd_450176 := by exact prefixLift 450176
  have htrace : WordTrace (prefixWord ++ tailWord_450176) baseStart_450176 baseEnd_450176 := by
    simpa [prefixWord, tailWord_450176, baseEnd_450176] using wordTrace_append hprefix tailTrace_450176
  have hstable : (prefixWord ++ tailWord_450176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450176).length < 2 ^ (prefixWord ++ tailWord_450176).sum := by decide
  have hdescent : baseEnd_450176 < baseStart_450176 := by decide
  rcases family_descends (prefixWord ++ tailWord_450176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450186 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_450186 : Nat := 118140960795 + 450186 * 2 ^ 59
def prefixEnd_450186 : Nat := 4983230072969 + 3 ^ 40 * 450186 * 2
def baseEnd_450186 : Nat := 205477157266738559026345

theorem tailTrace_450186 : CollatzResearch.WordTrace tailWord_450186 prefixEnd_450186 205477157266738559026345 := by
  unfold tailWord_450186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104908086765120623182603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10946421564706988328486941 4104908086765120623182603)
  ·
    refine ⟨6157362130147680934773905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4104908086765120623182603 6157362130147680934773905)
    ·
      refine ⟨4618021597610760701080429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6157362130147680934773905 4618021597610760701080429)
      ·
        refine ⟨1731758099104035262905161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4618021597610760701080429 1731758099104035262905161)
        ·
          refine ⟨1298818574328026447178871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1731758099104035262905161 1298818574328026447178871)
          ·
            refine ⟨1948227861492039670768307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298818574328026447178871 1948227861492039670768307)
            ·
              refine ⟨2922341792238059506152461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948227861492039670768307 2922341792238059506152461)
              ·
                refine ⟨1095878172089272314807173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2922341792238059506152461 1095878172089272314807173)
                ·
                  refine ⟨205477157266738559026345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095878172089272314807173 205477157266738559026345)
                  ·
                    rfl

theorem cell20_450186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_450186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450186 prefixEnd_450186 := by exact prefixLift 450186
  have htrace : WordTrace (prefixWord ++ tailWord_450186) baseStart_450186 baseEnd_450186 := by
    simpa [prefixWord, tailWord_450186, baseEnd_450186] using wordTrace_append hprefix tailTrace_450186
  have hstable : (prefixWord ++ tailWord_450186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450186).length < 2 ^ (prefixWord ++ tailWord_450186).sum := by decide
  have hdescent : baseEnd_450186 < baseStart_450186 := by decide
  rcases family_descends (prefixWord ++ tailWord_450186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450231 : List Nat := [1, 1, 3, 1, 5, 3, 6]
def baseStart_450231 : Nat := 118140960795 + 450231 * 2 ^ 59
def prefixEnd_450231 : Nat := 4983230072969 + 3 ^ 40 * 450231 * 2
def baseEnd_450231 : Nat := 22833077388102044725129

theorem tailTrace_450231 : CollatzResearch.WordTrace tailWord_450231 prefixEnd_450231 22833077388102044725129 := by
  unfold tailWord_450231
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421273631897455178118547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10947515754598303452079031 16421273631897455178118547)
  ·
    refine ⟨24631910447846182767177821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16421273631897455178118547 24631910447846182767177821)
    ·
      refine ⟨9236966417942318537691683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24631910447846182767177821 9236966417942318537691683)
      ·
        refine ⟨13855449626913477806537525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9236966417942318537691683 13855449626913477806537525)
        ·
          refine ⟨1298948402523138544362893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13855449626913477806537525 1298948402523138544362893)
          ·
            refine ⟨487105650946176954136085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1298948402523138544362893 487105650946176954136085)
            ·
              refine ⟨22833077388102044725129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 487105650946176954136085 22833077388102044725129)
              ·
                rfl

theorem cell20_450231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 6].length) (baseStart_450231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450231 prefixEnd_450231 := by exact prefixLift 450231
  have htrace : WordTrace (prefixWord ++ tailWord_450231) baseStart_450231 baseEnd_450231 := by
    simpa [prefixWord, tailWord_450231, baseEnd_450231] using wordTrace_append hprefix tailTrace_450231
  have hstable : (prefixWord ++ tailWord_450231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450231).length < 2 ^ (prefixWord ++ tailWord_450231).sum := by decide
  have hdescent : baseEnd_450231 < baseStart_450231 := by decide
  rcases family_descends (prefixWord ++ tailWord_450231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450292 : List Nat := [2, 6, 1, 1, 1, 1, 4, 2, 2]
def baseStart_450292 : Nat := 118140960795 + 450292 * 2 ^ 59
def prefixEnd_450292 : Nat := 4983230072969 + 3 ^ 40 * 450292 * 2
def baseEnd_450292 : Nat := 205525538555073301492579

theorem tailTrace_450292 : CollatzResearch.WordTrace tailWord_450292 prefixEnd_450292 205525538555073301492579 := by
  unfold tailWord_450292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211749242338231298044565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10948998989784308397392753 8211749242338231298044565)
  ·
    refine ⟨384925745734604592095839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8211749242338231298044565 384925745734604592095839)
    ·
      refine ⟨577388618601906888143759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384925745734604592095839 577388618601906888143759)
      ·
        refine ⟨866082927902860332215639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577388618601906888143759 866082927902860332215639)
        ·
          refine ⟨1299124391854290498323459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866082927902860332215639 1299124391854290498323459)
          ·
            refine ⟨1948686587781435747485189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299124391854290498323459 1948686587781435747485189)
            ·
              refine ⟨365378735209019202653473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1948686587781435747485189 365378735209019202653473)
              ·
                refine ⟨274034051406764401990105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365378735209019202653473 274034051406764401990105)
                ·
                  refine ⟨205525538555073301492579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274034051406764401990105 205525538555073301492579)
                  ·
                    rfl

theorem cell20_450292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_450292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450292 prefixEnd_450292 := by exact prefixLift 450292
  have htrace : WordTrace (prefixWord ++ tailWord_450292) baseStart_450292 baseEnd_450292 := by
    simpa [prefixWord, tailWord_450292, baseEnd_450292] using wordTrace_append hprefix tailTrace_450292
  have hstable : (prefixWord ++ tailWord_450292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450292).length < 2 ^ (prefixWord ++ tailWord_450292).sum := by decide
  have hdescent : baseEnd_450292 < baseStart_450292 := by decide
  rcases family_descends (prefixWord ++ tailWord_450292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450328 : List Nat := [2, 1, 2, 3, 1, 1, 2, 8]
def baseStart_450328 : Nat := 118140960795 + 450328 * 2 ^ 59
def prefixEnd_450328 : Nat := 4983230072969 + 3 ^ 40 * 450328 * 2
def baseEnd_450328 : Nat := 68513989978672392097477

theorem tailTrace_450328 : CollatzResearch.WordTrace tailWord_450328 prefixEnd_450328 68513989978672392097477 := by
  unfold tailWord_450328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212405756273020372199819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10949874341697360496266425 8212405756273020372199819)
  ·
    refine ⟨12318608634409530558299729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8212405756273020372199819 12318608634409530558299729)
    ·
      refine ⟨9238956475807147918724797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12318608634409530558299729 9238956475807147918724797)
      ·
        refine ⟨3464608678427680469521799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9238956475807147918724797 3464608678427680469521799)
        ·
          refine ⟨5196913017641520704282699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464608678427680469521799 5196913017641520704282699)
          ·
            refine ⟨7795369526462281056424049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196913017641520704282699 7795369526462281056424049)
            ·
              refine ⟨5846527144846710792318037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7795369526462281056424049 5846527144846710792318037)
              ·
                refine ⟨68513989978672392097477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5846527144846710792318037 68513989978672392097477)
                ·
                  rfl

theorem cell20_450328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_450328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450328 prefixEnd_450328 := by exact prefixLift 450328
  have htrace : WordTrace (prefixWord ++ tailWord_450328) baseStart_450328 baseEnd_450328 := by
    simpa [prefixWord, tailWord_450328, baseEnd_450328] using wordTrace_append hprefix tailTrace_450328
  have hstable : (prefixWord ++ tailWord_450328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450328).length < 2 ^ (prefixWord ++ tailWord_450328).sum := by decide
  have hdescent : baseEnd_450328 < baseStart_450328 := by decide
  rcases family_descends (prefixWord ++ tailWord_450328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450410 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_450410 : Nat := 118140960795 + 450410 * 2 ^ 59
def prefixEnd_450410 : Nat := 4983230072969 + 3 ^ 40 * 450410 * 2
def baseEnd_450410 : Nat := 205579396970389335558763

theorem tailTrace_450410 : CollatzResearch.WordTrace tailWord_450410 prefixEnd_450410 205579396970389335558763 := by
  unfold tailWord_450410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106950574562242187221171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10951868198832645832589789 4106950574562242187221171)
  ·
    refine ⟨6160425861843363280831757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4106950574562242187221171 6160425861843363280831757)
    ·
      refine ⟨2310159698191261230311909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6160425861843363280831757 2310159698191261230311909)
      ·
        refine ⟨433154943410861480683483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2310159698191261230311909 433154943410861480683483)
        ·
          refine ⟨649732415116292221025225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433154943410861480683483 649732415116292221025225)
          ·
            refine ⟨487299311337219165768919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649732415116292221025225 487299311337219165768919)
            ·
              refine ⟨730948967005828748653379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487299311337219165768919 730948967005828748653379)
              ·
                refine ⟨1096423450508743122980069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730948967005828748653379 1096423450508743122980069)
                ·
                  refine ⟨205579396970389335558763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096423450508743122980069 205579396970389335558763)
                  ·
                    rfl

theorem cell20_450410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_450410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450410 prefixEnd_450410 := by exact prefixLift 450410
  have htrace : WordTrace (prefixWord ++ tailWord_450410) baseStart_450410 baseEnd_450410 := by
    simpa [prefixWord, tailWord_450410, baseEnd_450410] using wordTrace_append hprefix tailTrace_450410
  have hstable : (prefixWord ++ tailWord_450410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450410).length < 2 ^ (prefixWord ++ tailWord_450410).sum := by decide
  have hdescent : baseEnd_450410 < baseStart_450410 := by decide
  rcases family_descends (prefixWord ++ tailWord_450410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450421 : List Nat := [1, 3, 4, 1, 1, 1, 4, 5]
def baseStart_450421 : Nat := 118140960795 + 450421 * 2 ^ 59
def prefixEnd_450421 : Nat := 4983230072969 + 3 ^ 40 * 450421 * 2
def baseEnd_450421 : Nat := 68528139223374062064017

theorem tailTrace_450421 : CollatzResearch.WordTrace tailWord_450421 prefixEnd_450421 68528139223374062064017 := by
  unfold tailWord_450421
  simp only [CollatzResearch.WordTrace]
  refine ⟨16428203501209117627535117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10952135667472745085023411 16428203501209117627535117)
  ·
    refine ⟨6160576312953419110325669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16428203501209117627535117 6160576312953419110325669)
    ·
      refine ⟨1155108058678766083186063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6160576312953419110325669 1155108058678766083186063)
      ·
        refine ⟨1732662088018149124779095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155108058678766083186063 1732662088018149124779095)
        ·
          refine ⟨2598993132027223687168643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732662088018149124779095 2598993132027223687168643)
          ·
            refine ⟨3898489698040835530752965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598993132027223687168643 3898489698040835530752965)
            ·
              refine ⟨730966818382656662016181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3898489698040835530752965 730966818382656662016181)
              ·
                refine ⟨68528139223374062064017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 730966818382656662016181 68528139223374062064017)
                ·
                  rfl

theorem cell20_450421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_450421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450421 prefixEnd_450421 := by exact prefixLift 450421
  have htrace : WordTrace (prefixWord ++ tailWord_450421) baseStart_450421 baseEnd_450421 := by
    simpa [prefixWord, tailWord_450421, baseEnd_450421] using wordTrace_append hprefix tailTrace_450421
  have hstable : (prefixWord ++ tailWord_450421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450421).length < 2 ^ (prefixWord ++ tailWord_450421).sum := by decide
  have hdescent : baseEnd_450421 < baseStart_450421 := by decide
  rcases family_descends (prefixWord ++ tailWord_450421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450449 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_450449 : Nat := 118140960795 + 450449 * 2 ^ 59
def prefixEnd_450449 : Nat := 4983230072969 + 3 ^ 40 * 450449 * 2
def baseEnd_450449 : Nat := 205597197633078533258603

theorem tailTrace_450449 : CollatzResearch.WordTrace tailWord_450449 prefixEnd_450449 205597197633078533258603 := by
  unfold tailWord_450449
  simp only [CollatzResearch.WordTrace]
  refine ⟨16429224745107678409554401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10952816496738452273036267 16429224745107678409554401)
  ·
    refine ⟨12321918558830758807165801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16429224745107678409554401 12321918558830758807165801)
    ·
      refine ⟨9241438919123069105374351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12321918558830758807165801 9241438919123069105374351)
      ·
        refine ⟨13862158378684603658061527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9241438919123069105374351 13862158378684603658061527)
        ·
          refine ⟨20793237568026905487092291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13862158378684603658061527 20793237568026905487092291)
          ·
            refine ⟨31189856352040358230638437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20793237568026905487092291 31189856352040358230638437)
            ·
              refine ⟨5848098066007567168244707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31189856352040358230638437 5848098066007567168244707)
              ·
                refine ⟨8772147099011350752367061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848098066007567168244707 8772147099011350752367061)
                ·
                  refine ⟨205597197633078533258603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8772147099011350752367061 205597197633078533258603)
                  ·
                    rfl

theorem cell20_450449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_450449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450449 prefixEnd_450449 := by exact prefixLift 450449
  have htrace : WordTrace (prefixWord ++ tailWord_450449) baseStart_450449 baseEnd_450449 := by
    simpa [prefixWord, tailWord_450449, baseEnd_450449] using wordTrace_append hprefix tailTrace_450449
  have hstable : (prefixWord ++ tailWord_450449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450449).length < 2 ^ (prefixWord ++ tailWord_450449).sum := by decide
  have hdescent : baseEnd_450449 < baseStart_450449 := by decide
  rcases family_descends (prefixWord ++ tailWord_450449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450465 : List Nat := [1, 2, 3, 4, 2, 2, 2, 2, 2]
def baseStart_450465 : Nat := 118140960795 + 450465 * 2 ^ 59
def prefixEnd_450465 : Nat := 4983230072969 + 3 ^ 40 * 450465 * 2
def baseEnd_450465 : Nat := 205604500469053588725205

theorem tailTrace_450465 : CollatzResearch.WordTrace tailWord_450465 prefixEnd_450465 205604500469053588725205 := by
  unfold tailWord_450465
  simp only [CollatzResearch.WordTrace]
  refine ⟨16429808313049713142136849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10953205542033142094757899 16429808313049713142136849)
  ·
    refine ⟨12322356234787284856602637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16429808313049713142136849 12322356234787284856602637)
    ·
      refine ⟨4620883588045231821225989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12322356234787284856602637 4620883588045231821225989)
      ·
        refine ⟨866415672758480966479873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4620883588045231821225989 866415672758480966479873)
        ·
          refine ⟨649811754568860724859905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866415672758480966479873 649811754568860724859905)
          ·
            refine ⟨487358815926645543644929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649811754568860724859905 487358815926645543644929)
            ·
              refine ⟨365519111944984157733697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487358815926645543644929 365519111944984157733697)
              ·
                refine ⟨274139333958738118300273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365519111944984157733697 274139333958738118300273)
                ·
                  refine ⟨205604500469053588725205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274139333958738118300273 205604500469053588725205)
                  ·
                    rfl

theorem cell20_450465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_450465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450465 prefixEnd_450465 := by exact prefixLift 450465
  have htrace : WordTrace (prefixWord ++ tailWord_450465) baseStart_450465 baseEnd_450465 := by
    simpa [prefixWord, tailWord_450465, baseEnd_450465] using wordTrace_append hprefix tailTrace_450465
  have hstable : (prefixWord ++ tailWord_450465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450465).length < 2 ^ (prefixWord ++ tailWord_450465).sum := by decide
  have hdescent : baseEnd_450465 < baseStart_450465 := by decide
  rcases family_descends (prefixWord ++ tailWord_450465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450472 : List Nat := [2, 1, 6, 2, 2, 1, 1, 5]
def baseStart_450472 : Nat := 118140960795 + 450472 * 2 ^ 59
def prefixEnd_450472 : Nat := 4983230072969 + 3 ^ 40 * 450472 * 2
def baseEnd_450472 : Nat := 68535898486597558497281

theorem tailTrace_450472 : CollatzResearch.WordTrace tailWord_450472 prefixEnd_450472 68535898486597558497281 := by
  unfold tailWord_450472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8215031812012176668820835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10953375749349568891761113 8215031812012176668820835)
  ·
    refine ⟨12322547718018265003231253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8215031812012176668820835 12322547718018265003231253)
    ·
      refine ⟨577619424282106172026465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12322547718018265003231253 577619424282106172026465)
      ·
        refine ⟨433214568211579629019849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577619424282106172026465 433214568211579629019849)
        ·
          refine ⟨324910926158684721764887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433214568211579629019849 324910926158684721764887)
          ·
            refine ⟨487366389238027082647331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324910926158684721764887 487366389238027082647331)
            ·
              refine ⟨731049583857040623970997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487366389238027082647331 731049583857040623970997)
              ·
                refine ⟨68535898486597558497281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731049583857040623970997 68535898486597558497281)
                ·
                  rfl

theorem cell20_450472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_450472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450472 prefixEnd_450472 := by exact prefixLift 450472
  have htrace : WordTrace (prefixWord ++ tailWord_450472) baseStart_450472 baseEnd_450472 := by
    simpa [prefixWord, tailWord_450472, baseEnd_450472] using wordTrace_append hprefix tailTrace_450472
  have hstable : (prefixWord ++ tailWord_450472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450472).length < 2 ^ (prefixWord ++ tailWord_450472).sum := by decide
  have hdescent : baseEnd_450472 < baseStart_450472 := by decide
  rcases family_descends (prefixWord ++ tailWord_450472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450487 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_450487 : Nat := 118140960795 + 450487 * 2 ^ 59
def prefixEnd_450487 : Nat := 4983230072969 + 3 ^ 40 * 450487 * 2
def baseEnd_450487 : Nat := 205614541868519289991781

theorem tailTrace_450487 : CollatzResearch.WordTrace tailWord_450487 prefixEnd_450487 205614541868519289991781 := by
  unfold tailWord_450487
  simp only [CollatzResearch.WordTrace]
  refine ⟨16430610718970010899437715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10953740479313340599625143 16430610718970010899437715)
  ·
    refine ⟨24645916078455016349156573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16430610718970010899437715 24645916078455016349156573)
    ·
      refine ⟨9242218529420631130933715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24645916078455016349156573 9242218529420631130933715)
      ·
        refine ⟨13863327794130946696400573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9242218529420631130933715 13863327794130946696400573)
        ·
          refine ⟨5198747922799105011150215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13863327794130946696400573 5198747922799105011150215)
          ·
            refine ⟨7798121884198657516725323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198747922799105011150215 7798121884198657516725323)
            ·
              refine ⟨11697182826297986275087985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7798121884198657516725323 11697182826297986275087985)
              ·
                refine ⟨8772887119723489706315989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11697182826297986275087985 8772887119723489706315989)
                ·
                  refine ⟨205614541868519289991781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8772887119723489706315989 205614541868519289991781)
                  ·
                    rfl

theorem cell20_450487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_450487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450487 prefixEnd_450487 := by exact prefixLift 450487
  have htrace : WordTrace (prefixWord ++ tailWord_450487) baseStart_450487 baseEnd_450487 := by
    simpa [prefixWord, tailWord_450487, baseEnd_450487] using wordTrace_append hprefix tailTrace_450487
  have hstable : (prefixWord ++ tailWord_450487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450487).length < 2 ^ (prefixWord ++ tailWord_450487).sum := by decide
  have hdescent : baseEnd_450487 < baseStart_450487 := by decide
  rcases family_descends (prefixWord ++ tailWord_450487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450556 : List Nat := [2, 2, 2, 1, 2, 2, 3, 6]
def baseStart_450556 : Nat := 118140960795 + 450556 * 2 ^ 59
def prefixEnd_450556 : Nat := 4983230072969 + 3 ^ 40 * 450556 * 2
def baseEnd_450556 : Nat := 68548678449553905563833

theorem tailTrace_450556 : CollatzResearch.WordTrace tailWord_450556 prefixEnd_450556 68548678449553905563833 := by
  unfold tailWord_450556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216563677860017841849761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10955418237146690455799681 8216563677860017841849761)
  ·
    refine ⟨6162422758395013381387321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8216563677860017841849761 6162422758395013381387321)
    ·
      refine ⟨4621817068796260036040491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6162422758395013381387321 4621817068796260036040491)
      ·
        refine ⟨6932725603194390054060737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4621817068796260036040491 6932725603194390054060737)
        ·
          refine ⟨5199544202395792540545553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6932725603194390054060737 5199544202395792540545553)
          ·
            refine ⟨3899658151796844405409165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5199544202395792540545553 3899658151796844405409165)
            ·
              refine ⟨1462371806923816652028437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3899658151796844405409165 1462371806923816652028437)
              ·
                refine ⟨68548678449553905563833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1462371806923816652028437 68548678449553905563833)
                ·
                  rfl

theorem cell20_450556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_450556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450556 prefixEnd_450556 := by exact prefixLift 450556
  have htrace : WordTrace (prefixWord ++ tailWord_450556) baseStart_450556 baseEnd_450556 := by
    simpa [prefixWord, tailWord_450556, baseEnd_450556] using wordTrace_append hprefix tailTrace_450556
  have hstable : (prefixWord ++ tailWord_450556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450556).length < 2 ^ (prefixWord ++ tailWord_450556).sum := by decide
  have hdescent : baseEnd_450556 < baseStart_450556 := by decide
  rcases family_descends (prefixWord ++ tailWord_450556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450583 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 4]
def baseStart_450583 : Nat := 118140960795 + 450583 * 2 ^ 59
def prefixEnd_450583 : Nat := 4983230072969 + 3 ^ 40 * 450583 * 2
def baseEnd_450583 : Nat := 205658358884369622791389

theorem tailTrace_450583 : CollatzResearch.WordTrace tailWord_450583 prefixEnd_450583 205658358884369622791389 := by
  unfold tailWord_450583
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434112126622219294932403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10956074751081479529954935 16434112126622219294932403)
  ·
    refine ⟨24651168189933328942398605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16434112126622219294932403 24651168189933328942398605)
    ·
      refine ⟨9244188071224998353399477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24651168189933328942398605 9244188071224998353399477)
      ·
        refine ⟨866642631677343595631201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9244188071224998353399477 866642631677343595631201)
        ·
          refine ⟨649981973758007696723401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866642631677343595631201 649981973758007696723401)
          ·
            refine ⟨487486480318505772542551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649981973758007696723401 487486480318505772542551)
            ·
              refine ⟨731229720477758658813827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487486480318505772542551 731229720477758658813827)
              ·
                refine ⟨1096844580716637988220741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731229720477758658813827 1096844580716637988220741)
                ·
                  refine ⟨205658358884369622791389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096844580716637988220741 205658358884369622791389)
                  ·
                    rfl

theorem cell20_450583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_450583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450583 prefixEnd_450583 := by exact prefixLift 450583
  have htrace : WordTrace (prefixWord ++ tailWord_450583) baseStart_450583 baseEnd_450583 := by
    simpa [prefixWord, tailWord_450583, baseEnd_450583] using wordTrace_append hprefix tailTrace_450583
  have hstable : (prefixWord ++ tailWord_450583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450583).length < 2 ^ (prefixWord ++ tailWord_450583).sum := by decide
  have hdescent : baseEnd_450583 < baseStart_450583 := by decide
  rcases family_descends (prefixWord ++ tailWord_450583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450593 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 3]
def baseStart_450593 : Nat := 118140960795 + 450593 * 2 ^ 59
def prefixEnd_450593 : Nat := 4983230072969 + 3 ^ 40 * 450593 * 2
def baseEnd_450593 : Nat := 205662923156854032458015

theorem tailTrace_450593 : CollatzResearch.WordTrace tailWord_450593 prefixEnd_450593 205662923156854032458015 := by
  unfold tailWord_450593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434476856585991002796433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10956317904390660668530955 16434476856585991002796433)
  ·
    refine ⟨12325857642439493252097325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16434476856585991002796433 12325857642439493252097325)
    ·
      refine ⟨4622196615914809969536497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12325857642439493252097325 4622196615914809969536497)
      ·
        refine ⟨3466647461936107477152373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4622196615914809969536497 3466647461936107477152373)
        ·
          refine ⟨324998199556510075983035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3466647461936107477152373 324998199556510075983035)
          ·
            refine ⟨487497299334765113974553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324998199556510075983035 487497299334765113974553)
            ·
              refine ⟨365622974501073835480915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487497299334765113974553 365622974501073835480915)
              ·
                refine ⟨548434461751610753221373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365622974501073835480915 548434461751610753221373)
                ·
                  refine ⟨205662923156854032458015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548434461751610753221373 205662923156854032458015)
                  ·
                    rfl

theorem cell20_450593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_450593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450593 prefixEnd_450593 := by exact prefixLift 450593
  have htrace : WordTrace (prefixWord ++ tailWord_450593) baseStart_450593 baseEnd_450593 := by
    simpa [prefixWord, tailWord_450593, baseEnd_450593] using wordTrace_append hprefix tailTrace_450593
  have hstable : (prefixWord ++ tailWord_450593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450593).length < 2 ^ (prefixWord ++ tailWord_450593).sum := by decide
  have hdescent : baseEnd_450593 < baseStart_450593 := by decide
  rcases family_descends (prefixWord ++ tailWord_450593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450597 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 3]
def baseStart_450597 : Nat := 118140960795 + 450597 * 2 ^ 59
def prefixEnd_450597 : Nat := 4983230072969 + 3 ^ 40 * 450597 * 2
def baseEnd_450597 : Nat := 205664748865847796324665

theorem tailTrace_450597 : CollatzResearch.WordTrace tailWord_450597 prefixEnd_450597 205664748865847796324665 := by
  unfold tailWord_450597
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434622748571499685942045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10956415165714333123961363 16434622748571499685942045)
  ·
    refine ⟨6162983530714312382228267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16434622748571499685942045 6162983530714312382228267)
    ·
      refine ⟨9244475296071468573342401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162983530714312382228267 9244475296071468573342401)
      ·
        refine ⟨6933356472053601430006801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9244475296071468573342401 6933356472053601430006801)
        ·
          refine ⟨5200017354040201072505101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6933356472053601430006801 5200017354040201072505101)
          ·
            refine ⟨1950006507765075402189413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5200017354040201072505101 1950006507765075402189413)
            ·
              refine ⟨365626220205951637910515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1950006507765075402189413 365626220205951637910515)
              ·
                refine ⟨548439330308927456865773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365626220205951637910515 548439330308927456865773)
                ·
                  refine ⟨205664748865847796324665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548439330308927456865773 205664748865847796324665)
                  ·
                    rfl

theorem cell20_450597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_450597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450597 prefixEnd_450597 := by exact prefixLift 450597
  have htrace : WordTrace (prefixWord ++ tailWord_450597) baseStart_450597 baseEnd_450597 := by
    simpa [prefixWord, tailWord_450597, baseEnd_450597] using wordTrace_append hprefix tailTrace_450597
  have hstable : (prefixWord ++ tailWord_450597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450597).length < 2 ^ (prefixWord ++ tailWord_450597).sum := by decide
  have hdescent : baseEnd_450597 < baseStart_450597 := by decide
  rcases family_descends (prefixWord ++ tailWord_450597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450638 : List Nat := [4, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_450638 : Nat := 118140960795 + 450638 * 2 ^ 59
def prefixEnd_450638 : Nat := 4983230072969 + 3 ^ 40 * 450638 * 2
def baseEnd_450638 : Nat := 205683462383033875957831

theorem tailTrace_450638 : CollatzResearch.WordTrace tailWord_450638 prefixEnd_450638 205683462383033875957831 := by
  unfold tailWord_450638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054514767677870461023071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10957412094281975792123045 2054514767677870461023071)
  ·
    refine ⟨3081772151516805691534607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2054514767677870461023071 3081772151516805691534607)
    ·
      refine ⟨4622658227275208537301911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081772151516805691534607 4622658227275208537301911)
      ·
        refine ⟨6933987340912812805952867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622658227275208537301911 6933987340912812805952867)
        ·
          refine ⟨10400981011369219208929301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933987340912812805952867 10400981011369219208929301)
          ·
            refine ⟨487545984907932150418561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10400981011369219208929301 487545984907932150418561)
            ·
              refine ⟨365659488680949112813921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487545984907932150418561 365659488680949112813921)
              ·
                refine ⟨274244616510711834610441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365659488680949112813921 274244616510711834610441)
                ·
                  refine ⟨205683462383033875957831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274244616510711834610441 205683462383033875957831)
                  ·
                    rfl

theorem cell20_450638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_450638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450638 prefixEnd_450638 := by exact prefixLift 450638
  have htrace : WordTrace (prefixWord ++ tailWord_450638) baseStart_450638 baseEnd_450638 := by
    simpa [prefixWord, tailWord_450638, baseEnd_450638] using wordTrace_append hprefix tailTrace_450638
  have hstable : (prefixWord ++ tailWord_450638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450638).length < 2 ^ (prefixWord ++ tailWord_450638).sum := by decide
  have hdescent : baseEnd_450638 < baseStart_450638 := by decide
  rcases family_descends (prefixWord ++ tailWord_450638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450656 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_450656 : Nat := 118140960795 + 450656 * 2 ^ 59
def prefixEnd_450656 : Nat := 4983230072969 + 3 ^ 40 * 450656 * 2
def baseEnd_450656 : Nat := 205691678073505813357757

theorem tailTrace_450656 : CollatzResearch.WordTrace tailWord_450656 prefixEnd_450656 205691678073505813357757 := by
  unfold tailWord_450656
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218387327678876381169911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10957849770238501841559881 8218387327678876381169911)
  ·
    refine ⟨12327580991518314571754867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8218387327678876381169911 12327580991518314571754867)
    ·
      refine ⟨18491371487277471857632301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327580991518314571754867 18491371487277471857632301)
      ·
        refine ⟨6934264307729051946612113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18491371487277471857632301 6934264307729051946612113)
        ·
          refine ⟨5200698230796788959959085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934264307729051946612113 5200698230796788959959085)
          ·
            refine ⟨1950261836548795859984657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5200698230796788959959085 1950261836548795859984657)
            ·
              refine ⟨1462696377411596894988493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1950261836548795859984657 1462696377411596894988493)
              ·
                refine ⟨548511141529348835620685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462696377411596894988493 548511141529348835620685)
                ·
                  refine ⟨205691678073505813357757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548511141529348835620685 205691678073505813357757)
                  ·
                    rfl

theorem cell20_450656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_450656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450656 prefixEnd_450656 := by exact prefixLift 450656
  have htrace : WordTrace (prefixWord ++ tailWord_450656) baseStart_450656 baseEnd_450656 := by
    simpa [prefixWord, tailWord_450656, baseEnd_450656] using wordTrace_append hprefix tailTrace_450656
  have hstable : (prefixWord ++ tailWord_450656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450656).length < 2 ^ (prefixWord ++ tailWord_450656).sum := by decide
  have hdescent : baseEnd_450656 < baseStart_450656 := by decide
  rcases family_descends (prefixWord ++ tailWord_450656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450663 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_450663 : Nat := 118140960795 + 450663 * 2 ^ 59
def prefixEnd_450663 : Nat := 4983230072969 + 3 ^ 40 * 450663 * 2
def baseEnd_450663 : Nat := 205694873064244900124395

theorem tailTrace_450663 : CollatzResearch.WordTrace tailWord_450663 prefixEnd_450663 205694873064244900124395 := by
  unfold tailWord_450663
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437029966332392957844643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10958019977554928638563095 16437029966332392957844643)
  ·
    refine ⟨24655544949498589436766965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16437029966332392957844643 24655544949498589436766965)
    ·
      refine ⟨2311457339015492759696903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24655544949498589436766965 2311457339015492759696903)
      ·
        refine ⟨3467186008523239139545355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311457339015492759696903 3467186008523239139545355)
        ·
          refine ⟨5200779012784858709318033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467186008523239139545355 5200779012784858709318033)
          ·
            refine ⟨3900584259588644031988525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5200779012784858709318033 3900584259588644031988525)
            ·
              refine ⟨1462719097345741511995697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3900584259588644031988525 1462719097345741511995697)
              ·
                refine ⟨1097039323009306133996773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462719097345741511995697 1097039323009306133996773)
                ·
                  refine ⟨205694873064244900124395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097039323009306133996773 205694873064244900124395)
                  ·
                    rfl

theorem cell20_450663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_450663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450663 prefixEnd_450663 := by exact prefixLift 450663
  have htrace : WordTrace (prefixWord ++ tailWord_450663) baseStart_450663 baseEnd_450663 := by
    simpa [prefixWord, tailWord_450663, baseEnd_450663] using wordTrace_append hprefix tailTrace_450663
  have hstable : (prefixWord ++ tailWord_450663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450663).length < 2 ^ (prefixWord ++ tailWord_450663).sum := by decide
  have hdescent : baseEnd_450663 < baseStart_450663 := by decide
  rcases family_descends (prefixWord ++ tailWord_450663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450666 : List Nat := [3, 1, 3, 2, 3, 1, 3, 4]
def baseStart_450666 : Nat := 118140960795 + 450666 * 2 ^ 59
def prefixEnd_450666 : Nat := 4983230072969 + 3 ^ 40 * 450666 * 2
def baseEnd_450666 : Nat := 68565414115330074341461

theorem tailTrace_450666 : CollatzResearch.WordTrace tailWord_450666 prefixEnd_450666 68565414115330074341461 := by
  unfold tailWord_450666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109284846330381117550963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10958092923547682980135901 4109284846330381117550963)
  ·
    refine ⟨6163927269495571676326445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4109284846330381117550963 6163927269495571676326445)
    ·
      refine ⟨2311472726060839378622417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6163927269495571676326445 2311472726060839378622417)
      ·
        refine ⟨1733604544545629533966813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2311472726060839378622417 1733604544545629533966813)
        ·
          refine ⟨650101704204611075237555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1733604544545629533966813 650101704204611075237555)
          ·
            refine ⟨975152556306916612856333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650101704204611075237555 975152556306916612856333)
            ·
              refine ⟨365682208615093729821125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 975152556306916612856333 365682208615093729821125)
              ·
                refine ⟨68565414115330074341461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365682208615093729821125 68565414115330074341461)
                ·
                  rfl

theorem cell20_450666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_450666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450666 prefixEnd_450666 := by exact prefixLift 450666
  have htrace : WordTrace (prefixWord ++ tailWord_450666) baseStart_450666 baseEnd_450666 := by
    simpa [prefixWord, tailWord_450666, baseEnd_450666] using wordTrace_append hprefix tailTrace_450666
  have hstable : (prefixWord ++ tailWord_450666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450666).length < 2 ^ (prefixWord ++ tailWord_450666).sum := by decide
  have hdescent : baseEnd_450666 < baseStart_450666 := by decide
  rcases family_descends (prefixWord ++ tailWord_450666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450756 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_450756 : Nat := 118140960795 + 450756 * 2 ^ 59
def prefixEnd_450756 : Nat := 4983230072969 + 3 ^ 40 * 450756 * 2
def baseEnd_450756 : Nat := 205737320798349910024015

theorem tailTrace_450756 : CollatzResearch.WordTrace tailWord_450756 prefixEnd_450756 205737320798349910024015 := by
  unfold tailWord_450756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220210977497734920490061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10960281303330313227320081 8220210977497734920490061)
  ·
    refine ⟨3082579116561650595183773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8220210977497734920490061 3082579116561650595183773)
    ·
      refine ⟨1155967168710618973193915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3082579116561650595183773 1155967168710618973193915)
      ·
        refine ⟨1733950753065928459790873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155967168710618973193915 1733950753065928459790873)
        ·
          refine ⟨1300463064799446344843155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733950753065928459790873 1300463064799446344843155)
          ·
            refine ⟨1950694597199169517264733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300463064799446344843155 1950694597199169517264733)
            ·
              refine ⟨731510473949688568974275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950694597199169517264733 731510473949688568974275)
              ·
                refine ⟨1097265710924532853461413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731510473949688568974275 1097265710924532853461413)
                ·
                  refine ⟨205737320798349910024015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097265710924532853461413 205737320798349910024015)
                  ·
                    rfl

theorem cell20_450756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_450756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450756 prefixEnd_450756 := by exact prefixLift 450756
  have htrace : WordTrace (prefixWord ++ tailWord_450756) baseStart_450756 baseEnd_450756 := by
    simpa [prefixWord, tailWord_450756, baseEnd_450756] using wordTrace_append hprefix tailTrace_450756
  have hstable : (prefixWord ++ tailWord_450756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450756).length < 2 ^ (prefixWord ++ tailWord_450756).sum := by decide
  have hdescent : baseEnd_450756 < baseStart_450756 := by decide
  rcases family_descends (prefixWord ++ tailWord_450756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450766 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_450766 : Nat := 118140960795 + 450766 * 2 ^ 59
def prefixEnd_450766 : Nat := 4983230072969 + 3 ^ 40 * 450766 * 2
def baseEnd_450766 : Nat := 205741885070834319690641

theorem tailTrace_450766 : CollatzResearch.WordTrace tailWord_450766 prefixEnd_450766 205741885070834319690641 := by
  unfold tailWord_450766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055098335619905193605519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10960524456639494365896101 2055098335619905193605519)
  ·
    refine ⟨3082647503429857790408279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2055098335619905193605519 3082647503429857790408279)
    ·
      refine ⟨4623971255144786685612419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3082647503429857790408279 4623971255144786685612419)
      ·
        refine ⟨6935956882717180028418629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623971255144786685612419 6935956882717180028418629)
        ·
          refine ⟨1300491915509471255328493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6935956882717180028418629 1300491915509471255328493)
          ·
            refine ⟨487684468316051720748185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1300491915509471255328493 487684468316051720748185)
            ·
              refine ⟨365763351237038790561139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487684468316051720748185 365763351237038790561139)
              ·
                refine ⟨548645026855558185841709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365763351237038790561139 548645026855558185841709)
                ·
                  refine ⟨205741885070834319690641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548645026855558185841709 205741885070834319690641)
                  ·
                    rfl

theorem cell20_450766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_450766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450766 prefixEnd_450766 := by exact prefixLift 450766
  have htrace : WordTrace (prefixWord ++ tailWord_450766) baseStart_450766 baseEnd_450766 := by
    simpa [prefixWord, tailWord_450766, baseEnd_450766] using wordTrace_append hprefix tailTrace_450766
  have hstable : (prefixWord ++ tailWord_450766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450766).length < 2 ^ (prefixWord ++ tailWord_450766).sum := by decide
  have hdescent : baseEnd_450766 < baseStart_450766 := by decide
  rcases family_descends (prefixWord ++ tailWord_450766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450794 : List Nat := [3, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_450794 : Nat := 118140960795 + 450794 * 2 ^ 59
def prefixEnd_450794 : Nat := 4983230072969 + 3 ^ 40 * 450794 * 2
def baseEnd_450794 : Nat := 205754665033790666757193

theorem tailTrace_450794 : CollatzResearch.WordTrace tailWord_450794 prefixEnd_450794 205754665033790666757193 := by
  unfold tailWord_450794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110451982214450582715859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10961205285905201553908957 4110451982214450582715859)
  ·
    refine ⟨6165677973321675874073789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4110451982214450582715859 6165677973321675874073789)
    ·
      refine ⟨2312129239995628452777671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6165677973321675874073789 2312129239995628452777671)
      ·
        refine ⟨3468193859993442679166507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312129239995628452777671 3468193859993442679166507)
        ·
          refine ⟨5202290789990164018749761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468193859993442679166507 5202290789990164018749761)
          ·
            refine ⟨3901718092492623014062321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5202290789990164018749761 3901718092492623014062321)
            ·
              refine ⟨2926288569369467260546741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901718092492623014062321 2926288569369467260546741)
              ·
                refine ⟨274339553378387555676257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2926288569369467260546741 274339553378387555676257)
                ·
                  refine ⟨205754665033790666757193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274339553378387555676257 205754665033790666757193)
                  ·
                    rfl

theorem cell20_450794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_450794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450794 prefixEnd_450794 := by exact prefixLift 450794
  have htrace : WordTrace (prefixWord ++ tailWord_450794) baseStart_450794 baseEnd_450794 := by
    simpa [prefixWord, tailWord_450794, baseEnd_450794] using wordTrace_append hprefix tailTrace_450794
  have hstable : (prefixWord ++ tailWord_450794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450794).length < 2 ^ (prefixWord ++ tailWord_450794).sum := by decide
  have hdescent : baseEnd_450794 < baseStart_450794 := by decide
  rcases family_descends (prefixWord ++ tailWord_450794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450805 : List Nat := [1, 3, 16]
def baseStart_450805 : Nat := 118140960795 + 450805 * 2 ^ 59
def prefixEnd_450805 : Nat := 4983230072969 + 3 ^ 40 * 450805 * 2
def baseEnd_450805 : Nat := 282249225971911546489

theorem tailTrace_450805 : CollatzResearch.WordTrace tailWord_450805 prefixEnd_450805 282249225971911546489 := by
  unfold tailWord_450805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16442209131817951209513869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10961472754545300806342579 16442209131817951209513869)
  ·
    refine ⟨6165828424431731703567701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16442209131817951209513869 6165828424431731703567701)
    ·
      refine ⟨282249225971911546489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 6165828424431731703567701 282249225971911546489)
      ·
        rfl

theorem cell20_450805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 16].length) (baseStart_450805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450805 prefixEnd_450805 := by exact prefixLift 450805
  have htrace : WordTrace (prefixWord ++ tailWord_450805) baseStart_450805 baseEnd_450805 := by
    simpa [prefixWord, tailWord_450805, baseEnd_450805] using wordTrace_append hprefix tailTrace_450805
  have hstable : (prefixWord ++ tailWord_450805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450805).length < 2 ^ (prefixWord ++ tailWord_450805).sum := by decide
  have hdescent : baseEnd_450805 < baseStart_450805 := by decide
  rcases family_descends (prefixWord ++ tailWord_450805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450818 : List Nat := [3, 4, 1, 1, 2, 3, 1, 5]
def baseStart_450818 : Nat := 118140960795 + 450818 * 2 ^ 59
def prefixEnd_450818 : Nat := 4983230072969 + 3 ^ 40 * 450818 * 2
def baseEnd_450818 : Nat := 68588539762584416652365

theorem tailTrace_450818 : CollatzResearch.WordTrace tailWord_450818 prefixEnd_450818 68588539762584416652365 := by
  unfold tailWord_450818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110670820192713607434277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10961788853847236286491405 4110670820192713607434277)
  ·
    refine ⟨770750778786133801393927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4110670820192713607434277 770750778786133801393927)
    ·
      refine ⟨1156126168179200702090891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770750778786133801393927 1156126168179200702090891)
      ·
        refine ⟨1734189252268801053136337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156126168179200702090891 1734189252268801053136337)
        ·
          refine ⟨1300641939201600789852253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734189252268801053136337 1300641939201600789852253)
          ·
            refine ⟨487740727200600296194595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1300641939201600789852253 487740727200600296194595)
            ·
              refine ⟨731611090800900444291893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487740727200600296194595 731611090800900444291893)
              ·
                refine ⟨68588539762584416652365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731611090800900444291893 68588539762584416652365)
                ·
                  rfl

theorem cell20_450818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_450818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450818 prefixEnd_450818 := by exact prefixLift 450818
  have htrace : WordTrace (prefixWord ++ tailWord_450818) baseStart_450818 baseEnd_450818 := by
    simpa [prefixWord, tailWord_450818, baseEnd_450818] using wordTrace_append hprefix tailTrace_450818
  have hstable : (prefixWord ++ tailWord_450818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450818).length < 2 ^ (prefixWord ++ tailWord_450818).sum := by decide
  have hdescent : baseEnd_450818 < baseStart_450818 := by decide
  rcases family_descends (prefixWord ++ tailWord_450818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450839 : List Nat := [1, 1, 3, 4, 1, 3, 3, 4]
def baseStart_450839 : Nat := 118140960795 + 450839 * 2 ^ 59
def prefixEnd_450839 : Nat := 4983230072969 + 3 ^ 40 * 450839 * 2
def baseEnd_450839 : Nat := 68591734753323503419003

theorem tailTrace_450839 : CollatzResearch.WordTrace tailWord_450839 prefixEnd_450839 68591734753323503419003 := by
  unfold tailWord_450839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16443449213694775016251571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10962299475796516677501047 16443449213694775016251571)
  ·
    refine ⟨24665173820542162524377357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16443449213694775016251571 24665173820542162524377357)
    ·
      refine ⟨9249440182703310946641509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24665173820542162524377357 9249440182703310946641509)
      ·
        refine ⟨1734270034256870802495283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9249440182703310946641509 1734270034256870802495283)
        ·
          refine ⟨2601405051385306203742925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734270034256870802495283 2601405051385306203742925)
          ·
            refine ⟨975526894269489826403597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2601405051385306203742925 975526894269489826403597)
            ·
              refine ⟨365822585351058684901349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 975526894269489826403597 365822585351058684901349)
              ·
                refine ⟨68591734753323503419003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365822585351058684901349 68591734753323503419003)
                ·
                  rfl

theorem cell20_450839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_450839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450839 prefixEnd_450839 := by exact prefixLift 450839
  have htrace : WordTrace (prefixWord ++ tailWord_450839) baseStart_450839 baseEnd_450839 := by
    simpa [prefixWord, tailWord_450839, baseEnd_450839] using wordTrace_append hprefix tailTrace_450839
  have hstable : (prefixWord ++ tailWord_450839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450839).length < 2 ^ (prefixWord ++ tailWord_450839).sum := by decide
  have hdescent : baseEnd_450839 < baseStart_450839 := by decide
  rcases family_descends (prefixWord ++ tailWord_450839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450843 : List Nat := [1, 1, 1, 1, 1, 1, 6, 8]
def baseStart_450843 : Nat := 118140960795 + 450843 * 2 ^ 59
def prefixEnd_450843 : Nat := 4983230072969 + 3 ^ 40 * 450843 * 2
def baseEnd_450843 : Nat := 68592343322988091374553

theorem tailTrace_450843 : CollatzResearch.WordTrace tailWord_450843 prefixEnd_450843 68592343322988091374553 := by
  unfold tailWord_450843
  simp only [CollatzResearch.WordTrace]
  refine ⟨16443595105680283699397183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10962396737120189132931455 16443595105680283699397183)
  ·
    refine ⟨24665392658520425549095775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16443595105680283699397183 24665392658520425549095775)
    ·
      refine ⟨36998088987780638323643663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24665392658520425549095775 36998088987780638323643663)
      ·
        refine ⟨55497133481670957485465495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36998088987780638323643663 55497133481670957485465495)
        ·
          refine ⟨83245700222506436228198243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55497133481670957485465495 83245700222506436228198243)
          ·
            refine ⟨124868550333759654342297365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83245700222506436228198243 124868550333759654342297365)
            ·
              refine ⟨5853213296894983797295189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124868550333759654342297365 5853213296894983797295189)
              ·
                refine ⟨68592343322988091374553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5853213296894983797295189 68592343322988091374553)
                ·
                  rfl

theorem cell20_450843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_450843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450843 prefixEnd_450843 := by exact prefixLift 450843
  have htrace : WordTrace (prefixWord ++ tailWord_450843) baseStart_450843 baseEnd_450843 := by
    simpa [prefixWord, tailWord_450843, baseEnd_450843] using wordTrace_append hprefix tailTrace_450843
  have hstable : (prefixWord ++ tailWord_450843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450843).length < 2 ^ (prefixWord ++ tailWord_450843).sum := by decide
  have hdescent : baseEnd_450843 < baseStart_450843 := by decide
  rcases family_descends (prefixWord ++ tailWord_450843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450867 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_450867 : Nat := 118140960795 + 450867 * 2 ^ 59
def prefixEnd_450867 : Nat := 4983230072969 + 3 ^ 40 * 450867 * 2
def baseEnd_450867 : Nat := 205787984222926857323561

theorem tailTrace_450867 : CollatzResearch.WordTrace tailWord_450867 prefixEnd_450867 205787984222926857323561 := by
  unfold tailWord_450867
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444470457593335798270855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10962980305062223865513903 16444470457593335798270855)
  ·
    refine ⟨24666705686390003697406283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16444470457593335798270855 24666705686390003697406283)
    ·
      refine ⟨37000058529585005546109425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24666705686390003697406283 37000058529585005546109425)
      ·
        refine ⟨27750043897188754159582069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37000058529585005546109425 27750043897188754159582069)
        ·
          refine ⟨2601566615361445702460819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27750043897188754159582069 2601566615361445702460819)
          ·
            refine ⟨3902349923042168553691229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601566615361445702460819 3902349923042168553691229)
            ·
              refine ⟨1463381221140813207634211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3902349923042168553691229 1463381221140813207634211)
              ·
                refine ⟨2195071831711219811451317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463381221140813207634211 2195071831711219811451317)
                ·
                  refine ⟨205787984222926857323561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2195071831711219811451317 205787984222926857323561)
                  ·
                    rfl

theorem cell20_450867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_450867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450867 prefixEnd_450867 := by exact prefixLift 450867
  have htrace : WordTrace (prefixWord ++ tailWord_450867) baseStart_450867 baseEnd_450867 := by
    simpa [prefixWord, tailWord_450867, baseEnd_450867] using wordTrace_append hprefix tailTrace_450867
  have hstable : (prefixWord ++ tailWord_450867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450867).length < 2 ^ (prefixWord ++ tailWord_450867).sum := by decide
  have hdescent : baseEnd_450867 < baseStart_450867 := by decide
  rcases family_descends (prefixWord ++ tailWord_450867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450922 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_450922 : Nat := 118140960795 + 450922 * 2 ^ 59
def prefixEnd_450922 : Nat := 4983230072969 + 3 ^ 40 * 450922 * 2
def baseEnd_450922 : Nat := 205813087721591110490003

theorem tailTrace_450922 : CollatzResearch.WordTrace tailWord_450922 prefixEnd_450922 205813087721591110490003 := by
  unfold tailWord_450922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111619118098520047880755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10964317648262720127682013 4111619118098520047880755)
  ·
    refine ⟨6167428677147780071821133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4111619118098520047880755 6167428677147780071821133)
    ·
      refine ⟨2312785753930417526932925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6167428677147780071821133 2312785753930417526932925)
      ·
        refine ⟨867294657723906572599847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2312785753930417526932925 867294657723906572599847)
        ·
          refine ⟨1300941986585859858899771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867294657723906572599847 1300941986585859858899771)
          ·
            refine ⟨1951412979878789788349657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300941986585859858899771 1951412979878789788349657)
            ·
              refine ⟨1463559734909092341262243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951412979878789788349657 1463559734909092341262243)
              ·
                refine ⟨2195339602363638511893365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463559734909092341262243 2195339602363638511893365)
                ·
                  refine ⟨205813087721591110490003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2195339602363638511893365 205813087721591110490003)
                  ·
                    rfl

theorem cell20_450922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_450922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450922 prefixEnd_450922 := by exact prefixLift 450922
  have htrace : WordTrace (prefixWord ++ tailWord_450922) baseStart_450922 baseEnd_450922 := by
    simpa [prefixWord, tailWord_450922, baseEnd_450922] using wordTrace_append hprefix tailTrace_450922
  have hstable : (prefixWord ++ tailWord_450922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450922).length < 2 ^ (prefixWord ++ tailWord_450922).sum := by decide
  have hdescent : baseEnd_450922 < baseStart_450922 := by decide
  rcases family_descends (prefixWord ++ tailWord_450922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450925 : List Nat := [1, 5, 1, 1, 1, 2, 5, 2, 2]
def baseStart_450925 : Nat := 118140960795 + 450925 * 2 ^ 59
def prefixEnd_450925 : Nat := 4983230072969 + 3 ^ 40 * 450925 * 2
def baseEnd_450925 : Nat := 205814457003336433389991

theorem tailTrace_450925 : CollatzResearch.WordTrace tailWord_450925 prefixEnd_450925 205814457003336433389991 := by
  unfold tailWord_450925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446585891383211703882229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10964390594255474469254819 16446585891383211703882229)
  ·
    refine ⟨1541867427317176097238959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16446585891383211703882229 1541867427317176097238959)
    ·
      refine ⟨2312801140975764145858439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541867427317176097238959 2312801140975764145858439)
      ·
        refine ⟨3469201711463646218787659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312801140975764145858439 3469201711463646218787659)
        ·
          refine ⟨5203802567195469328181489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469201711463646218787659 5203802567195469328181489)
          ·
            refine ⟨3902851925396601996136117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5203802567195469328181489 3902851925396601996136117)
            ·
              refine ⟨365892368005931437137761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3902851925396601996136117 365892368005931437137761)
              ·
                refine ⟨274419276004448577853321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365892368005931437137761 274419276004448577853321)
                ·
                  refine ⟨205814457003336433389991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274419276004448577853321 205814457003336433389991)
                  ·
                    rfl

theorem cell20_450925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_450925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450925 prefixEnd_450925 := by exact prefixLift 450925
  have htrace : WordTrace (prefixWord ++ tailWord_450925) baseStart_450925 baseEnd_450925 := by
    simpa [prefixWord, tailWord_450925, baseEnd_450925] using wordTrace_append hprefix tailTrace_450925
  have hstable : (prefixWord ++ tailWord_450925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450925).length < 2 ^ (prefixWord ++ tailWord_450925).sum := by decide
  have hdescent : baseEnd_450925 < baseStart_450925 := by decide
  rcases family_descends (prefixWord ++ tailWord_450925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450939 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 3]
def baseStart_450939 : Nat := 118140960795 + 450939 * 2 ^ 59
def prefixEnd_450939 : Nat := 4983230072969 + 3 ^ 40 * 450939 * 2
def baseEnd_450939 : Nat := 205820846984814606923267

theorem tailTrace_450939 : CollatzResearch.WordTrace tailWord_450939 prefixEnd_450939 205820846984814606923267 := by
  unfold tailWord_450939
  simp only [CollatzResearch.WordTrace]
  refine ⟨16447096513332492094891871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10964731008888328063261247 16447096513332492094891871)
  ·
    refine ⟨24670644769998738142337807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16447096513332492094891871 24670644769998738142337807)
    ·
      refine ⟨37005967154998107213506711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24670644769998738142337807 37005967154998107213506711)
      ·
        refine ⟨55508950732497160820260067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37005967154998107213506711 55508950732497160820260067)
        ·
          refine ⟨83263426098745741230390101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55508950732497160820260067 83263426098745741230390101)
          ·
            refine ⟨487871637297338327521817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 83263426098745741230390101 487871637297338327521817)
            ·
              refine ⟨365903727973003745641363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487871637297338327521817 365903727973003745641363)
              ·
                refine ⟨548855591959505618462045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365903727973003745641363 548855591959505618462045)
                ·
                  refine ⟨205820846984814606923267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548855591959505618462045 205820846984814606923267)
                  ·
                    rfl

theorem cell20_450939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 3].length) (baseStart_450939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450939 prefixEnd_450939 := by exact prefixLift 450939
  have htrace : WordTrace (prefixWord ++ tailWord_450939) baseStart_450939 baseEnd_450939 := by
    simpa [prefixWord, tailWord_450939, baseEnd_450939] using wordTrace_append hprefix tailTrace_450939
  have hstable : (prefixWord ++ tailWord_450939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450939).length < 2 ^ (prefixWord ++ tailWord_450939).sum := by decide
  have hdescent : baseEnd_450939 < baseStart_450939 := by decide
  rcases family_descends (prefixWord ++ tailWord_450939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450943 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 3]
def baseStart_450943 : Nat := 118140960795 + 450943 * 2 ^ 59
def prefixEnd_450943 : Nat := 4983230072969 + 3 ^ 40 * 450943 * 2
def baseEnd_450943 : Nat := 205822672693808370789917

theorem tailTrace_450943 : CollatzResearch.WordTrace tailWord_450943 prefixEnd_450943 205822672693808370789917 := by
  unfold tailWord_450943
  simp only [CollatzResearch.WordTrace]
  refine ⟨16447242405318000778037483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10964828270212000518691655 16447242405318000778037483)
  ·
    refine ⟨24670863607977001167056225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16447242405318000778037483 24670863607977001167056225)
    ·
      refine ⟨18503147705982750875292169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24670863607977001167056225 18503147705982750875292169)
      ·
        refine ⟨13877360779487063156469127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18503147705982750875292169 13877360779487063156469127)
        ·
          refine ⟨20816041169230594734703691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13877360779487063156469127 20816041169230594734703691)
          ·
            refine ⟨31224061753845892102055537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20816041169230594734703691 31224061753845892102055537)
            ·
              refine ⟨23418046315384419076541653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31224061753845892102055537 23418046315384419076541653)
              ·
                refine ⟨548860460516822322106445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23418046315384419076541653 548860460516822322106445)
                ·
                  refine ⟨205822672693808370789917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548860460516822322106445 205822672693808370789917)
                  ·
                    rfl

theorem cell20_450943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_450943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450943 prefixEnd_450943 := by exact prefixLift 450943
  have htrace : WordTrace (prefixWord ++ tailWord_450943) baseStart_450943 baseEnd_450943 := by
    simpa [prefixWord, tailWord_450943, baseEnd_450943] using wordTrace_append hprefix tailTrace_450943
  have hstable : (prefixWord ++ tailWord_450943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450943).length < 2 ^ (prefixWord ++ tailWord_450943).sum := by decide
  have hdescent : baseEnd_450943 < baseStart_450943 := by decide
  rcases family_descends (prefixWord ++ tailWord_450943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450988 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_450988 : Nat := 118140960795 + 450988 * 2 ^ 59
def prefixEnd_450988 : Nat := 4983230072969 + 3 ^ 40 * 450988 * 2
def baseEnd_450988 : Nat := 205843211919988214289733

theorem tailTrace_450988 : CollatzResearch.WordTrace tailWord_450988 prefixEnd_450988 205843211919988214289733 := by
  unfold tailWord_450988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224441845077486731712809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10965922460103315642283745 8224441845077486731712809)
  ·
    refine ⟨6168331383808115048784607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8224441845077486731712809 6168331383808115048784607)
    ·
      refine ⟨9252497075712172573176911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6168331383808115048784607 9252497075712172573176911)
      ·
        refine ⟨13878745613568258859765367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9252497075712172573176911 13878745613568258859765367)
        ·
          refine ⟨20818118420352388289648051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13878745613568258859765367 20818118420352388289648051)
          ·
            refine ⟨31227177630528582434472077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20818118420352388289648051 31227177630528582434472077)
            ·
              refine ⟨11710191611448218412927029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31227177630528582434472077 11710191611448218412927029)
              ·
                refine ⟨1097830463573270476211909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11710191611448218412927029 1097830463573270476211909)
                ·
                  refine ⟨205843211919988214289733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097830463573270476211909 205843211919988214289733)
                  ·
                    rfl

theorem cell20_450988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_450988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_450988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_450988 prefixEnd_450988 := by exact prefixLift 450988
  have htrace : WordTrace (prefixWord ++ tailWord_450988) baseStart_450988 baseEnd_450988 := by
    simpa [prefixWord, tailWord_450988, baseEnd_450988] using wordTrace_append hprefix tailTrace_450988
  have hstable : (prefixWord ++ tailWord_450988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450988).length < 2 ^ (prefixWord ++ tailWord_450988).sum := by decide
  have hdescent : baseEnd_450988 < baseStart_450988 := by decide
  rcases family_descends (prefixWord ++ tailWord_450988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451005 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_451005 : Nat := 118140960795 + 451005 * 2 ^ 59
def prefixEnd_451005 : Nat := 4983230072969 + 3 ^ 40 * 451005 * 2
def baseEnd_451005 : Nat := 205850971183211710722997

theorem tailTrace_451005 : CollatzResearch.WordTrace tailWord_451005 prefixEnd_451005 205850971183211710722997 := by
  unfold tailWord_451005
  simp only [CollatzResearch.WordTrace]
  refine ⟨16449503731093385366794469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10966335820728923577862979 16449503731093385366794469)
  ·
    refine ⟨3084281949580009756273963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16449503731093385366794469 3084281949580009756273963)
    ·
      refine ⟨4626422924370014634410945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084281949580009756273963 4626422924370014634410945)
      ·
        refine ⟨3469817193277510975808209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4626422924370014634410945 3469817193277510975808209)
        ·
          refine ⟨2602362894958133231856157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3469817193277510975808209 2602362894958133231856157)
          ·
            refine ⟨975886085609299961946059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2602362894958133231856157 975886085609299961946059)
            ·
              refine ⟨1463829128413949942919089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975886085609299961946059 1463829128413949942919089)
              ·
                refine ⟨1097871846310462457189317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463829128413949942919089 1097871846310462457189317)
                ·
                  refine ⟨205850971183211710722997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097871846310462457189317 205850971183211710722997)
                  ·
                    rfl

theorem cell20_451005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_451005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451005 prefixEnd_451005 := by exact prefixLift 451005
  have htrace : WordTrace (prefixWord ++ tailWord_451005) baseStart_451005 baseEnd_451005 := by
    simpa [prefixWord, tailWord_451005, baseEnd_451005] using wordTrace_append hprefix tailTrace_451005
  have hstable : (prefixWord ++ tailWord_451005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451005).length < 2 ^ (prefixWord ++ tailWord_451005).sum := by decide
  have hdescent : baseEnd_451005 < baseStart_451005 := by decide
  rcases family_descends (prefixWord ++ tailWord_451005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451033 : List Nat := [1, 2, 1, 2, 4, 1, 9]
def baseStart_451033 : Nat := 118140960795 + 451033 * 2 ^ 59
def prefixEnd_451033 : Nat := 4983230072969 + 3 ^ 40 * 451033 * 2
def baseEnd_451033 : Nat := 22873750127352006421061

theorem tailTrace_451033 : CollatzResearch.WordTrace tailWord_451033 prefixEnd_451033 22873750127352006421061 := by
  unfold tailWord_451033
  simp only [CollatzResearch.WordTrace]
  refine ⟨16450524974991946148813753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10967016649994630765875835 16450524974991946148813753)
  ·
    refine ⟨12337893731243959611610315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16450524974991946148813753 12337893731243959611610315)
    ·
      refine ⟨18506840596865939417415473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12337893731243959611610315 18506840596865939417415473)
      ·
        refine ⟨13880130447649454563061605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18506840596865939417415473 13880130447649454563061605)
        ·
          refine ⟨2602524458934272730574051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13880130447649454563061605 2602524458934272730574051)
          ·
            refine ⟨3903786688401409095861077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602524458934272730574051 3903786688401409095861077)
            ·
              refine ⟨22873750127352006421061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3903786688401409095861077 22873750127352006421061)
              ·
                rfl

theorem cell20_451033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_451033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451033 prefixEnd_451033 := by exact prefixLift 451033
  have htrace : WordTrace (prefixWord ++ tailWord_451033) baseStart_451033 baseEnd_451033 := by
    simpa [prefixWord, tailWord_451033, baseEnd_451033] using wordTrace_append hprefix tailTrace_451033
  have hstable : (prefixWord ++ tailWord_451033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451033).length < 2 ^ (prefixWord ++ tailWord_451033).sum := by decide
  have hdescent : baseEnd_451033 < baseStart_451033 := by decide
  rcases family_descends (prefixWord ++ tailWord_451033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451064 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_451064 : Nat := 118140960795 + 451064 * 2 ^ 59
def prefixEnd_451064 : Nat := 4983230072969 + 3 ^ 40 * 451064 * 2
def baseEnd_451064 : Nat := 205877900390869727756089

theorem tailTrace_451064 : CollatzResearch.WordTrace tailWord_451064 prefixEnd_451064 205877900390869727756089 := by
  unfold tailWord_451064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225827818939819221596123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10967770425253092295461497 8225827818939819221596123)
  ·
    refine ⟨12338741728409728832394185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8225827818939819221596123 12338741728409728832394185)
    ·
      refine ⟨9254056296307296624295639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12338741728409728832394185 9254056296307296624295639)
      ·
        refine ⟨13881084444460944936443459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9254056296307296624295639 13881084444460944936443459)
        ·
          refine ⟨20821626666691417404665189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13881084444460944936443459 20821626666691417404665189)
          ·
            refine ⟨3904055000004640763374723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20821626666691417404665189 3904055000004640763374723)
            ·
              refine ⟨5856082500006961145062085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904055000004640763374723 5856082500006961145062085)
              ·
                refine ⟨1098015468751305214699141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5856082500006961145062085 1098015468751305214699141)
                ·
                  refine ⟨205877900390869727756089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1098015468751305214699141 205877900390869727756089)
                  ·
                    rfl

theorem cell20_451064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_451064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451064 prefixEnd_451064 := by exact prefixLift 451064
  have htrace : WordTrace (prefixWord ++ tailWord_451064) baseStart_451064 baseEnd_451064 := by
    simpa [prefixWord, tailWord_451064, baseEnd_451064] using wordTrace_append hprefix tailTrace_451064
  have hstable : (prefixWord ++ tailWord_451064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451064).length < 2 ^ (prefixWord ++ tailWord_451064).sum := by decide
  have hdescent : baseEnd_451064 < baseStart_451064 := by decide
  rcases family_descends (prefixWord ++ tailWord_451064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451071 : List Nat := [1, 1, 2, 2, 1, 2, 5, 6]
def baseStart_451071 : Nat := 118140960795 + 451071 * 2 ^ 59
def prefixEnd_451071 : Nat := 4983230072969 + 3 ^ 40 * 451071 * 2
def baseEnd_451071 : Nat := 68627031793869604840909

theorem tailTrace_451071 : CollatzResearch.WordTrace tailWord_451071 prefixEnd_451071 68627031793869604840909 := by
  unfold tailWord_451071
  simp only [CollatzResearch.WordTrace]
  refine ⟨16451910948854278638697067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10967940632569519092464711 16451910948854278638697067)
  ·
    refine ⟨24677866423281417958045601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16451910948854278638697067 24677866423281417958045601)
    ·
      refine ⟨18508399817461063468534201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24677866423281417958045601 18508399817461063468534201)
      ·
        refine ⟨13881299863095797601400651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18508399817461063468534201 13881299863095797601400651)
        ·
          refine ⟨20821949794643696402100977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13881299863095797601400651 20821949794643696402100977)
          ·
            refine ⟨15616462345982772301575733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20821949794643696402100977 15616462345982772301575733)
            ·
              refine ⟨1464043344935884903272725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15616462345982772301575733 1464043344935884903272725)
              ·
                refine ⟨68627031793869604840909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1464043344935884903272725 68627031793869604840909)
                ·
                  rfl

theorem cell20_451071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_451071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451071 prefixEnd_451071 := by exact prefixLift 451071
  have htrace : WordTrace (prefixWord ++ tailWord_451071) baseStart_451071 baseEnd_451071 := by
    simpa [prefixWord, tailWord_451071, baseEnd_451071] using wordTrace_append hprefix tailTrace_451071
  have hstable : (prefixWord ++ tailWord_451071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451071).length < 2 ^ (prefixWord ++ tailWord_451071).sum := by decide
  have hdescent : baseEnd_451071 < baseStart_451071 := by decide
  rcases family_descends (prefixWord ++ tailWord_451071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
