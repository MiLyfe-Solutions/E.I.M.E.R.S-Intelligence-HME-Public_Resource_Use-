import V185TrunkScan23Chunk0397

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2353759 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 10]
def baseStart_2353759 : Nat := 118140960795 + 2353759 * 2 ^ 59
def prefixEnd_2353759 : Nat := 4983230072969 + 3 ^ 40 * 2353759 * 2
def baseEnd_2353759 : Nat := 402869903948720546929255

theorem tailTrace_2353759 : CollatzResearch.WordTrace tailWord_2353759 prefixEnd_2353759 402869903948720546929255 := by
  unfold tailWord_2353759
  simp only [CollatzResearch.WordTrace]
  refine ⟨85848643479740607878248331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57232428986493738585498887 85848643479740607878248331)
  ·
    refine ⟨128772965219610911817372497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85848643479740607878248331 128772965219610911817372497)
    ·
      refine ⟨96579723914708183863029373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128772965219610911817372497 96579723914708183863029373)
      ·
        refine ⟨36217396468015568948636015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96579723914708183863029373 36217396468015568948636015)
        ·
          refine ⟨54326094702023353422954023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36217396468015568948636015 54326094702023353422954023)
          ·
            refine ⟨81489142053035030134431035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54326094702023353422954023 81489142053035030134431035)
            ·
              refine ⟨122233713079552545201646553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81489142053035030134431035 122233713079552545201646553)
              ·
                refine ⟨91675284809664408901234915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122233713079552545201646553 91675284809664408901234915)
                ·
                  refine ⟨137512927214496613351852373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91675284809664408901234915 137512927214496613351852373)
                  ·
                    refine ⟨402869903948720546929255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 137512927214496613351852373 402869903948720546929255)
                    ·
                      rfl

theorem cell23_2353759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_2353759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353759 prefixEnd_2353759 := by exact prefixLift 2353759
  have htrace : WordTrace (prefixWord ++ tailWord_2353759) baseStart_2353759 baseEnd_2353759 := by
    simpa [prefixWord, tailWord_2353759, baseEnd_2353759] using wordTrace_append hprefix tailTrace_2353759
  have hstable : (prefixWord ++ tailWord_2353759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353759).length < 2 ^ (prefixWord ++ tailWord_2353759).sum := by decide
  have hdescent : baseEnd_2353759 < baseStart_2353759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353783 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 2, 4, 2]
def baseStart_2353783 : Nat := 118140960795 + 2353783 * 2 ^ 59
def prefixEnd_2353783 : Nat := 4983230072969 + 3 ^ 40 * 2353783 * 2
def baseEnd_2353783 : Nat := 1208622035381869546887655

theorem tailTrace_2353783 : CollatzResearch.WordTrace tailWord_2353783 prefixEnd_2353783 1208622035381869546887655 := by
  unfold tailWord_2353783
  simp only [CollatzResearch.WordTrace]
  refine ⟨85849518831653659977122003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57233012554435773318081335 85849518831653659977122003)
  ·
    refine ⟨128774278247480489965683005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85849518831653659977122003 128774278247480489965683005)
    ·
      refine ⟨48290354342805183737131127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128774278247480489965683005 48290354342805183737131127)
      ·
        refine ⟨72435531514207775605696691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48290354342805183737131127 72435531514207775605696691)
        ·
          refine ⟨108653297271311663408545037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72435531514207775605696691 108653297271311663408545037)
          ·
            refine ⟨40744986476741873778204389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108653297271311663408545037 40744986476741873778204389)
            ·
              refine ⟨7639684964389101333413323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40744986476741873778204389 7639684964389101333413323)
              ·
                refine ⟨11459527446583652000119985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7639684964389101333413323 11459527446583652000119985)
                ·
                  refine ⟨8594645584937739000089989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11459527446583652000119985 8594645584937739000089989)
                  ·
                    refine ⟨1611496047175826062516873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8594645584937739000089989 1611496047175826062516873)
                    ·
                      refine ⟨1208622035381869546887655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611496047175826062516873 1208622035381869546887655)
                      ·
                        rfl

theorem cell23_2353783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_2353783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353783 prefixEnd_2353783 := by exact prefixLift 2353783
  have htrace : WordTrace (prefixWord ++ tailWord_2353783) baseStart_2353783 baseEnd_2353783 := by
    simpa [prefixWord, tailWord_2353783, baseEnd_2353783] using wordTrace_append hprefix tailTrace_2353783
  have hstable : (prefixWord ++ tailWord_2353783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353783).length < 2 ^ (prefixWord ++ tailWord_2353783).sum := by decide
  have hdescent : baseEnd_2353783 < baseStart_2353783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353793 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2353793 : Nat := 118140960795 + 2353793 * 2 ^ 59
def prefixEnd_2353793 : Nat := 4983230072969 + 3 ^ 40 * 2353793 * 2
def baseEnd_2353793 : Nat := 402875723396138169254203

theorem tailTrace_2353793 : CollatzResearch.WordTrace tailWord_2353793 prefixEnd_2353793 402875723396138169254203 := by
  unfold tailWord_2353793
  simp only [CollatzResearch.WordTrace]
  refine ⟨85849883561617431684986033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57233255707744954456657355 85849883561617431684986033)
  ·
    refine ⟨64387412671213073763739525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85849883561617431684986033 64387412671213073763739525)
    ·
      refine ⟨12072639875852451330701161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64387412671213073763739525 12072639875852451330701161)
      ·
        refine ⟨9054479906889338498025871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12072639875852451330701161 9054479906889338498025871)
        ·
          refine ⟨13581719860334007747038807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9054479906889338498025871 13581719860334007747038807)
          ·
            refine ⟨20372579790501011620558211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13581719860334007747038807 20372579790501011620558211)
            ·
              refine ⟨30558869685751517430837317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20372579790501011620558211 30558869685751517430837317)
              ·
                refine ⟨5729788066078409518281997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30558869685751517430837317 5729788066078409518281997)
                ·
                  refine ⟨2148670524779403569355749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5729788066078409518281997 2148670524779403569355749)
                  ·
                    refine ⟨402875723396138169254203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2148670524779403569355749 402875723396138169254203)
                    ·
                      rfl

theorem cell23_2353793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2353793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353793 prefixEnd_2353793 := by exact prefixLift 2353793
  have htrace : WordTrace (prefixWord ++ tailWord_2353793) baseStart_2353793 baseEnd_2353793 := by
    simpa [prefixWord, tailWord_2353793, baseEnd_2353793] using wordTrace_append hprefix tailTrace_2353793
  have hstable : (prefixWord ++ tailWord_2353793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353793).length < 2 ^ (prefixWord ++ tailWord_2353793).sum := by decide
  have hdescent : baseEnd_2353793 < baseStart_2353793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353806 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_2353806 : Nat := 118140960795 + 2353806 * 2 ^ 59
def prefixEnd_2353806 : Nat := 4983230072969 + 3 ^ 40 * 2353806 * 2
def baseEnd_2353806 : Nat := 134292649492991439655561

theorem tailTrace_2353806 : CollatzResearch.WordTrace tailWord_2353806 prefixEnd_2353806 134292649492991439655561 := by
  unfold tailWord_2353806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10731294713821291863151159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57233571807046889936806181 10731294713821291863151159)
  ·
    refine ⟨16096942070731937794726739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10731294713821291863151159 16096942070731937794726739)
    ·
      refine ⟨24145413106097906692090109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16096942070731937794726739 24145413106097906692090109)
      ·
        refine ⟨9054529914786715009533791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24145413106097906692090109 9054529914786715009533791)
        ·
          refine ⟨13581794872180072514300687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9054529914786715009533791 13581794872180072514300687)
          ·
            refine ⟨20372692308270108771451031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13581794872180072514300687 20372692308270108771451031)
            ·
              refine ⟨30559038462405163157176547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20372692308270108771451031 30559038462405163157176547)
              ·
                refine ⟨45838557693607744735764821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30559038462405163157176547 45838557693607744735764821)
                ·
                  refine ⟨134292649492991439655561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 45838557693607744735764821 134292649492991439655561)
                  ·
                    rfl

theorem cell23_2353806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_2353806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353806 prefixEnd_2353806 := by exact prefixLift 2353806
  have htrace : WordTrace (prefixWord ++ tailWord_2353806) baseStart_2353806 baseEnd_2353806 := by
    simpa [prefixWord, tailWord_2353806, baseEnd_2353806] using wordTrace_append hprefix tailTrace_2353806
  have hstable : (prefixWord ++ tailWord_2353806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353806).length < 2 ^ (prefixWord ++ tailWord_2353806).sum := by decide
  have hdescent : baseEnd_2353806 < baseStart_2353806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353820 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2353820 : Nat := 118140960795 + 2353820 * 2 ^ 59
def prefixEnd_2353820 : Nat := 4983230072969 + 3 ^ 40 * 2353820 * 2
def baseEnd_2353820 : Nat := 1208641034166085902124985

theorem tailTrace_2353820 : CollatzResearch.WordTrace tailWord_2353820 prefixEnd_2353820 1208641034166085902124985 := by
  unfold tailWord_2353820
  simp only [CollatzResearch.WordTrace]
  refine ⟨42925434166259807648109457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57233912221679743530812609 42925434166259807648109457)
  ·
    refine ⟨32194075624694855736082093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42925434166259807648109457 32194075624694855736082093)
    ·
      refine ⟨12072778359260570901030785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32194075624694855736082093 12072778359260570901030785)
      ·
        refine ⟨9054583769445428175773089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12072778359260570901030785 9054583769445428175773089)
        ·
          refine ⟨6790937827084071131829817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9054583769445428175773089 6790937827084071131829817)
          ·
            refine ⟨5093203370313053348872363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6790937827084071131829817 5093203370313053348872363)
            ·
              refine ⟨7639805055469580023308545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093203370313053348872363 7639805055469580023308545)
              ·
                refine ⟨5729853791602185017481409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7639805055469580023308545 5729853791602185017481409)
                ·
                  refine ⟨4297390343701638763111057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5729853791602185017481409 4297390343701638763111057)
                  ·
                    refine ⟨3223042757776229072333293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4297390343701638763111057 3223042757776229072333293)
                    ·
                      refine ⟨1208641034166085902124985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3223042757776229072333293 1208641034166085902124985)
                      ·
                        rfl

theorem cell23_2353820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2353820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353820 prefixEnd_2353820 := by exact prefixLift 2353820
  have htrace : WordTrace (prefixWord ++ tailWord_2353820) baseStart_2353820 baseEnd_2353820 := by
    simpa [prefixWord, tailWord_2353820, baseEnd_2353820] using wordTrace_append hprefix tailTrace_2353820
  have hstable : (prefixWord ++ tailWord_2353820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353820).length < 2 ^ (prefixWord ++ tailWord_2353820).sum := by decide
  have hdescent : baseEnd_2353820 < baseStart_2353820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353853 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_2353853 : Nat := 118140960795 + 2353853 * 2 ^ 59
def prefixEnd_2353853 : Nat := 4983230072969 + 3 ^ 40 * 2353853 * 2
def baseEnd_2353853 : Nat := 402885993009228091004111

theorem tailTrace_2353853 : CollatzResearch.WordTrace tailWord_2353853 prefixEnd_2353853 402885993009228091004111 := by
  unfold tailWord_2353853
  simp only [CollatzResearch.WordTrace]
  refine ⟨85852071941400061932170213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57234714627600041288113475 85852071941400061932170213)
  ·
    refine ⟨16097263489012511612281915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85852071941400061932170213 16097263489012511612281915)
    ·
      refine ⟨24145895233518767418422873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16097263489012511612281915 24145895233518767418422873)
      ·
        refine ⟨18109421425139075563817155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24145895233518767418422873 18109421425139075563817155)
        ·
          refine ⟨27164132137708613345725733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18109421425139075563817155 27164132137708613345725733)
          ·
            refine ⟨5093274775820365002323575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27164132137708613345725733 5093274775820365002323575)
            ·
              refine ⟨7639912163730547503485363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093274775820365002323575 7639912163730547503485363)
              ·
                refine ⟨11459868245595821255228045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7639912163730547503485363 11459868245595821255228045)
                ·
                  refine ⟨4297450592098432970710517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11459868245595821255228045 4297450592098432970710517)
                  ·
                    refine ⟨402885993009228091004111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4297450592098432970710517 402885993009228091004111)
                    ·
                      rfl

theorem cell23_2353853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_2353853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353853 prefixEnd_2353853 := by exact prefixLift 2353853
  have htrace : WordTrace (prefixWord ++ tailWord_2353853) baseStart_2353853 baseEnd_2353853 := by
    simpa [prefixWord, tailWord_2353853, baseEnd_2353853] using wordTrace_append hprefix tailTrace_2353853
  have hstable : (prefixWord ++ tailWord_2353853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353853).length < 2 ^ (prefixWord ++ tailWord_2353853).sum := by decide
  have hdescent : baseEnd_2353853 < baseStart_2353853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353903 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_2353903 : Nat := 118140960795 + 2353903 * 2 ^ 59
def prefixEnd_2353903 : Nat := 4983230072969 + 3 ^ 40 * 2353903 * 2
def baseEnd_2353903 : Nat := 1208683653060409077387103

theorem tailTrace_2353903 : CollatzResearch.WordTrace tailWord_2353903 prefixEnd_2353903 1208683653060409077387103 := by
  unfold tailWord_2353903
  simp only [CollatzResearch.WordTrace]
  refine ⟨85853895591218920471490363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57235930394145946980993575 85853895591218920471490363)
  ·
    refine ⟨128780843386828380707235545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85853895591218920471490363 128780843386828380707235545)
    ·
      refine ⟨96585632540121285530426659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128780843386828380707235545 96585632540121285530426659)
      ·
        refine ⟨144878448810181928295639989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96585632540121285530426659 144878448810181928295639989)
        ·
          refine ⟨13582354575954555777716249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144878448810181928295639989 13582354575954555777716249)
          ·
            refine ⟨10186765931965916833287187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13582354575954555777716249 10186765931965916833287187)
            ·
              refine ⟨15280148897948875249930781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10186765931965916833287187 15280148897948875249930781)
              ·
                refine ⟨5730055836730828218724043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15280148897948875249930781 5730055836730828218724043)
                ·
                  refine ⟨8595083755096242328086065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5730055836730828218724043 8595083755096242328086065)
                  ·
                    refine ⟨6446312816322181746064549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8595083755096242328086065 6446312816322181746064549)
                    ·
                      refine ⟨1208683653060409077387103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6446312816322181746064549 1208683653060409077387103)
                      ·
                        rfl

theorem cell23_2353903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_2353903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353903 prefixEnd_2353903 := by exact prefixLift 2353903
  have htrace : WordTrace (prefixWord ++ tailWord_2353903) baseStart_2353903 baseEnd_2353903 := by
    simpa [prefixWord, tailWord_2353903, baseEnd_2353903] using wordTrace_append hprefix tailTrace_2353903
  have hstable : (prefixWord ++ tailWord_2353903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353903).length < 2 ^ (prefixWord ++ tailWord_2353903).sum := by decide
  have hdescent : baseEnd_2353903 < baseStart_2353903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353910 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2353910 : Nat := 118140960795 + 2353910 * 2 ^ 59
def prefixEnd_2353910 : Nat := 4983230072969 + 3 ^ 40 * 2353910 * 2
def baseEnd_2353910 : Nat := 1208687247424990549999571

theorem tailTrace_2353910 : CollatzResearch.WordTrace tailWord_2353910 prefixEnd_2353910 1208687247424990549999571 := by
  unfold tailWord_2353910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365884431387097541687199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57236100601462373777996789 5365884431387097541687199)
  ·
    refine ⟨8048826647080646312530799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5365884431387097541687199 8048826647080646312530799)
    ·
      refine ⟨12073239970620969468796199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8048826647080646312530799 12073239970620969468796199)
      ·
        refine ⟨18109859955931454203194299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12073239970620969468796199 18109859955931454203194299)
        ·
          refine ⟨27164789933897181304791449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18109859955931454203194299 27164789933897181304791449)
          ·
            refine ⟨20373592450422885978593587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27164789933897181304791449 20373592450422885978593587)
            ·
              refine ⟨30560388675634328967890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20373592450422885978593587 30560388675634328967890381)
              ·
                refine ⟨11460145753362873362958893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30560388675634328967890381 11460145753362873362958893)
                ·
                  refine ⟨4297554657511077511109585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11460145753362873362958893 4297554657511077511109585)
                  ·
                    refine ⟨3223165993133308133332189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4297554657511077511109585 3223165993133308133332189)
                    ·
                      refine ⟨1208687247424990549999571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3223165993133308133332189 1208687247424990549999571)
                      ·
                        rfl

theorem cell23_2353910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2353910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353910 prefixEnd_2353910 := by exact prefixLift 2353910
  have htrace : WordTrace (prefixWord ++ tailWord_2353910) baseStart_2353910 baseEnd_2353910 := by
    simpa [prefixWord, tailWord_2353910, baseEnd_2353910] using wordTrace_append hprefix tailTrace_2353910
  have hstable : (prefixWord ++ tailWord_2353910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353910).length < 2 ^ (prefixWord ++ tailWord_2353910).sum := by decide
  have hdescent : baseEnd_2353910 < baseStart_2353910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353927 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2353927 : Nat := 118140960795 + 2353927 * 2 ^ 59
def prefixEnd_2353927 : Nat := 4983230072969 + 3 ^ 40 * 2353927 * 2
def baseEnd_2353927 : Nat := 1208695976596116983486993

theorem tailTrace_2353927 : CollatzResearch.WordTrace tailWord_2353927 prefixEnd_2353927 1208695976596116983486993 := by
  unfold tailWord_2353927
  simp only [CollatzResearch.WordTrace]
  refine ⟨85854770943131972570364035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57236513962087981713576023 85854770943131972570364035)
  ·
    refine ⟨128782156414697958855546053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85854770943131972570364035 128782156414697958855546053)
    ·
      refine ⟨24146654327755867285414885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128782156414697958855546053 24146654327755867285414885)
      ·
        refine ⟨4527497686454225116015291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24146654327755867285414885 4527497686454225116015291)
        ·
          refine ⟨6791246529681337674022937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4527497686454225116015291 6791246529681337674022937)
          ·
            refine ⟨5093434897261003255517203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6791246529681337674022937 5093434897261003255517203)
            ·
              refine ⟨7640152345891504883275805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093434897261003255517203 7640152345891504883275805)
              ·
                refine ⟨2865057129709314331228427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7640152345891504883275805 2865057129709314331228427)
                ·
                  refine ⟨4297585694563971496842641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865057129709314331228427 4297585694563971496842641)
                  ·
                    refine ⟨3223189270922978622631981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4297585694563971496842641 3223189270922978622631981)
                    ·
                      refine ⟨1208695976596116983486993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3223189270922978622631981 1208695976596116983486993)
                      ·
                        rfl

theorem cell23_2353927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2353927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353927 prefixEnd_2353927 := by exact prefixLift 2353927
  have htrace : WordTrace (prefixWord ++ tailWord_2353927) baseStart_2353927 baseEnd_2353927 := by
    simpa [prefixWord, tailWord_2353927, baseEnd_2353927] using wordTrace_append hprefix tailTrace_2353927
  have hstable : (prefixWord ++ tailWord_2353927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353927).length < 2 ^ (prefixWord ++ tailWord_2353927).sum := by decide
  have hdescent : baseEnd_2353927 < baseStart_2353927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353980 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_2353980 : Nat := 118140960795 + 2353980 * 2 ^ 59
def prefixEnd_2353980 : Nat := 4983230072969 + 3 ^ 40 * 2353980 * 2
def baseEnd_2353980 : Nat := 1208723191070805276124249

theorem tailTrace_2353980 : CollatzResearch.WordTrace tailWord_2353980 prefixEnd_2353980 1208723191070805276124249 := by
  unfold tailWord_2353980
  simp only [CollatzResearch.WordTrace]
  refine ⟨42928352005969981311021697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57237802674626641748028929 42928352005969981311021697)
  ·
    refine ⟨32196264004477485983266273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42928352005969981311021697 32196264004477485983266273)
    ·
      refine ⟨24147198003358114487449705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32196264004477485983266273 24147198003358114487449705)
      ·
        refine ⟨18110398502518585865587279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24147198003358114487449705 18110398502518585865587279)
        ·
          refine ⟨27165597753777878798380919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18110398502518585865587279 27165597753777878798380919)
          ·
            refine ⟨40748396630666818197571379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27165597753777878798380919 40748396630666818197571379)
            ·
              refine ⟨61122594946000227296357069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40748396630666818197571379 61122594946000227296357069)
              ·
                refine ⟨22920973104750085236133901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61122594946000227296357069 22920973104750085236133901)
                ·
                  refine ⟨8595364914281281963550213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22920973104750085236133901 8595364914281281963550213)
                  ·
                    refine ⟨1611630921427740368165665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8595364914281281963550213 1611630921427740368165665)
                    ·
                      refine ⟨1208723191070805276124249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611630921427740368165665 1208723191070805276124249)
                      ·
                        rfl

theorem cell23_2353980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_2353980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353980 prefixEnd_2353980 := by exact prefixLift 2353980
  have htrace : WordTrace (prefixWord ++ tailWord_2353980) baseStart_2353980 baseEnd_2353980 := by
    simpa [prefixWord, tailWord_2353980, baseEnd_2353980] using wordTrace_append hprefix tailTrace_2353980
  have hstable : (prefixWord ++ tailWord_2353980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353980).length < 2 ^ (prefixWord ++ tailWord_2353980).sum := by decide
  have hdescent : baseEnd_2353980 < baseStart_2353980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353983 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_2353983 : Nat := 118140960795 + 2353983 * 2 ^ 59
def prefixEnd_2353983 : Nat := 4983230072969 + 3 ^ 40 * 2353983 * 2
def baseEnd_2353983 : Nat := 1208724731512768764386735

theorem tailTrace_2353983 : CollatzResearch.WordTrace tailWord_2353983 prefixEnd_2353983 1208724731512768764386735 := by
  unfold tailWord_2353983
  simp only [CollatzResearch.WordTrace]
  refine ⟨85856813430929094134402603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57237875620619396089601735 85856813430929094134402603)
  ·
    refine ⟨128785220146393641201603905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85856813430929094134402603 128785220146393641201603905)
    ·
      refine ⟨96588915109795230901202929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128785220146393641201603905 96588915109795230901202929)
      ·
        refine ⟨72441686332346423175902197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96588915109795230901202929 72441686332346423175902197)
        ·
          refine ⟨6791408093657477172740831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72441686332346423175902197 6791408093657477172740831)
          ·
            refine ⟨10187112140486215759111247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6791408093657477172740831 10187112140486215759111247)
            ·
              refine ⟨15280668210729323638666871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10187112140486215759111247 15280668210729323638666871)
              ·
                refine ⟨22921002316093985458000307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15280668210729323638666871 22921002316093985458000307)
                ·
                  refine ⟨34381503474140978187000461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22921002316093985458000307 34381503474140978187000461)
                  ·
                    refine ⟨12893063802802866820125173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34381503474140978187000461 12893063802802866820125173)
                    ·
                      refine ⟨1208724731512768764386735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12893063802802866820125173 1208724731512768764386735)
                      ·
                        rfl

theorem cell23_2353983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_2353983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353983 prefixEnd_2353983 := by exact prefixLift 2353983
  have htrace : WordTrace (prefixWord ++ tailWord_2353983) baseStart_2353983 baseEnd_2353983 := by
    simpa [prefixWord, tailWord_2353983, baseEnd_2353983] using wordTrace_append hprefix tailTrace_2353983
  have hstable : (prefixWord ++ tailWord_2353983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353983).length < 2 ^ (prefixWord ++ tailWord_2353983).sum := by decide
  have hdescent : baseEnd_2353983 < baseStart_2353983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354018 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_2354018 : Nat := 118140960795 + 2354018 * 2 ^ 59
def prefixEnd_2354018 : Nat := 4983230072969 + 3 ^ 40 * 2354018 * 2
def baseEnd_2354018 : Nat := 1208742703335676127449075

theorem tailTrace_2354018 : CollatzResearch.WordTrace tailWord_2354018 prefixEnd_2354018 1208742703335676127449075 := by
  unfold tailWord_2354018
  simp only [CollatzResearch.WordTrace]
  refine ⟨21464522496450573777981677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57238726657201530074617805 21464522496450573777981677)
  ·
    refine ⟨8049195936168965166743129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21464522496450573777981677 8049195936168965166743129)
    ·
      refine ⟨6036896952126723875057347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8049195936168965166743129 6036896952126723875057347)
      ·
        refine ⟨9055345428190085812586021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6036896952126723875057347 9055345428190085812586021)
        ·
          refine ⟨1697877267785641089859879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9055345428190085812586021 1697877267785641089859879)
          ·
            refine ⟨2546815901678461634789819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697877267785641089859879 2546815901678461634789819)
            ·
              refine ⟨3820223852517692452184729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546815901678461634789819 3820223852517692452184729)
              ·
                refine ⟨2865167889388269339138547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3820223852517692452184729 2865167889388269339138547)
                ·
                  refine ⟨4297751834082404008707821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865167889388269339138547 4297751834082404008707821)
                  ·
                    refine ⟨1611656937780901503265433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4297751834082404008707821 1611656937780901503265433)
                    ·
                      refine ⟨1208742703335676127449075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611656937780901503265433 1208742703335676127449075)
                      ·
                        rfl

theorem cell23_2354018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_2354018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354018 prefixEnd_2354018 := by exact prefixLift 2354018
  have htrace : WordTrace (prefixWord ++ tailWord_2354018) baseStart_2354018 baseEnd_2354018 := by
    simpa [prefixWord, tailWord_2354018, baseEnd_2354018] using wordTrace_append hprefix tailTrace_2354018
  have hstable : (prefixWord ++ tailWord_2354018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354018).length < 2 ^ (prefixWord ++ tailWord_2354018).sum := by decide
  have hdescent : baseEnd_2354018 < baseStart_2354018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354043 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5]
def baseStart_2354043 : Nat := 118140960795 + 2354043 * 2 ^ 59
def prefixEnd_2354043 : Nat := 4983230072969 + 3 ^ 40 * 2354043 * 2
def baseEnd_2354043 : Nat := 1208755540352038529636459

theorem tailTrace_2354043 : CollatzResearch.WordTrace tailWord_2354043 prefixEnd_2354043 1208755540352038529636459 := by
  unfold tailWord_2354043
  simp only [CollatzResearch.WordTrace]
  refine ⟨85859001810711724381586783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57239334540474482921057855 85859001810711724381586783)
  ·
    refine ⟨128788502716067586572380175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85859001810711724381586783 128788502716067586572380175)
    ·
      refine ⟨193182754074101379858570263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128788502716067586572380175 193182754074101379858570263)
      ·
        refine ⟨289774131111152069787855395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193182754074101379858570263 289774131111152069787855395)
        ·
          refine ⟨434661196666728104681783093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289774131111152069787855395 434661196666728104681783093)
          ·
            refine ⟨40749487187505759813917165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 434661196666728104681783093 40749487187505759813917165)
            ·
              refine ⟨15281057695314659930218937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40749487187505759813917165 15281057695314659930218937)
              ·
                refine ⟨11460793271485994947664203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15281057695314659930218937 11460793271485994947664203)
                ·
                  refine ⟨17191189907228992421496305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460793271485994947664203 17191189907228992421496305)
                  ·
                    refine ⟨12893392430421744316122229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17191189907228992421496305 12893392430421744316122229)
                    ·
                      refine ⟨1208755540352038529636459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12893392430421744316122229 1208755540352038529636459)
                      ·
                        rfl

theorem cell23_2354043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_2354043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354043 prefixEnd_2354043 := by exact prefixLift 2354043
  have htrace : WordTrace (prefixWord ++ tailWord_2354043) baseStart_2354043 baseEnd_2354043 := by
    simpa [prefixWord, tailWord_2354043, baseEnd_2354043] using wordTrace_append hprefix tailTrace_2354043
  have hstable : (prefixWord ++ tailWord_2354043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354043).length < 2 ^ (prefixWord ++ tailWord_2354043).sum := by decide
  have hdescent : baseEnd_2354043 < baseStart_2354043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354080 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 5, 4]
def baseStart_2354080 : Nat := 118140960795 + 2354080 * 2 ^ 59
def prefixEnd_2354080 : Nat := 4983230072969 + 3 ^ 40 * 2354080 * 2
def baseEnd_2354080 : Nat := 402924846378751628291263

theorem tailTrace_2354080 : CollatzResearch.WordTrace tailWord_2354080 prefixEnd_2354080 402924846378751628291263 := by
  unfold tailWord_2354080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42930175655788839850341847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57240234207718453133789129 42930175655788839850341847)
  ·
    refine ⟨64395263483683259775512771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42930175655788839850341847 64395263483683259775512771)
    ·
      refine ⟨96592895225524889663269157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64395263483683259775512771 96592895225524889663269157)
      ·
        refine ⟨18111167854785916811862967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96592895225524889663269157 18111167854785916811862967)
        ·
          refine ⟨27166751782178875217794451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18111167854785916811862967 27166751782178875217794451)
          ·
            refine ⟨40750127673268312826691677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27166751782178875217794451 40750127673268312826691677)
            ·
              refine ⟨15281297877475617310009379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40750127673268312826691677 15281297877475617310009379)
              ·
                refine ⟨22921946816213425965014069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15281297877475617310009379 22921946816213425965014069)
                ·
                  refine ⟨2148932514020008684220069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22921946816213425965014069 2148932514020008684220069)
                  ·
                    refine ⟨402924846378751628291263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2148932514020008684220069 402924846378751628291263)
                    ·
                      rfl

theorem cell23_2354080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_2354080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354080 prefixEnd_2354080 := by exact prefixLift 2354080
  have htrace : WordTrace (prefixWord ++ tailWord_2354080) baseStart_2354080 baseEnd_2354080 := by
    simpa [prefixWord, tailWord_2354080, baseEnd_2354080] using wordTrace_append hprefix tailTrace_2354080
  have hstable : (prefixWord ++ tailWord_2354080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354080).length < 2 ^ (prefixWord ++ tailWord_2354080).sum := by decide
  have hdescent : baseEnd_2354080 < baseStart_2354080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354087 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2354087 : Nat := 118140960795 + 2354087 * 2 ^ 59
def prefixEnd_2354087 : Nat := 4983230072969 + 3 ^ 40 * 2354087 * 2
def baseEnd_2354087 : Nat := 1208778133500836357486257

theorem tailTrace_2354087 : CollatzResearch.WordTrace tailWord_2354087 prefixEnd_2354087 1208778133500836357486257 := by
  unfold tailWord_2354087
  simp only [CollatzResearch.WordTrace]
  refine ⟨85860606622552319896188515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57240404415034879930792343 85860606622552319896188515)
  ·
    refine ⟨128790909933828479844282773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85860606622552319896188515 128790909933828479844282773)
    ·
      refine ⟨6037073903148209992700755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128790909933828479844282773 6037073903148209992700755)
      ·
        refine ⟨9055610854722314989051133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6037073903148209992700755 9055610854722314989051133)
        ·
          refine ⟨3395854070520868120894175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9055610854722314989051133 3395854070520868120894175)
          ·
            refine ⟨5093781105781302181341263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395854070520868120894175 5093781105781302181341263)
            ·
              refine ⟨7640671658671953272011895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093781105781302181341263 7640671658671953272011895)
              ·
                refine ⟨11461007488007929908017843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640671658671953272011895 11461007488007929908017843)
                ·
                  refine ⟨17191511232011894862026765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11461007488007929908017843 17191511232011894862026765)
                  ·
                    refine ⟨6446816712004460573260037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17191511232011894862026765 6446816712004460573260037)
                    ·
                      refine ⟨1208778133500836357486257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6446816712004460573260037 1208778133500836357486257)
                      ·
                        rfl

theorem cell23_2354087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2354087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354087 prefixEnd_2354087 := by exact prefixLift 2354087
  have htrace : WordTrace (prefixWord ++ tailWord_2354087) baseStart_2354087 baseEnd_2354087 := by
    simpa [prefixWord, tailWord_2354087, baseEnd_2354087] using wordTrace_append hprefix tailTrace_2354087
  have hstable : (prefixWord ++ tailWord_2354087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354087).length < 2 ^ (prefixWord ++ tailWord_2354087).sum := by decide
  have hdescent : baseEnd_2354087 < baseStart_2354087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354110 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2354110 : Nat := 118140960795 + 2354110 * 2 ^ 59
def prefixEnd_2354110 : Nat := 4983230072969 + 3 ^ 40 * 2354110 * 2
def baseEnd_2354110 : Nat := 134309993728432196388739

theorem tailTrace_2354110 : CollatzResearch.WordTrace tailWord_2354110 prefixEnd_2354110 134309993728432196388739 := by
  unfold tailWord_2354110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10732680687683624353034473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57240963667645996549517189 10732680687683624353034473)
  ·
    refine ⟨8049510515762718264775855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10732680687683624353034473 8049510515762718264775855)
    ·
      refine ⟨12074265773644077397163783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8049510515762718264775855 12074265773644077397163783)
      ·
        refine ⟨18111398660466116095745675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12074265773644077397163783 18111398660466116095745675)
        ·
          refine ⟨27167097990699174143618513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18111398660466116095745675 27167097990699174143618513)
          ·
            refine ⟨20375323493024380607713885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27167097990699174143618513 20375323493024380607713885)
            ·
              refine ⟨7640746309884142727892707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20375323493024380607713885 7640746309884142727892707)
              ·
                refine ⟨11461119464826214091839061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640746309884142727892707 11461119464826214091839061)
                ·
                  refine ⟨134309993728432196388739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11461119464826214091839061 134309993728432196388739)
                  ·
                    rfl

theorem cell23_2354110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2354110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354110 prefixEnd_2354110 := by exact prefixLift 2354110
  have htrace : WordTrace (prefixWord ++ tailWord_2354110) baseStart_2354110 baseEnd_2354110 := by
    simpa [prefixWord, tailWord_2354110, baseEnd_2354110] using wordTrace_append hprefix tailTrace_2354110
  have hstable : (prefixWord ++ tailWord_2354110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354110).length < 2 ^ (prefixWord ++ tailWord_2354110).sum := by decide
  have hdescent : baseEnd_2354110 < baseStart_2354110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354127 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 6]
def baseStart_2354127 : Nat := 118140960795 + 2354127 * 2 ^ 59
def prefixEnd_2354127 : Nat := 4983230072969 + 3 ^ 40 * 2354127 * 2
def baseEnd_2354127 : Nat := 134310963636335133442897

theorem tailTrace_2354127 : CollatzResearch.WordTrace tailWord_2354127 prefixEnd_2354127 134310963636335133442897 := by
  unfold tailWord_2354127
  simp only [CollatzResearch.WordTrace]
  refine ⟨85862065542407406727644635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57241377028271604485096423 85862065542407406727644635)
  ·
    refine ⟨128793098313611110091466953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85862065542407406727644635 128793098313611110091466953)
    ·
      refine ⟨96594823735208332568600215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128793098313611110091466953 96594823735208332568600215)
      ·
        refine ⟨144892235602812498852900323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96594823735208332568600215 144892235602812498852900323)
        ·
          refine ⟨217338353404218748279350485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144892235602812498852900323 217338353404218748279350485)
          ·
            refine ⟨5093867657911376912797277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 217338353404218748279350485 5093867657911376912797277)
            ·
              refine ⟨1910200371716766342298979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5093867657911376912797277 1910200371716766342298979)
              ·
                refine ⟨2865300557575149513448469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910200371716766342298979 2865300557575149513448469)
                ·
                  refine ⟨134310963636335133442897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2865300557575149513448469 134310963636335133442897)
                  ·
                    rfl

theorem cell23_2354127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 6].length) (baseStart_2354127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354127 prefixEnd_2354127 := by exact prefixLift 2354127
  have htrace : WordTrace (prefixWord ++ tailWord_2354127) baseStart_2354127 baseEnd_2354127 := by
    simpa [prefixWord, tailWord_2354127, baseEnd_2354127] using wordTrace_append hprefix tailTrace_2354127
  have hstable : (prefixWord ++ tailWord_2354127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354127).length < 2 ^ (prefixWord ++ tailWord_2354127).sum := by decide
  have hdescent : baseEnd_2354127 < baseStart_2354127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354147 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 1, 5, 2]
def baseStart_2354147 : Nat := 118140960795 + 2354147 * 2 ^ 59
def prefixEnd_2354147 : Nat := 4983230072969 + 3 ^ 40 * 2354147 * 2
def baseEnd_2354147 : Nat := 1208808942340106122735981

theorem tailTrace_2354147 : CollatzResearch.WordTrace tailWord_2354147 prefixEnd_2354147 1208808942340106122735981 := by
  unfold tailWord_2354147
  simp only [CollatzResearch.WordTrace]
  refine ⟨85862795002334950143372695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57241863334889966762248463 85862795002334950143372695)
  ·
    refine ⟨128794192503502425215059043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85862795002334950143372695 128794192503502425215059043)
    ·
      refine ⟨193191288755253637822588565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128794192503502425215059043 193191288755253637822588565)
      ·
        refine ⟨9055841660402514272933839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193191288755253637822588565 9055841660402514272933839)
        ·
          refine ⟨13583762490603771409400759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9055841660402514272933839 13583762490603771409400759)
          ·
            refine ⟨20375643735905657114101139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13583762490603771409400759 20375643735905657114101139)
            ·
              refine ⟨30563465603858485671151709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20375643735905657114101139 30563465603858485671151709)
              ·
                refine ⟨11461299601446932126681891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30563465603858485671151709 11461299601446932126681891)
                ·
                  refine ⟨17191949402170398190022837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11461299601446932126681891 17191949402170398190022837)
                  ·
                    refine ⟨1611745256453474830314641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17191949402170398190022837 1611745256453474830314641)
                    ·
                      refine ⟨1208808942340106122735981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611745256453474830314641 1208808942340106122735981)
                      ·
                        rfl

theorem cell23_2354147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_2354147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354147 prefixEnd_2354147 := by exact prefixLift 2354147
  have htrace : WordTrace (prefixWord ++ tailWord_2354147) baseStart_2354147 baseEnd_2354147 := by
    simpa [prefixWord, tailWord_2354147, baseEnd_2354147] using wordTrace_append hprefix tailTrace_2354147
  have hstable : (prefixWord ++ tailWord_2354147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354147).length < 2 ^ (prefixWord ++ tailWord_2354147).sum := by decide
  have hdescent : baseEnd_2354147 < baseStart_2354147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354160 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_2354160 : Nat := 118140960795 + 2354160 * 2 ^ 59
def prefixEnd_2354160 : Nat := 4983230072969 + 3 ^ 40 * 2354160 * 2
def baseEnd_2354160 : Nat := 1208815617588614571873421

theorem tailTrace_2354160 : CollatzResearch.WordTrace tailWord_2354160 prefixEnd_2354160 1208815617588614571873421 := by
  unfold tailWord_2354160
  simp only [CollatzResearch.WordTrace]
  refine ⟨42931634575643926681797967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57242179434191902242397289 42931634575643926681797967)
  ·
    refine ⟨64397451863465890022696951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42931634575643926681797967 64397451863465890022696951)
    ·
      refine ⟨96596177795198835034045427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64397451863465890022696951 96596177795198835034045427)
      ·
        refine ⟨144894266692798252551068141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96596177795198835034045427 144894266692798252551068141)
        ·
          refine ⟨54335350009799344706650553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144894266692798252551068141 54335350009799344706650553)
          ·
            refine ⟨40751512507349508529987915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54335350009799344706650553 40751512507349508529987915)
            ·
              refine ⟨61127268761024262794981873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40751512507349508529987915 61127268761024262794981873)
              ·
                refine ⟨45845451570768197096236405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61127268761024262794981873 45845451570768197096236405)
                ·
                  refine ⟨4298011084759518477772163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45845451570768197096236405 4298011084759518477772163)
                  ·
                    refine ⟨6447016627139277716658245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298011084759518477772163 6447016627139277716658245)
                    ·
                      refine ⟨1208815617588614571873421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6447016627139277716658245 1208815617588614571873421)
                      ·
                        rfl

theorem cell23_2354160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_2354160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354160 prefixEnd_2354160 := by exact prefixLift 2354160
  have htrace : WordTrace (prefixWord ++ tailWord_2354160) baseStart_2354160 baseEnd_2354160 := by
    simpa [prefixWord, tailWord_2354160, baseEnd_2354160] using wordTrace_append hprefix tailTrace_2354160
  have hstable : (prefixWord ++ tailWord_2354160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354160).length < 2 ^ (prefixWord ++ tailWord_2354160).sum := by decide
  have hdescent : baseEnd_2354160 < baseStart_2354160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354165 : List Nat := [1, 3, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2354165 : Nat := 118140960795 + 2354165 * 2 ^ 59
def prefixEnd_2354165 : Nat := 4983230072969 + 3 ^ 40 * 2354165 * 2
def baseEnd_2354165 : Nat := 402939394997295684103633

theorem tailTrace_2354165 : CollatzResearch.WordTrace tailWord_2354165 prefixEnd_2354165 402939394997295684103633 := by
  unfold tailWord_2354165
  simp only [CollatzResearch.WordTrace]
  refine ⟨85863451516269739217527949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57242301010846492811685299 85863451516269739217527949)
  ·
    refine ⟨32198794318601152206572981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85863451516269739217527949 32198794318601152206572981)
    ·
      refine ⟨3018636967368858019366217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32198794318601152206572981 3018636967368858019366217)
      ·
        refine ⟨2263977725526643514524663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3018636967368858019366217 2263977725526643514524663)
        ·
          refine ⟨3395966588289965271786995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263977725526643514524663 3395966588289965271786995)
          ·
            refine ⟨5093949882434947907680493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395966588289965271786995 5093949882434947907680493)
            ·
              refine ⟨1910231205913105465380185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5093949882434947907680493 1910231205913105465380185)
              ·
                refine ⟨1432673404434829099035139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1910231205913105465380185 1432673404434829099035139)
                ·
                  refine ⟨2149010106652243648552709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432673404434829099035139 2149010106652243648552709)
                  ·
                    refine ⟨402939394997295684103633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2149010106652243648552709 402939394997295684103633)
                    ·
                      rfl

theorem cell23_2354165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2354165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354165 prefixEnd_2354165 := by exact prefixLift 2354165
  have htrace : WordTrace (prefixWord ++ tailWord_2354165) baseStart_2354165 baseEnd_2354165 := by
    simpa [prefixWord, tailWord_2354165, baseEnd_2354165] using wordTrace_append hprefix tailTrace_2354165
  have hstable : (prefixWord ++ tailWord_2354165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354165).length < 2 ^ (prefixWord ++ tailWord_2354165).sum := by decide
  have hdescent : baseEnd_2354165 < baseStart_2354165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354178 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2354178 : Nat := 118140960795 + 2354178 * 2 ^ 59
def prefixEnd_2354178 : Nat := 4983230072969 + 3 ^ 40 * 2354178 * 2
def baseEnd_2354178 : Nat := 134313873360043944605371

theorem tailTrace_2354178 : CollatzResearch.WordTrace tailWord_2354178 prefixEnd_2354178 134313873360043944605371 := by
  unfold tailWord_2354178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21465981416305660609437797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57242617110148428291834125 21465981416305660609437797)
  ·
    refine ⟨4024871515557311364269587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21465981416305660609437797 4024871515557311364269587)
    ·
      refine ⟨6037307273335967046404381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4024871515557311364269587 6037307273335967046404381)
      ·
        refine ⟨2263990227500987642401643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6037307273335967046404381 2263990227500987642401643)
        ·
          refine ⟨3395985341251481463602465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263990227500987642401643 3395985341251481463602465)
          ·
            refine ⟨2546989005938611097701849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3395985341251481463602465 2546989005938611097701849)
            ·
              refine ⟨1910241754453958323276387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2546989005938611097701849 1910241754453958323276387)
              ·
                refine ⟨2865362631680937484914581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910241754453958323276387 2865362631680937484914581)
                ·
                  refine ⟨134313873360043944605371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2865362631680937484914581 134313873360043944605371)
                  ·
                    rfl

theorem cell23_2354178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2354178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354178 prefixEnd_2354178 := by exact prefixLift 2354178
  have htrace : WordTrace (prefixWord ++ tailWord_2354178) baseStart_2354178 baseEnd_2354178 := by
    simpa [prefixWord, tailWord_2354178, baseEnd_2354178] using wordTrace_append hprefix tailTrace_2354178
  have hstable : (prefixWord ++ tailWord_2354178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354178).length < 2 ^ (prefixWord ++ tailWord_2354178).sum := by decide
  have hdescent : baseEnd_2354178 < baseStart_2354178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354200 : List Nat := [2, 1, 2, 3, 2, 2, 2, 9]
def baseStart_2354200 : Nat := 118140960795 + 2354200 * 2 ^ 59
def prefixEnd_2354200 : Nat := 4983230072969 + 3 ^ 40 * 2354200 * 2
def baseEnd_2354200 : Nat := 44771709511659052421231

theorem tailTrace_2354200 : CollatzResearch.WordTrace tailWord_2354200 prefixEnd_2354200 44771709511659052421231 := by
  unfold tailWord_2354200
  simp only [CollatzResearch.WordTrace]
  refine ⟨42932364035571470097526027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57243152047428626796701369 42932364035571470097526027)
  ·
    refine ⟨64398546053357205146289041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42932364035571470097526027 64398546053357205146289041)
    ·
      refine ⟨48298909540017903859716781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64398546053357205146289041 48298909540017903859716781)
      ·
        refine ⟨18112091077506713947393793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48298909540017903859716781 18112091077506713947393793)
        ·
          refine ⟨13584068308130035460545345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18112091077506713947393793 13584068308130035460545345)
          ·
            refine ⟨10188051231097526595409009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13584068308130035460545345 10188051231097526595409009)
            ·
              refine ⟨7641038423323144946556757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10188051231097526595409009 7641038423323144946556757)
              ·
                refine ⟨44771709511659052421231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7641038423323144946556757 44771709511659052421231)
                ·
                  rfl

theorem cell23_2354200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 9].length) (baseStart_2354200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354200 prefixEnd_2354200 := by exact prefixLift 2354200
  have htrace : WordTrace (prefixWord ++ tailWord_2354200) baseStart_2354200 baseEnd_2354200 := by
    simpa [prefixWord, tailWord_2354200, baseEnd_2354200] using wordTrace_append hprefix tailTrace_2354200
  have hstable : (prefixWord ++ tailWord_2354200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354200).length < 2 ^ (prefixWord ++ tailWord_2354200).sum := by decide
  have hdescent : baseEnd_2354200 < baseStart_2354200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354207 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_2354207 : Nat := 118140960795 + 2354207 * 2 ^ 59
def prefixEnd_2354207 : Nat := 4983230072969 + 3 ^ 40 * 2354207 * 2
def baseEnd_2354207 : Nat := 1208839751179375887985705

theorem tailTrace_2354207 : CollatzResearch.WordTrace tailWord_2354207 prefixEnd_2354207 1208839751179375887985705 := by
  unfold tailWord_2354207
  simp only [CollatzResearch.WordTrace]
  refine ⟨85864983382117580390556875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57243322254745053593704583 85864983382117580390556875)
  ·
    refine ⟨128797475073176370585835313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85864983382117580390556875 128797475073176370585835313)
    ·
      refine ⟨96598106304882277939376485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128797475073176370585835313 96598106304882277939376485)
      ·
        refine ⟨18112144932165427113633091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96598106304882277939376485 18112144932165427113633091)
        ·
          refine ⟨27168217398248140670449637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18112144932165427113633091 27168217398248140670449637)
          ·
            refine ⟨5094040762171526375709307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27168217398248140670449637 5094040762171526375709307)
            ·
              refine ⟨7641061143257289563563961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094040762171526375709307 7641061143257289563563961)
              ·
                refine ⟨5730795857442967172672971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7641061143257289563563961 5730795857442967172672971)
                ·
                  refine ⟨8596193786164450759009457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5730795857442967172672971 8596193786164450759009457)
                  ·
                    refine ⟨6447145339623338069257093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8596193786164450759009457 6447145339623338069257093)
                    ·
                      refine ⟨1208839751179375887985705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6447145339623338069257093 1208839751179375887985705)
                      ·
                        rfl

theorem cell23_2354207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_2354207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354207 prefixEnd_2354207 := by exact prefixLift 2354207
  have htrace : WordTrace (prefixWord ++ tailWord_2354207) baseStart_2354207 baseEnd_2354207 := by
    simpa [prefixWord, tailWord_2354207, baseEnd_2354207] using wordTrace_append hprefix tailTrace_2354207
  have hstable : (prefixWord ++ tailWord_2354207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354207).length < 2 ^ (prefixWord ++ tailWord_2354207).sum := by decide
  have hdescent : baseEnd_2354207 < baseStart_2354207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354254 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_2354254 : Nat := 118140960795 + 2354254 * 2 ^ 59
def prefixEnd_2354254 : Nat := 4983230072969 + 3 ^ 40 * 2354254 * 2
def baseEnd_2354254 : Nat := 1208863884770137204097989

theorem tailTrace_2354254 : CollatzResearch.WordTrace tailWord_2354254 prefixEnd_2354254 1208863884770137204097989 := by
  unfold tailWord_2354254
  simp only [CollatzResearch.WordTrace]
  refine ⟨10733337201618413427189727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57244465075298204945011877 10733337201618413427189727)
  ·
    refine ⟨16100005802427620140784591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10733337201618413427189727 16100005802427620140784591)
    ·
      refine ⟨24150008703641430211176887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16100005802427620140784591 24150008703641430211176887)
      ·
        refine ⟨36225013055462145316765331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24150008703641430211176887 36225013055462145316765331)
        ·
          refine ⟨54337519583193217975147997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36225013055462145316765331 54337519583193217975147997)
          ·
            refine ⟨20376569843697456740680499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54337519583193217975147997 20376569843697456740680499)
            ·
              refine ⟨30564854765546185111020749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20376569843697456740680499 30564854765546185111020749)
              ·
                refine ⟨11461820537079819416632781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30564854765546185111020749 11461820537079819416632781)
                ·
                  refine ⟨4298182701404932281237293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11461820537079819416632781 4298182701404932281237293)
                  ·
                    refine ⟨1611818513026849605463985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4298182701404932281237293 1611818513026849605463985)
                    ·
                      refine ⟨1208863884770137204097989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611818513026849605463985 1208863884770137204097989)
                      ·
                        rfl

theorem cell23_2354254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_2354254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354254 prefixEnd_2354254 := by exact prefixLift 2354254
  have htrace : WordTrace (prefixWord ++ tailWord_2354254) baseStart_2354254 baseEnd_2354254 := by
    simpa [prefixWord, tailWord_2354254, baseEnd_2354254] using wordTrace_append hprefix tailTrace_2354254
  have hstable : (prefixWord ++ tailWord_2354254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354254).length < 2 ^ (prefixWord ++ tailWord_2354254).sum := by decide
  have hdescent : baseEnd_2354254 < baseStart_2354254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354262 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2354262 : Nat := 118140960795 + 2354262 * 2 ^ 59
def prefixEnd_2354262 : Nat := 4983230072969 + 3 ^ 40 * 2354262 * 2
def baseEnd_2354262 : Nat := 1208867992615373172797953

theorem tailTrace_2354262 : CollatzResearch.WordTrace tailWord_2354262 prefixEnd_2354262 1208867992615373172797953 := by
  unfold tailWord_2354262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366686837307395298988065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57244659597945549855872693 5366686837307395298988065)
  ·
    refine ⟨4025015127980546474241049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5366686837307395298988065 4025015127980546474241049)
    ·
      refine ⟨3018761345985409855680787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4025015127980546474241049 3018761345985409855680787)
      ·
        refine ⟨4528142018978114783521181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3018761345985409855680787 4528142018978114783521181)
        ·
          refine ⟨1698053257116793043820443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4528142018978114783521181 1698053257116793043820443)
          ·
            refine ⟨2547079885675189565730665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698053257116793043820443 2547079885675189565730665)
            ·
              refine ⟨1910309914256392174297999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2547079885675189565730665 1910309914256392174297999)
              ·
                refine ⟨2865464871384588261446999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910309914256392174297999 2865464871384588261446999)
                ·
                  refine ⟨4298197307076882392170499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865464871384588261446999 4298197307076882392170499)
                  ·
                    refine ⟨6447295960615323588255749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298197307076882392170499 6447295960615323588255749)
                    ·
                      refine ⟨1208867992615373172797953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6447295960615323588255749 1208867992615373172797953)
                      ·
                        rfl

theorem cell23_2354262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2354262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354262 prefixEnd_2354262 := by exact prefixLift 2354262
  have htrace : WordTrace (prefixWord ++ tailWord_2354262) baseStart_2354262 baseEnd_2354262 := by
    simpa [prefixWord, tailWord_2354262, baseEnd_2354262] using wordTrace_append hprefix tailTrace_2354262
  have hstable : (prefixWord ++ tailWord_2354262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354262).length < 2 ^ (prefixWord ++ tailWord_2354262).sum := by decide
  have hdescent : baseEnd_2354262 < baseStart_2354262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354341 : List Nat := [1, 3, 1, 2, 1, 5, 3, 2, 5]
def baseStart_2354341 : Nat := 118140960795 + 2354341 * 2 ^ 59
def prefixEnd_2354341 : Nat := 4983230072969 + 3 ^ 40 * 2354341 * 2
def baseEnd_2354341 : Nat := 134323173065230929301121

theorem tailTrace_2354341 : CollatzResearch.WordTrace tailWord_2354341 prefixEnd_2354341 134323173065230929301121 := by
  unfold tailWord_2354341
  simp only [CollatzResearch.WordTrace]
  refine ⟨85869870763632121275934877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57246580509088080850623251 85869870763632121275934877)
  ·
    refine ⟨32201201536362045478475579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85869870763632121275934877 32201201536362045478475579)
    ·
      refine ⟨48301802304543068217713369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32201201536362045478475579 48301802304543068217713369)
      ·
        refine ⟨36226351728407301163285027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48301802304543068217713369 36226351728407301163285027)
        ·
          refine ⟨54339527592610951744927541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36226351728407301163285027 54339527592610951744927541)
          ·
            refine ⟨5094330711807276726086957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54339527592610951744927541 5094330711807276726086957)
            ·
              refine ⟨1910374016927728772282609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5094330711807276726086957 1910374016927728772282609)
              ·
                refine ⟨1432780512695796579211957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1910374016927728772282609 1432780512695796579211957)
                ·
                  refine ⟨134323173065230929301121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1432780512695796579211957 134323173065230929301121)
                  ·
                    rfl

theorem cell23_2354341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_2354341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354341 prefixEnd_2354341 := by exact prefixLift 2354341
  have htrace : WordTrace (prefixWord ++ tailWord_2354341) baseStart_2354341 baseEnd_2354341 := by
    simpa [prefixWord, tailWord_2354341, baseEnd_2354341] using wordTrace_append hprefix tailTrace_2354341
  have hstable : (prefixWord ++ tailWord_2354341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354341).length < 2 ^ (prefixWord ++ tailWord_2354341).sum := by decide
  have hdescent : baseEnd_2354341 < baseStart_2354341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354377 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 3]
def baseStart_2354377 : Nat := 118140960795 + 2354377 * 2 ^ 59
def prefixEnd_2354377 : Nat := 4983230072969 + 3 ^ 40 * 2354377 * 2
def baseEnd_2354377 : Nat := 1208927042890640222859923

theorem tailTrace_2354377 : CollatzResearch.WordTrace tailWord_2354377 prefixEnd_2354377 1208927042890640222859923 := by
  unfold tailWord_2354377
  simp only [CollatzResearch.WordTrace]
  refine ⟨85871183791501699424245385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57247455861001132949496923 85871183791501699424245385)
  ·
    refine ⟨64403387843626274568184039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85871183791501699424245385 64403387843626274568184039)
    ·
      refine ⟨96605081765439411852276059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64403387843626274568184039 96605081765439411852276059)
      ·
        refine ⟨144907622648159117778414089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96605081765439411852276059 144907622648159117778414089)
        ·
          refine ⟨108680716986119338333810567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144907622648159117778414089 108680716986119338333810567)
          ·
            refine ⟨163021075479179007500715851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108680716986119338333810567 163021075479179007500715851)
            ·
              refine ⟨244531613218768511251073777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163021075479179007500715851 244531613218768511251073777)
              ·
                refine ⟨183398709914076383438305333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244531613218768511251073777 183398709914076383438305333)
                ·
                  refine ⟨17193629054444660947341125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183398709914076383438305333 17193629054444660947341125)
                  ·
                    refine ⟨3223805447708373927626461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17193629054444660947341125 3223805447708373927626461)
                    ·
                      refine ⟨1208927042890640222859923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3223805447708373927626461 1208927042890640222859923)
                      ·
                        rfl

theorem cell23_2354377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_2354377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354377 prefixEnd_2354377 := by exact prefixLift 2354377
  have htrace : WordTrace (prefixWord ++ tailWord_2354377) baseStart_2354377 baseEnd_2354377 := by
    simpa [prefixWord, tailWord_2354377, baseEnd_2354377] using wordTrace_append hprefix tailTrace_2354377
  have hstable : (prefixWord ++ tailWord_2354377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354377).length < 2 ^ (prefixWord ++ tailWord_2354377).sum := by decide
  have hdescent : baseEnd_2354377 < baseStart_2354377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354414 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_2354414 : Nat := 118140960795 + 2354414 * 2 ^ 59
def prefixEnd_2354414 : Nat := 4983230072969 + 3 ^ 40 * 2354414 * 2
def baseEnd_2354414 : Nat := 134327337963872953121917

theorem tailTrace_2354414 : CollatzResearch.WordTrace tailWord_2354414 prefixEnd_2354414 134327337963872953121917 := by
  unfold tailWord_2354414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734066661545956842917787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57248355528245103162228197 10734066661545956842917787)
  ·
    refine ⟨16101099992318935264376681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10734066661545956842917787 16101099992318935264376681)
    ·
      refine ⟨12075824994239201448282511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16101099992318935264376681 12075824994239201448282511)
      ·
        refine ⟨18113737491358802172423767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12075824994239201448282511 18113737491358802172423767)
        ·
          refine ⟨27170606237038203258635651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18113737491358802172423767 27170606237038203258635651)
          ·
            refine ⟨40755909355557304887953477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27170606237038203258635651 40755909355557304887953477)
            ·
              refine ⟨7641733004166994666491277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40755909355557304887953477 7641733004166994666491277)
              ·
                refine ⟨2865649876562622999934229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7641733004166994666491277 2865649876562622999934229)
                ·
                  refine ⟨134327337963872953121917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2865649876562622999934229 134327337963872953121917)
                  ·
                    rfl

theorem cell23_2354414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_2354414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354414 prefixEnd_2354414 := by exact prefixLift 2354414
  have htrace : WordTrace (prefixWord ++ tailWord_2354414) baseStart_2354414 baseEnd_2354414 := by
    simpa [prefixWord, tailWord_2354414, baseEnd_2354414] using wordTrace_append hprefix tailTrace_2354414
  have hstable : (prefixWord ++ tailWord_2354414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354414).length < 2 ^ (prefixWord ++ tailWord_2354414).sum := by decide
  have hdescent : baseEnd_2354414 < baseStart_2354414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354428 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_2354428 : Nat := 118140960795 + 2354428 * 2 ^ 59
def prefixEnd_2354428 : Nat := 4983230072969 + 3 ^ 40 * 2354428 * 2
def baseEnd_2354428 : Nat := 1208953230404019523322189

theorem tailTrace_2354428 : CollatzResearch.WordTrace tailWord_2354428 prefixEnd_2354428 1208953230404019523322189 := by
  unfold tailWord_2354428
  simp only [CollatzResearch.WordTrace]
  refine ⟨42936521957158467567175969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57248695942877956756234625 42936521957158467567175969)
  ·
    refine ⟨32202391467868850675381977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42936521957158467567175969 32202391467868850675381977)
    ·
      refine ⟨24151793600901638006536483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32202391467868850675381977 24151793600901638006536483)
      ·
        refine ⟨36227690401352457009804725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24151793600901638006536483 36227690401352457009804725)
        ·
          refine ⟨3396345975126792844669193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36227690401352457009804725 3396345975126792844669193)
          ·
            refine ⟨2547259481345094633501895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3396345975126792844669193 2547259481345094633501895)
            ·
              refine ⟨3820889222017641950252843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547259481345094633501895 3820889222017641950252843)
              ·
                refine ⟨5731333833026462925379265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820889222017641950252843 5731333833026462925379265)
                ·
                  refine ⟨4298500374769847194034449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731333833026462925379265 4298500374769847194034449)
                  ·
                    refine ⟨3223875281077385395525837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4298500374769847194034449 3223875281077385395525837)
                    ·
                      refine ⟨1208953230404019523322189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3223875281077385395525837 1208953230404019523322189)
                      ·
                        rfl

theorem cell23_2354428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_2354428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354428 prefixEnd_2354428 := by exact prefixLift 2354428
  have htrace : WordTrace (prefixWord ++ tailWord_2354428) baseStart_2354428 baseEnd_2354428 := by
    simpa [prefixWord, tailWord_2354428, baseEnd_2354428] using wordTrace_append hprefix tailTrace_2354428
  have hstable : (prefixWord ++ tailWord_2354428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354428).length < 2 ^ (prefixWord ++ tailWord_2354428).sum := by decide
  have hdescent : baseEnd_2354428 < baseStart_2354428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354458 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_2354458 : Nat := 118140960795 + 2354458 * 2 ^ 59
def prefixEnd_2354458 : Nat := 4983230072969 + 3 ^ 40 * 2354458 * 2
def baseEnd_2354458 : Nat := 1208968634823654405947051

theorem tailTrace_2354458 : CollatzResearch.WordTrace tailWord_2354458 prefixEnd_2354458 1208968634823654405947051 := by
  unfold tailWord_2354458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21468534526052062564486007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57249425402805500171962685 21468534526052062564486007)
  ·
    refine ⟨32202801789078093846729011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21468534526052062564486007 32202801789078093846729011)
    ·
      refine ⟨48304202683617140770093517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32202801789078093846729011 48304202683617140770093517)
      ·
        refine ⟨18114076006356427788785069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48304202683617140770093517 18114076006356427788785069)
        ·
          refine ⟨6792778502383660420794401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18114076006356427788785069 6792778502383660420794401)
          ·
            refine ⟨5094583876787745315595801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6792778502383660420794401 5094583876787745315595801)
            ·
              refine ⟨3820937907590808986696851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5094583876787745315595801 3820937907590808986696851)
              ·
                refine ⟨5731406861386213480045277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820937907590808986696851 5731406861386213480045277)
                ·
                  refine ⟨2149277573019830055016979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5731406861386213480045277 2149277573019830055016979)
                  ·
                    refine ⟨3223916359529745082525469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2149277573019830055016979 3223916359529745082525469)
                    ·
                      refine ⟨1208968634823654405947051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3223916359529745082525469 1208968634823654405947051)
                      ·
                        rfl

theorem cell23_2354458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_2354458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354458 prefixEnd_2354458 := by exact prefixLift 2354458
  have htrace : WordTrace (prefixWord ++ tailWord_2354458) baseStart_2354458 baseEnd_2354458 := by
    simpa [prefixWord, tailWord_2354458, baseEnd_2354458] using wordTrace_append hprefix tailTrace_2354458
  have hstable : (prefixWord ++ tailWord_2354458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354458).length < 2 ^ (prefixWord ++ tailWord_2354458).sum := by decide
  have hdescent : baseEnd_2354458 < baseStart_2354458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354481 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_2354481 : Nat := 118140960795 + 2354481 * 2 ^ 59
def prefixEnd_2354481 : Nat := 4983230072969 + 3 ^ 40 * 2354481 * 2
def baseEnd_2354481 : Nat := 1208980444878707815959445

theorem tailTrace_2354481 : CollatzResearch.WordTrace tailWord_2354481 prefixEnd_2354481 1208980444878707815959445 := by
  unfold tailWord_2354481
  simp only [CollatzResearch.WordTrace]
  refine ⟨85874976983124925186031297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57249984655416616790687531 85874976983124925186031297)
  ·
    refine ⟨64406232737343693889523473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85874976983124925186031297 64406232737343693889523473)
    ·
      refine ⟨48304674553007770417142605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64406232737343693889523473 48304674553007770417142605)
      ·
        refine ⟨18114252957377913906428477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48304674553007770417142605 18114252957377913906428477)
        ·
          refine ⟨6792844859016717714910679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18114252957377913906428477 6792844859016717714910679)
          ·
            refine ⟨10189267288525076572366019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6792844859016717714910679 10189267288525076572366019)
            ·
              refine ⟨15283900932787614858549029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10189267288525076572366019 15283900932787614858549029)
              ·
                refine ⟨2865731424897677785977943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15283900932787614858549029 2865731424897677785977943)
                ·
                  refine ⟨4298597137346516678966915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865731424897677785977943 4298597137346516678966915)
                  ·
                    refine ⟨6447895706019775018450373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298597137346516678966915 6447895706019775018450373)
                    ·
                      refine ⟨1208980444878707815959445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6447895706019775018450373 1208980444878707815959445)
                      ·
                        rfl

theorem cell23_2354481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_2354481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354481 prefixEnd_2354481 := by exact prefixLift 2354481
  have htrace : WordTrace (prefixWord ++ tailWord_2354481) baseStart_2354481 baseEnd_2354481 := by
    simpa [prefixWord, tailWord_2354481, baseEnd_2354481] using wordTrace_append hprefix tailTrace_2354481
  have hstable : (prefixWord ++ tailWord_2354481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354481).length < 2 ^ (prefixWord ++ tailWord_2354481).sum := by decide
  have hdescent : baseEnd_2354481 < baseStart_2354481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354509 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2354509 : Nat := 118140960795 + 2354509 * 2 ^ 59
def prefixEnd_2354509 : Nat := 4983230072969 + 3 ^ 40 * 2354509 * 2
def baseEnd_2354509 : Nat := 1208994822337033706409317

theorem tailTrace_2354509 : CollatzResearch.WordTrace tailWord_2354509 prefixEnd_2354509 1208994822337033706409317 := by
  unfold tailWord_2354509
  simp only [CollatzResearch.WordTrace]
  refine ⟨85875998227023485968050581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57250665484682323978700387 85875998227023485968050581)
  ·
    refine ⟨4025437416891725904752371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85875998227023485968050581 4025437416891725904752371)
    ·
      refine ⟨6038156125337588857128557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4025437416891725904752371 6038156125337588857128557)
      ·
        refine ⟨2264308547001595821423209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6038156125337588857128557 2264308547001595821423209)
        ·
          refine ⟨1698231410251196866067407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2264308547001595821423209 1698231410251196866067407)
          ·
            refine ⟨2547347115376795299101111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698231410251196866067407 2547347115376795299101111)
            ·
              refine ⟨3821020673065192948651667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547347115376795299101111 3821020673065192948651667)
              ·
                refine ⟨5731531009597789422977501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821020673065192948651667 5731531009597789422977501)
                ·
                  refine ⟨2149324128599171033616563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5731531009597789422977501 2149324128599171033616563)
                  ·
                    refine ⟨3223986192898756550424845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2149324128599171033616563 3223986192898756550424845)
                    ·
                      refine ⟨1208994822337033706409317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3223986192898756550424845 1208994822337033706409317)
                      ·
                        rfl

theorem cell23_2354509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2354509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354509 prefixEnd_2354509 := by exact prefixLift 2354509
  have htrace : WordTrace (prefixWord ++ tailWord_2354509) baseStart_2354509 baseEnd_2354509 := by
    simpa [prefixWord, tailWord_2354509, baseEnd_2354509] using wordTrace_append hprefix tailTrace_2354509
  have hstable : (prefixWord ++ tailWord_2354509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354509).length < 2 ^ (prefixWord ++ tailWord_2354509).sum := by decide
  have hdescent : baseEnd_2354509 < baseStart_2354509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354535 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2354535 : Nat := 118140960795 + 2354535 * 2 ^ 59
def prefixEnd_2354535 : Nat := 4983230072969 + 3 ^ 40 * 2354535 * 2
def baseEnd_2354535 : Nat := 1209008172834050604684197

theorem tailTrace_2354535 : CollatzResearch.WordTrace tailWord_2354535 prefixEnd_2354535 1209008172834050604684197 := by
  unfold tailWord_2354535
  simp only [CollatzResearch.WordTrace]
  refine ⟨85876946524929292408497059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57251297683286194938998039 85876946524929292408497059)
  ·
    refine ⟨128815419787393938612745589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85876946524929292408497059 128815419787393938612745589)
    ·
      refine ⟨12076445605068181744944899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128815419787393938612745589 12076445605068181744944899)
      ·
        refine ⟨18114668407602272617417349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12076445605068181744944899 18114668407602272617417349)
        ·
          refine ⟨3396500326425426115765753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18114668407602272617417349 3396500326425426115765753)
          ·
            refine ⟨2547375244819069586824315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3396500326425426115765753 2547375244819069586824315)
            ·
              refine ⟨3821062867228604380236473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547375244819069586824315 3821062867228604380236473)
              ·
                refine ⟨2865797150421453285177355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821062867228604380236473 2865797150421453285177355)
                ·
                  refine ⟨4298695725632179927766033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865797150421453285177355 4298695725632179927766033)
                  ·
                    refine ⟨3224021794224134945824525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4298695725632179927766033 3224021794224134945824525)
                    ·
                      refine ⟨1209008172834050604684197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3224021794224134945824525 1209008172834050604684197)
                      ·
                        rfl

theorem cell23_2354535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2354535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354535 prefixEnd_2354535 := by exact prefixLift 2354535
  have htrace : WordTrace (prefixWord ++ tailWord_2354535) baseStart_2354535 baseEnd_2354535 := by
    simpa [prefixWord, tailWord_2354535, baseEnd_2354535] using wordTrace_append hprefix tailTrace_2354535
  have hstable : (prefixWord ++ tailWord_2354535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354535).length < 2 ^ (prefixWord ++ tailWord_2354535).sum := by decide
  have hdescent : baseEnd_2354535 < baseStart_2354535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354571 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 3, 4, 2]
def baseStart_2354571 : Nat := 118140960795 + 2354571 * 2 ^ 59
def prefixEnd_2354571 : Nat := 4983230072969 + 3 ^ 40 * 2354571 * 2
def baseEnd_2354571 : Nat := 1209026658137612463834031

theorem tailTrace_2354571 : CollatzResearch.WordTrace tailWord_2354571 prefixEnd_2354571 1209026658137612463834031 := by
  unfold tailWord_2354571
  simp only [CollatzResearch.WordTrace]
  refine ⟨85878259552798870556807567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57252173035199247037871711 85878259552798870556807567)
  ·
    refine ⟨128817389329198305835211351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85878259552798870556807567 128817389329198305835211351)
    ·
      refine ⟨193226083993797458752817027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128817389329198305835211351 193226083993797458752817027)
      ·
        refine ⟨289839125990696188129225541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193226083993797458752817027 289839125990696188129225541)
        ·
          refine ⟨54344836123255535274229789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 289839125990696188129225541 54344836123255535274229789)
          ·
            refine ⟨20379313546220825727836171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54344836123255535274229789 20379313546220825727836171)
            ·
              refine ⟨30568970319331238591754257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20379313546220825727836171 30568970319331238591754257)
              ·
                refine ⟨22926727739498428943815693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30568970319331238591754257 22926727739498428943815693)
                ·
                  refine ⟨8597522902311910853930885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22926727739498428943815693 8597522902311910853930885)
                  ·
                    refine ⟨1612035544183483285112041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8597522902311910853930885 1612035544183483285112041)
                    ·
                      refine ⟨1209026658137612463834031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612035544183483285112041 1209026658137612463834031)
                      ·
                        rfl

theorem cell23_2354571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4, 2].length) (baseStart_2354571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354571 prefixEnd_2354571 := by exact prefixLift 2354571
  have htrace : WordTrace (prefixWord ++ tailWord_2354571) baseStart_2354571 baseEnd_2354571 := by
    simpa [prefixWord, tailWord_2354571, baseEnd_2354571] using wordTrace_append hprefix tailTrace_2354571
  have hstable : (prefixWord ++ tailWord_2354571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354571).length < 2 ^ (prefixWord ++ tailWord_2354571).sum := by decide
  have hdescent : baseEnd_2354571 < baseStart_2354571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354605 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2354605 : Nat := 118140960795 + 2354605 * 2 ^ 59
def prefixEnd_2354605 : Nat := 4983230072969 + 3 ^ 40 * 2354605 * 2
def baseEnd_2354605 : Nat := 1209044116479865330808875

theorem tailTrace_2354605 : CollatzResearch.WordTrace tailWord_2354605 prefixEnd_2354605 1209044116479865330808875 := by
  unfold tailWord_2354605
  simp only [CollatzResearch.WordTrace]
  refine ⟨85879499634675694363545269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57252999756450462909030179 85879499634675694363545269)
  ·
    refine ⟨8051203090750846346582369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85879499634675694363545269 8051203090750846346582369)
    ·
      refine ⟨6038402318063134759936777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8051203090750846346582369 6038402318063134759936777)
      ·
        refine ⟨4528801738547351069952583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6038402318063134759936777 4528801738547351069952583)
        ·
          refine ⟨6793202607821026604928875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528801738547351069952583 6793202607821026604928875)
          ·
            refine ⟨10189803911731539907393313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6793202607821026604928875 10189803911731539907393313)
            ·
              refine ⟨7642352933798654930544985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10189803911731539907393313 7642352933798654930544985)
              ·
                refine ⟨5731764700348991197908739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7642352933798654930544985 5731764700348991197908739)
                ·
                  refine ⟨8597647050523486796863109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5731764700348991197908739 8597647050523486796863109)
                  ·
                    refine ⟨1612058821973153774411833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8597647050523486796863109 1612058821973153774411833)
                    ·
                      refine ⟨1209044116479865330808875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612058821973153774411833 1209044116479865330808875)
                      ·
                        rfl

theorem cell23_2354605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2354605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354605 prefixEnd_2354605 := by exact prefixLift 2354605
  have htrace : WordTrace (prefixWord ++ tailWord_2354605) baseStart_2354605 baseEnd_2354605 := by
    simpa [prefixWord, tailWord_2354605, baseEnd_2354605] using wordTrace_append hprefix tailTrace_2354605
  have hstable : (prefixWord ++ tailWord_2354605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354605).length < 2 ^ (prefixWord ++ tailWord_2354605).sum := by decide
  have hdescent : baseEnd_2354605 < baseStart_2354605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354621 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_2354621 : Nat := 118140960795 + 2354621 * 2 ^ 59
def prefixEnd_2354621 : Nat := 4983230072969 + 3 ^ 40 * 2354621 * 2
def baseEnd_2354621 : Nat := 1209052332170337268208801

theorem tailTrace_2354621 : CollatzResearch.WordTrace tailWord_2354621 prefixEnd_2354621 1209052332170337268208801 := by
  unfold tailWord_2354621
  simp only [CollatzResearch.WordTrace]
  refine ⟨85880083202617729096127717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57253388801745152730751811 85880083202617729096127717)
  ·
    refine ⟨16102515600490824205523947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85880083202617729096127717 16102515600490824205523947)
    ·
      refine ⟨24153773400736236308285921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16102515600490824205523947 24153773400736236308285921)
      ·
        refine ⟨18115330050552177231214441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24153773400736236308285921 18115330050552177231214441)
        ·
          refine ⟨13586497537914132923410831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18115330050552177231214441 13586497537914132923410831)
          ·
            refine ⟨20379746306871199385116247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13586497537914132923410831 20379746306871199385116247)
            ·
              refine ⟨30569619460306799077674371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20379746306871199385116247 30569619460306799077674371)
              ·
                refine ⟨45854429190460198616511557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30569619460306799077674371 45854429190460198616511557)
                ·
                  refine ⟨8597705473211287240595917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45854429190460198616511557 8597705473211287240595917)
                  ·
                    refine ⟨3224139552454232715223469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8597705473211287240595917 3224139552454232715223469)
                    ·
                      refine ⟨1209052332170337268208801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3224139552454232715223469 1209052332170337268208801)
                      ·
                        rfl

theorem cell23_2354621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_2354621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354621 prefixEnd_2354621 := by exact prefixLift 2354621
  have htrace : WordTrace (prefixWord ++ tailWord_2354621) baseStart_2354621 baseEnd_2354621 := by
    simpa [prefixWord, tailWord_2354621, baseEnd_2354621] using wordTrace_append hprefix tailTrace_2354621
  have hstable : (prefixWord ++ tailWord_2354621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354621).length < 2 ^ (prefixWord ++ tailWord_2354621).sum := by decide
  have hdescent : baseEnd_2354621 < baseStart_2354621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354628 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 7]
def baseStart_2354628 : Nat := 118140960795 + 2354628 * 2 ^ 59
def prefixEnd_2354628 : Nat := 4983230072969 + 3 ^ 40 * 2354628 * 2
def baseEnd_2354628 : Nat := 134339547392768748980141

theorem tailTrace_2354628 : CollatzResearch.WordTrace tailWord_2354628 prefixEnd_2354628 134339547392768748980141 := by
  unfold tailWord_2354628
  simp only [CollatzResearch.WordTrace]
  refine ⟨42940169256796184645816269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57253559009061579527755025 42940169256796184645816269)
  ·
    refine ⟨16102563471298569242181101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42940169256796184645816269 16102563471298569242181101)
    ·
      refine ⟨6038461301736963465817913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16102563471298569242181101 6038461301736963465817913)
      ·
        refine ⟨4528845976302722599363435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6038461301736963465817913 4528845976302722599363435)
        ·
          refine ⟨6793268964454083899045153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528845976302722599363435 6793268964454083899045153)
          ·
            refine ⟨5094951723340562924283865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6793268964454083899045153 5094951723340562924283865)
            ·
              refine ⟨3821213792505422193212899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5094951723340562924283865 3821213792505422193212899)
              ·
                refine ⟨5731820688758133289819349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821213792505422193212899 5731820688758133289819349)
                ·
                  refine ⟨134339547392768748980141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5731820688758133289819349 134339547392768748980141)
                  ·
                    rfl

theorem cell23_2354628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_2354628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354628 prefixEnd_2354628 := by exact prefixLift 2354628
  have htrace : WordTrace (prefixWord ++ tailWord_2354628) baseStart_2354628 baseEnd_2354628 := by
    simpa [prefixWord, tailWord_2354628, baseEnd_2354628] using wordTrace_append hprefix tailTrace_2354628
  have hstable : (prefixWord ++ tailWord_2354628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354628).length < 2 ^ (prefixWord ++ tailWord_2354628).sum := by decide
  have hdescent : baseEnd_2354628 < baseStart_2354628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354671 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 5, 4]
def baseStart_2354671 : Nat := 118140960795 + 2354671 * 2 ^ 59
def prefixEnd_2354671 : Nat := 4983230072969 + 3 ^ 40 * 2354671 * 2
def baseEnd_2354671 : Nat := 403026002067687357527857

theorem tailTrace_2354671 : CollatzResearch.WordTrace tailWord_2354671 prefixEnd_2354671 403026002067687357527857 := by
  unfold tailWord_2354671
  simp only [CollatzResearch.WordTrace]
  refine ⟨85881906852436587635447867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57254604568291058423631911 85881906852436587635447867)
  ·
    refine ⟨128822860278654881453171801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85881906852436587635447867 128822860278654881453171801)
    ·
      refine ⟨96617145208991161089878851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128822860278654881453171801 96617145208991161089878851)
      ·
        refine ⟨144925717813486741634818277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96617145208991161089878851 144925717813486741634818277)
        ·
          refine ⟨27173572090028764056528427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144925717813486741634818277 27173572090028764056528427)
          ·
            refine ⟨40760358135043146084792641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27173572090028764056528427 40760358135043146084792641)
            ·
              refine ⟨30570268601282359563594481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40760358135043146084792641 30570268601282359563594481)
              ·
                refine ⟨22927701450961769672695861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30570268601282359563594481 22927701450961769672695861)
                ·
                  refine ⟨2149472011027665906815237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22927701450961769672695861 2149472011027665906815237)
                  ·
                    refine ⟨403026002067687357527857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2149472011027665906815237 403026002067687357527857)
                    ·
                      rfl

theorem cell23_2354671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_2354671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354671 prefixEnd_2354671 := by exact prefixLift 2354671
  have htrace : WordTrace (prefixWord ++ tailWord_2354671) baseStart_2354671 baseEnd_2354671 := by
    simpa [prefixWord, tailWord_2354671, baseEnd_2354671] using wordTrace_append hprefix tailTrace_2354671
  have hstable : (prefixWord ++ tailWord_2354671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354671).length < 2 ^ (prefixWord ++ tailWord_2354671).sum := by decide
  have hdescent : baseEnd_2354671 < baseStart_2354671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354678 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2354678 : Nat := 118140960795 + 2354678 * 2 ^ 59
def prefixEnd_2354678 : Nat := 4983230072969 + 3 ^ 40 * 2354678 * 2
def baseEnd_2354678 : Nat := 1209081600567643545196039

theorem tailTrace_2354678 : CollatzResearch.WordTrace tailWord_2354678 prefixEnd_2354678 1209081600567643545196039 := by
  unfold tailWord_2354678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367635135213201739434543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57254774775607485220635125 5367635135213201739434543)
  ·
    refine ⟨8051452702819802609151815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5367635135213201739434543 8051452702819802609151815)
    ·
      refine ⟨12077179054229703913727723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8051452702819802609151815 12077179054229703913727723)
      ·
        refine ⟨18115768581344555870591585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12077179054229703913727723 18115768581344555870591585)
        ·
          refine ⟨13586826436008416902943689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18115768581344555870591585 13586826436008416902943689)
          ·
            refine ⟨10190119827006312677207767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13586826436008416902943689 10190119827006312677207767)
            ·
              refine ⟨15285179740509469015811651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10190119827006312677207767 15285179740509469015811651)
              ·
                refine ⟨22927769610764203523717477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15285179740509469015811651 22927769610764203523717477)
                ·
                  refine ⟨4298956802018288160697027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22927769610764203523717477 4298956802018288160697027)
                  ·
                    refine ⟨6448435203027432241045541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298956802018288160697027 6448435203027432241045541)
                    ·
                      refine ⟨1209081600567643545196039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6448435203027432241045541 1209081600567643545196039)
                      ·
                        rfl

theorem cell23_2354678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2354678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354678 prefixEnd_2354678 := by exact prefixLift 2354678
  have htrace : WordTrace (prefixWord ++ tailWord_2354678) baseStart_2354678 baseEnd_2354678 := by
    simpa [prefixWord, tailWord_2354678, baseEnd_2354678] using wordTrace_append hprefix tailTrace_2354678
  have hstable : (prefixWord ++ tailWord_2354678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354678).length < 2 ^ (prefixWord ++ tailWord_2354678).sum := by decide
  have hdescent : baseEnd_2354678 < baseStart_2354678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354738 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_2354738 : Nat := 118140960795 + 2354738 * 2 ^ 59
def prefixEnd_2354738 : Nat := 4983230072969 + 3 ^ 40 * 2354738 * 2
def baseEnd_2354738 : Nat := 1209112409406913310445763

theorem tailTrace_2354738 : CollatzResearch.WordTrace tailWord_2354738 prefixEnd_2354738 1209112409406913310445763 := by
  unfold tailWord_2354738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21471087635798464519534217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57256233695462572052091245 21471087635798464519534217)
  ·
    refine ⟨16103315726848848389650663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21471087635798464519534217 16103315726848848389650663)
    ·
      refine ⟨24154973590273272584475995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16103315726848848389650663 24154973590273272584475995)
      ·
        refine ⟨36232460385409908876713993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24154973590273272584475995 36232460385409908876713993)
        ·
          refine ⟨27174345289057431657535495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36232460385409908876713993 27174345289057431657535495)
          ·
            refine ⟨40761517933586147486303243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27174345289057431657535495 40761517933586147486303243)
            ·
              refine ⟨61142276900379221229454865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40761517933586147486303243 61142276900379221229454865)
              ·
                refine ⟨45856707675284415922091149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61142276900379221229454865 45856707675284415922091149)
                ·
                  refine ⟨17196265378231655970784181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45856707675284415922091149 17196265378231655970784181)
                  ·
                    refine ⟨1612149879209217747261017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17196265378231655970784181 1612149879209217747261017)
                    ·
                      refine ⟨1209112409406913310445763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612149879209217747261017 1209112409406913310445763)
                      ·
                        rfl

theorem cell23_2354738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_2354738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354738 prefixEnd_2354738 := by exact prefixLift 2354738
  have htrace : WordTrace (prefixWord ++ tailWord_2354738) baseStart_2354738 baseEnd_2354738 := by
    simpa [prefixWord, tailWord_2354738, baseEnd_2354738] using wordTrace_append hprefix tailTrace_2354738
  have hstable : (prefixWord ++ tailWord_2354738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354738).length < 2 ^ (prefixWord ++ tailWord_2354738).sum := by decide
  have hdescent : baseEnd_2354738 < baseStart_2354738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354768 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4]
def baseStart_2354768 : Nat := 118140960795 + 2354768 * 2 ^ 59
def prefixEnd_2354768 : Nat := 4983230072969 + 3 ^ 40 * 2354768 * 2
def baseEnd_2354768 : Nat := 1209127813826548193070625

theorem tailTrace_2354768 : CollatzResearch.WordTrace tailWord_2354768 prefixEnd_2354768 1209127813826548193070625 := by
  unfold tailWord_2354768
  simp only [CollatzResearch.WordTrace]
  refine ⟨42942722366542586600864479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57256963155390115467819305 42942722366542586600864479)
  ·
    refine ⟨64414083549813879901296719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42942722366542586600864479 64414083549813879901296719)
    ·
      refine ⟨96621125324720819851945079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64414083549813879901296719 96621125324720819851945079)
      ·
        refine ⟨144931687987081229777917619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96621125324720819851945079 144931687987081229777917619)
        ·
          refine ⟨217397531980621844666876429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144931687987081229777917619 217397531980621844666876429)
          ·
            refine ⟨81524074492733191750078661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217397531980621844666876429 81524074492733191750078661)
            ·
              refine ⟨15285763967387473453139749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81524074492733191750078661 15285763967387473453139749)
              ·
                refine ⟨2866080743885151272463703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15285763967387473453139749 2866080743885151272463703)
                ·
                  refine ⟨4299121115827726908695555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866080743885151272463703 4299121115827726908695555)
                  ·
                    refine ⟨6448681673741590363043333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4299121115827726908695555 6448681673741590363043333)
                    ·
                      refine ⟨1209127813826548193070625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6448681673741590363043333 1209127813826548193070625)
                      ·
                        rfl

theorem cell23_2354768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_2354768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354768 prefixEnd_2354768 := by exact prefixLift 2354768
  have htrace : WordTrace (prefixWord ++ tailWord_2354768) baseStart_2354768 baseEnd_2354768 := by
    simpa [prefixWord, tailWord_2354768, baseEnd_2354768] using wordTrace_append hprefix tailTrace_2354768
  have hstable : (prefixWord ++ tailWord_2354768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354768).length < 2 ^ (prefixWord ++ tailWord_2354768).sum := by decide
  have hdescent : baseEnd_2354768 < baseStart_2354768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354771 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 3]
def baseStart_2354771 : Nat := 118140960795 + 2354771 * 2 ^ 59
def prefixEnd_2354771 : Nat := 4983230072969 + 3 ^ 40 * 2354771 * 2
def baseEnd_2354771 : Nat := 1209129354268511681333111

theorem tailTrace_2354771 : CollatzResearch.WordTrace tailWord_2354771 prefixEnd_2354771 1209129354268511681333111 := by
  unfold tailWord_2354771
  simp only [CollatzResearch.WordTrace]
  refine ⟨85885554152074304714088167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57257036101382869809392111 85885554152074304714088167)
  ·
    refine ⟨128828331228111457071132251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85885554152074304714088167 128828331228111457071132251)
    ·
      refine ⟨193242496842167185606698377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128828331228111457071132251 193242496842167185606698377)
      ·
        refine ⟨144931872631625389205023783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193242496842167185606698377 144931872631625389205023783)
        ·
          refine ⟨217397808947438083807535675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144931872631625389205023783 217397808947438083807535675)
          ·
            refine ⟨326096713421157125711303513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217397808947438083807535675 326096713421157125711303513)
            ·
              refine ⟨244572535065867844283477635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326096713421157125711303513 244572535065867844283477635)
              ·
                refine ⟨366858802598801766425216453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244572535065867844283477635 366858802598801766425216453)
                ·
                  refine ⟨68786025487275331204728085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366858802598801766425216453 68786025487275331204728085)
                  ·
                    refine ⟨3224344944716031150221629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68786025487275331204728085 3224344944716031150221629)
                    ·
                      refine ⟨1209129354268511681333111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3224344944716031150221629 1209129354268511681333111)
                      ·
                        rfl

theorem cell23_2354771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_2354771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354771 prefixEnd_2354771 := by exact prefixLift 2354771
  have htrace : WordTrace (prefixWord ++ tailWord_2354771) baseStart_2354771 baseEnd_2354771 := by
    simpa [prefixWord, tailWord_2354771, baseEnd_2354771] using wordTrace_append hprefix tailTrace_2354771
  have hstable : (prefixWord ++ tailWord_2354771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354771).length < 2 ^ (prefixWord ++ tailWord_2354771).sum := by decide
  have hdescent : baseEnd_2354771 < baseStart_2354771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354785 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_2354785 : Nat := 118140960795 + 2354785 * 2 ^ 59
def prefixEnd_2354785 : Nat := 4983230072969 + 3 ^ 40 * 2354785 * 2
def baseEnd_2354785 : Nat := 1209136542997674626558047

theorem tailTrace_2354785 : CollatzResearch.WordTrace tailWord_2354785 prefixEnd_2354785 1209136542997674626558047 := by
  unfold tailWord_2354785
  simp only [CollatzResearch.WordTrace]
  refine ⟨85886064774023585105097809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57257376516015723403398539 85886064774023585105097809)
  ·
    refine ⟨64414548580517688828823357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85886064774023585105097809 64414548580517688828823357)
    ·
      refine ⟨24155455717694133310808759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64414548580517688828823357 24155455717694133310808759)
      ·
        refine ⟨36233183576541199966213139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24155455717694133310808759 36233183576541199966213139)
        ·
          refine ⟨54349775364811799949319709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36233183576541199966213139 54349775364811799949319709)
          ·
            refine ⟨20381165761804424980994891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54349775364811799949319709 20381165761804424980994891)
            ·
              refine ⟨30571748642706637471492337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20381165761804424980994891 30571748642706637471492337)
              ·
                refine ⟨22928811482029978103619253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30571748642706637471492337 22928811482029978103619253)
                ·
                  refine ⟨2149576076440310447214305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22928811482029978103619253 2149576076440310447214305)
                  ·
                    refine ⟨1612182057330232835410729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2149576076440310447214305 1612182057330232835410729)
                    ·
                      refine ⟨1209136542997674626558047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612182057330232835410729 1209136542997674626558047)
                      ·
                        rfl

theorem cell23_2354785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_2354785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354785 prefixEnd_2354785 := by exact prefixLift 2354785
  have htrace : WordTrace (prefixWord ++ tailWord_2354785) baseStart_2354785 baseEnd_2354785 := by
    simpa [prefixWord, tailWord_2354785, baseEnd_2354785] using wordTrace_append hprefix tailTrace_2354785
  have hstable : (prefixWord ++ tailWord_2354785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354785).length < 2 ^ (prefixWord ++ tailWord_2354785).sum := by decide
  have hdescent : baseEnd_2354785 < baseStart_2354785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354802 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_2354802 : Nat := 118140960795 + 2354802 * 2 ^ 59
def prefixEnd_2354802 : Nat := 4983230072969 + 3 ^ 40 * 2354802 * 2
def baseEnd_2354802 : Nat := 1209145272168801060045469

theorem tailTrace_2354802 : CollatzResearch.WordTrace tailWord_2354802 prefixEnd_2354802 1209145272168801060045469 := by
  unfold tailWord_2354802
  simp only [CollatzResearch.WordTrace]
  refine ⟨21471671203740499252116665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57257789876641331338977773 21471671203740499252116665)
  ·
    refine ⟨16103753402805374439087499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21471671203740499252116665 16103753402805374439087499)
    ·
      refine ⟨24155630104208061658631249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16103753402805374439087499 24155630104208061658631249)
      ·
        refine ⟨18116722578156046243973437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24155630104208061658631249 18116722578156046243973437)
        ·
          refine ⟨6793770966808517341490039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18116722578156046243973437 6793770966808517341490039)
          ·
            refine ⟨10190656450212776012235059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6793770966808517341490039 10190656450212776012235059)
            ·
              refine ⟨15285984675319164018352589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10190656450212776012235059 15285984675319164018352589)
              ·
                refine ⟨5732244253244686506882221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15285984675319164018352589 5732244253244686506882221)
                ·
                  refine ⟨2149591594966757440080833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5732244253244686506882221 2149591594966757440080833)
                  ·
                    refine ⟨1612193696225068080060625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2149591594966757440080833 1612193696225068080060625)
                    ·
                      refine ⟨1209145272168801060045469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612193696225068080060625 1209145272168801060045469)
                      ·
                        rfl

theorem cell23_2354802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_2354802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354802 prefixEnd_2354802 := by exact prefixLift 2354802
  have htrace : WordTrace (prefixWord ++ tailWord_2354802) baseStart_2354802 baseEnd_2354802 := by
    simpa [prefixWord, tailWord_2354802, baseEnd_2354802] using wordTrace_append hprefix tailTrace_2354802
  have hstable : (prefixWord ++ tailWord_2354802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354802).length < 2 ^ (prefixWord ++ tailWord_2354802).sum := by decide
  have hdescent : baseEnd_2354802 < baseStart_2354802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354805 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2354805 : Nat := 118140960795 + 2354805 * 2 ^ 59
def prefixEnd_2354805 : Nat := 4983230072969 + 3 ^ 40 * 2354805 * 2
def baseEnd_2354805 : Nat := 1209146812610764548307955

theorem tailTrace_2354805 : CollatzResearch.WordTrace tailWord_2354805 prefixEnd_2354805 1209146812610764548307955 := by
  unfold tailWord_2354805
  simp only [CollatzResearch.WordTrace]
  refine ⟨85886794233951128520825869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57257862822634085680550579 85886794233951128520825869)
  ·
    refine ⟨32207547837731673195309701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85886794233951128520825869 32207547837731673195309701)
    ·
      refine ⟨6038915219574688724120569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32207547837731673195309701 6038915219574688724120569)
      ·
        refine ⟨4529186414681016543090427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6038915219574688724120569 4529186414681016543090427)
        ·
          refine ⟨6793779622021524814635641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4529186414681016543090427 6793779622021524814635641)
          ·
            refine ⟨5095334716516143610976731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6793779622021524814635641 5095334716516143610976731)
            ·
              refine ⟨7643002074774215416465097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5095334716516143610976731 7643002074774215416465097)
              ·
                refine ⟨5732251556080661562348823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7643002074774215416465097 5732251556080661562348823)
                ·
                  refine ⟨8598377334120992343523235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5732251556080661562348823 8598377334120992343523235)
                  ·
                    refine ⟨12897566001181488515284853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8598377334120992343523235 12897566001181488515284853)
                    ·
                      refine ⟨1209146812610764548307955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12897566001181488515284853 1209146812610764548307955)
                      ·
                        rfl

theorem cell23_2354805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2354805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354805 prefixEnd_2354805 := by exact prefixLift 2354805
  have htrace : WordTrace (prefixWord ++ tailWord_2354805) baseStart_2354805 baseEnd_2354805 := by
    simpa [prefixWord, tailWord_2354805, baseEnd_2354805] using wordTrace_append hprefix tailTrace_2354805
  have hstable : (prefixWord ++ tailWord_2354805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354805).length < 2 ^ (prefixWord ++ tailWord_2354805).sum := by decide
  have hdescent : baseEnd_2354805 < baseStart_2354805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354845 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_2354845 : Nat := 118140960795 + 2354845 * 2 ^ 59
def prefixEnd_2354845 : Nat := 4983230072969 + 3 ^ 40 * 2354845 * 2
def baseEnd_2354845 : Nat := 1209167351836944391807771

theorem tailTrace_2354845 : CollatzResearch.WordTrace tailWord_2354845 prefixEnd_2354845 1209167351836944391807771 := by
  unfold tailWord_2354845
  simp only [CollatzResearch.WordTrace]
  refine ⟨85888253153806215352281989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57258835435870810234854659 85888253153806215352281989)
  ·
    refine ⟨16104047466338665378552873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85888253153806215352281989 16104047466338665378552873)
    ·
      refine ⟨12078035599753999033914655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16104047466338665378552873 12078035599753999033914655)
      ·
        refine ⟨18117053399630998550871983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12078035599753999033914655 18117053399630998550871983)
        ·
          refine ⟨27175580099446497826307975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18117053399630998550871983 27175580099446497826307975)
          ·
            refine ⟨40763370149169746739461963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27175580099446497826307975 40763370149169746739461963)
            ·
              refine ⟨61145055223754620109192945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40763370149169746739461963 61145055223754620109192945)
              ·
                refine ⟨45858791417815965081894709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61145055223754620109192945 45858791417815965081894709)
                ·
                  refine ⟨4299261695420246726427629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45858791417815965081894709 4299261695420246726427629)
                  ·
                    refine ⟨1612223135782592522410361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4299261695420246726427629 1612223135782592522410361)
                    ·
                      refine ⟨1209167351836944391807771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612223135782592522410361 1209167351836944391807771)
                      ·
                        rfl

theorem cell23_2354845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_2354845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354845 prefixEnd_2354845 := by exact prefixLift 2354845
  have htrace : WordTrace (prefixWord ++ tailWord_2354845) baseStart_2354845 baseEnd_2354845 := by
    simpa [prefixWord, tailWord_2354845, baseEnd_2354845] using wordTrace_append hprefix tailTrace_2354845
  have hstable : (prefixWord ++ tailWord_2354845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354845).length < 2 ^ (prefixWord ++ tailWord_2354845).sum := by decide
  have hdescent : baseEnd_2354845 < baseStart_2354845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354869 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2354869 : Nat := 118140960795 + 2354869 * 2 ^ 59
def prefixEnd_2354869 : Nat := 4983230072969 + 3 ^ 40 * 2354869 * 2
def baseEnd_2354869 : Nat := 1209179675372652297907661

theorem tailTrace_2354869 : CollatzResearch.WordTrace tailWord_2354869 prefixEnd_2354869 1209179675372652297907661 := by
  unfold tailWord_2354869
  simp only [CollatzResearch.WordTrace]
  refine ⟨85889128505719267451155661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57259419003812844967437107 85889128505719267451155661)
  ·
    refine ⟨32208423189644725294183373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85889128505719267451155661 32208423189644725294183373)
    ·
      refine ⟨12078158696116771985318765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32208423189644725294183373 12078158696116771985318765)
      ·
        refine ⟨4529309511043789494494537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12078158696116771985318765 4529309511043789494494537)
        ·
          refine ⟨3396982133282842120870903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4529309511043789494494537 3396982133282842120870903)
          ·
            refine ⟨5095473199924263181306355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396982133282842120870903 5095473199924263181306355)
            ·
              refine ⟨7643209799886394771959533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5095473199924263181306355 7643209799886394771959533)
              ·
                refine ⟨2866203674957398039484825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7643209799886394771959533 2866203674957398039484825)
                ·
                  refine ⟨2149652756218048529613619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2866203674957398039484825 2149652756218048529613619)
                  ·
                    refine ⟨3224479134327072794420429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2149652756218048529613619 3224479134327072794420429)
                    ·
                      refine ⟨1209179675372652297907661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3224479134327072794420429 1209179675372652297907661)
                      ·
                        rfl

theorem cell23_2354869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2354869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354869 prefixEnd_2354869 := by exact prefixLift 2354869
  have htrace : WordTrace (prefixWord ++ tailWord_2354869) baseStart_2354869 baseEnd_2354869 := by
    simpa [prefixWord, tailWord_2354869, baseEnd_2354869] using wordTrace_append hprefix tailTrace_2354869
  have hstable : (prefixWord ++ tailWord_2354869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354869).length < 2 ^ (prefixWord ++ tailWord_2354869).sum := by decide
  have hdescent : baseEnd_2354869 < baseStart_2354869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354925 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2354925 : Nat := 118140960795 + 2354925 * 2 ^ 59
def prefixEnd_2354925 : Nat := 4983230072969 + 3 ^ 40 * 2354925 * 2
def baseEnd_2354925 : Nat := 1209208430289304078807403

theorem tailTrace_2354925 : CollatzResearch.WordTrace tailWord_2354925 prefixEnd_2354925 1209208430289304078807403 := by
  unfold tailWord_2354925
  simp only [CollatzResearch.WordTrace]
  refine ⟨85891170993516389015194229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57260780662344259343462819 85891170993516389015194229)
  ·
    refine ⟨8052297280642161470174459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85891170993516389015194229 8052297280642161470174459)
    ·
      refine ⟨12078445920963242205261689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8052297280642161470174459 12078445920963242205261689)
      ·
        refine ⟨9058834440722431653946267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12078445920963242205261689 9058834440722431653946267)
        ·
          refine ⟨13588251661083647480919401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9058834440722431653946267 13588251661083647480919401)
          ·
            refine ⟨10191188745812735610689551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13588251661083647480919401 10191188745812735610689551)
            ·
              refine ⟨15286783118719103416034327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10191188745812735610689551 15286783118719103416034327)
              ·
                refine ⟨22930174678078655124051491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15286783118719103416034327 22930174678078655124051491)
                ·
                  refine ⟨34395262017117982686077237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22930174678078655124051491 34395262017117982686077237)
                  ·
                    refine ⟨3224555814104810876819741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34395262017117982686077237 3224555814104810876819741)
                    ·
                      refine ⟨1209208430289304078807403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3224555814104810876819741 1209208430289304078807403)
                      ·
                        rfl

theorem cell23_2354925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2354925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354925 prefixEnd_2354925 := by exact prefixLift 2354925
  have htrace : WordTrace (prefixWord ++ tailWord_2354925) baseStart_2354925 baseEnd_2354925 := by
    simpa [prefixWord, tailWord_2354925, baseEnd_2354925] using wordTrace_append hprefix tailTrace_2354925
  have hstable : (prefixWord ++ tailWord_2354925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354925).length < 2 ^ (prefixWord ++ tailWord_2354925).sum := by decide
  have hdescent : baseEnd_2354925 < baseStart_2354925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354932 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2354932 : Nat := 118140960795 + 2354932 * 2 ^ 59
def prefixEnd_2354932 : Nat := 4983230072969 + 3 ^ 40 * 2354932 * 2
def baseEnd_2354932 : Nat := 134356891628209505713319

theorem tailTrace_2354932 : CollatzResearch.WordTrace tailWord_2354932 prefixEnd_2354932 134356891628209505713319 := by
  unfold tailWord_2354932
  simp only [CollatzResearch.WordTrace]
  refine ⟨42945713152245514605349525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57260950869660686140466033 42945713152245514605349525)
  ·
    refine ⟨2013080304011508497125759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42945713152245514605349525 2013080304011508497125759)
    ·
      refine ⟨3019620456017262745688639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013080304011508497125759 3019620456017262745688639)
      ·
        refine ⟨4529430684025894118532959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3019620456017262745688639 4529430684025894118532959)
        ·
          refine ⟨6794146026038841177799439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4529430684025894118532959 6794146026038841177799439)
          ·
            refine ⟨10191219039058261766699159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6794146026038841177799439 10191219039058261766699159)
            ·
              refine ⟨15286828558587392650048739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10191219039058261766699159 15286828558587392650048739)
              ·
                refine ⟨22930242837881088975073109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15286828558587392650048739 22930242837881088975073109)
                ·
                  refine ⟨134356891628209505713319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22930242837881088975073109 134356891628209505713319)
                  ·
                    rfl

theorem cell23_2354932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2354932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354932 prefixEnd_2354932 := by exact prefixLift 2354932
  have htrace : WordTrace (prefixWord ++ tailWord_2354932) baseStart_2354932 baseEnd_2354932 := by
    simpa [prefixWord, tailWord_2354932, baseEnd_2354932] using wordTrace_append hprefix tailTrace_2354932
  have hstable : (prefixWord ++ tailWord_2354932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354932).length < 2 ^ (prefixWord ++ tailWord_2354932).sum := by decide
  have hdescent : baseEnd_2354932 < baseStart_2354932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354945 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2354945 : Nat := 118140960795 + 2354945 * 2 ^ 59
def prefixEnd_2354945 : Nat := 4983230072969 + 3 ^ 40 * 2354945 * 2
def baseEnd_2354945 : Nat := 403072899967464666852437

theorem tailTrace_2354945 : CollatzResearch.WordTrace tailWord_2354945 prefixEnd_2354945 403072899967464666852437 := by
  unfold tailWord_2354945
  simp only [CollatzResearch.WordTrace]
  refine ⟨85891900453443932430922289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57261266968962621620614859 85891900453443932430922289)
  ·
    refine ⟨64418925340082949323191717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85891900453443932430922289 64418925340082949323191717)
    ·
      refine ⟨12078548501265552998098447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64418925340082949323191717 12078548501265552998098447)
      ·
        refine ⟨18117822751898329497147671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12078548501265552998098447 18117822751898329497147671)
        ·
          refine ⟨27176734127847494245721507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18117822751898329497147671 27176734127847494245721507)
          ·
            refine ⟨40765101191771241368582261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27176734127847494245721507 40765101191771241368582261)
            ·
              refine ⟨3821728236728553878304587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40765101191771241368582261 3821728236728553878304587)
              ·
                refine ⟨5732592355092830817456881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821728236728553878304587 5732592355092830817456881)
                ·
                  refine ⟨4299444266319623113092661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5732592355092830817456881 4299444266319623113092661)
                  ·
                    refine ⟨403072899967464666852437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4299444266319623113092661 403072899967464666852437)
                    ·
                      rfl

theorem cell23_2354945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2354945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354945 prefixEnd_2354945 := by exact prefixLift 2354945
  have htrace : WordTrace (prefixWord ++ tailWord_2354945) baseStart_2354945 baseEnd_2354945 := by
    simpa [prefixWord, tailWord_2354945, baseEnd_2354945] using wordTrace_append hprefix tailTrace_2354945
  have hstable : (prefixWord ++ tailWord_2354945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354945).length < 2 ^ (prefixWord ++ tailWord_2354945).sum := by decide
  have hdescent : baseEnd_2354945 < baseStart_2354945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354968 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2354968 : Nat := 118140960795 + 2354968 * 2 ^ 59
def prefixEnd_2354968 : Nat := 4983230072969 + 3 ^ 40 * 2354968 * 2
def baseEnd_2354968 : Nat := 1209230509957447410569705

theorem tailTrace_2354968 : CollatzResearch.WordTrace tailWord_2354968 prefixEnd_2354968 1209230509957447410569705 := by
  unfold tailWord_2354968
  simp only [CollatzResearch.WordTrace]
  refine ⟨42946369666180303679504779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57261826221573738239339705 42946369666180303679504779)
  ·
    refine ⟨64419554499270455519257169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42946369666180303679504779 64419554499270455519257169)
    ·
      refine ⟨48314665874452841639442877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64419554499270455519257169 48314665874452841639442877)
      ·
        refine ⟨18117999702919815614791079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48314665874452841639442877 18117999702919815614791079)
        ·
          refine ⟨27176999554379723422186619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18117999702919815614791079 27176999554379723422186619)
          ·
            refine ⟨40765499331569585133279929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27176999554379723422186619 40765499331569585133279929)
            ·
              refine ⟨30574124498677188849959947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40765499331569585133279929 30574124498677188849959947)
              ·
                refine ⟨45861186748015783274939921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30574124498677188849959947 45861186748015783274939921)
                ·
                  refine ⟨34395890061011837456204941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45861186748015783274939921 34395890061011837456204941)
                  ·
                    refine ⟨12898458772879439046076853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34395890061011837456204941 12898458772879439046076853)
                    ·
                      refine ⟨1209230509957447410569705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12898458772879439046076853 1209230509957447410569705)
                      ·
                        rfl

theorem cell23_2354968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2354968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2354968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2354968 prefixEnd_2354968 := by exact prefixLift 2354968
  have htrace : WordTrace (prefixWord ++ tailWord_2354968) baseStart_2354968 baseEnd_2354968 := by
    simpa [prefixWord, tailWord_2354968, baseEnd_2354968] using wordTrace_append hprefix tailTrace_2354968
  have hstable : (prefixWord ++ tailWord_2354968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354968).length < 2 ^ (prefixWord ++ tailWord_2354968).sum := by decide
  have hdescent : baseEnd_2354968 < baseStart_2354968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355005 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 8]
def baseStart_2355005 : Nat := 118140960795 + 2355005 * 2 ^ 59
def prefixEnd_2355005 : Nat := 4983230072969 + 3 ^ 40 * 2355005 * 2
def baseEnd_2355005 : Nat := 134361056526851529534115

theorem tailTrace_2355005 : CollatzResearch.WordTrace tailWord_2355005 prefixEnd_2355005 134361056526851529534115 := by
  unfold tailWord_2355005
  simp only [CollatzResearch.WordTrace]
  refine ⟨85894088833226562678106469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57262725888817708452070979 85894088833226562678106469)
  ·
    refine ⟨16105141656229980502144963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85894088833226562678106469 16105141656229980502144963)
    ·
      refine ⟨24157712484344970753217445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16105141656229980502144963 24157712484344970753217445)
      ·
        refine ⟨4529571090814682016228271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24157712484344970753217445 4529571090814682016228271)
        ·
          refine ⟨6794356636222023024342407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4529571090814682016228271 6794356636222023024342407)
          ·
            refine ⟨10191534954333034536513611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6794356636222023024342407 10191534954333034536513611)
            ·
              refine ⟨15287302431499551804770417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10191534954333034536513611 15287302431499551804770417)
              ·
                refine ⟨11465476823624663853577813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15287302431499551804770417 11465476823624663853577813)
                ·
                  refine ⟨134361056526851529534115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11465476823624663853577813 134361056526851529534115)
                  ·
                    rfl

theorem cell23_2355005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_2355005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355005 prefixEnd_2355005 := by exact prefixLift 2355005
  have htrace : WordTrace (prefixWord ++ tailWord_2355005) baseStart_2355005 baseEnd_2355005 := by
    simpa [prefixWord, tailWord_2355005, baseEnd_2355005] using wordTrace_append hprefix tailTrace_2355005
  have hstable : (prefixWord ++ tailWord_2355005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355005).length < 2 ^ (prefixWord ++ tailWord_2355005).sum := by decide
  have hdescent : baseEnd_2355005 < baseStart_2355005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355026 : List Nat := [3, 2, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_2355026 : Nat := 118140960795 + 2355026 * 2 ^ 59
def prefixEnd_2355026 : Nat := 4983230072969 + 3 ^ 40 * 2355026 * 2
def baseEnd_2355026 : Nat := 403086763945136061214813

theorem tailTrace_2355026 : CollatzResearch.WordTrace tailWord_2355026 prefixEnd_2355026 403086763945136061214813 := by
  unfold tailWord_2355026
  simp only [CollatzResearch.WordTrace]
  refine ⟨21473713691537620816155233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57263236510766988843080621 21473713691537620816155233)
  ·
    refine ⟨16105285268653215612116425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21473713691537620816155233 16105285268653215612116425)
    ·
      refine ⟨12078963951489911709087319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16105285268653215612116425 12078963951489911709087319)
      ·
        refine ⟨18118445927234867563630979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12078963951489911709087319 18118445927234867563630979)
        ·
          refine ⟨27177668890852301345446469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18118445927234867563630979 27177668890852301345446469)
          ·
            refine ⟨5095812917034806502271213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27177668890852301345446469 5095812917034806502271213)
            ·
              refine ⟨1910929843888052438351705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5095812917034806502271213 1910929843888052438351705)
              ·
                refine ⟨1433197382916039328763779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1910929843888052438351705 1433197382916039328763779)
                ·
                  refine ⟨2149796074374058993145669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433197382916039328763779 2149796074374058993145669)
                  ·
                    refine ⟨403086763945136061214813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2149796074374058993145669 403086763945136061214813)
                    ·
                      rfl

theorem cell23_2355026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_2355026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355026 prefixEnd_2355026 := by exact prefixLift 2355026
  have htrace : WordTrace (prefixWord ++ tailWord_2355026) baseStart_2355026 baseEnd_2355026 := by
    simpa [prefixWord, tailWord_2355026, baseEnd_2355026] using wordTrace_append hprefix tailTrace_2355026
  have hstable : (prefixWord ++ tailWord_2355026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355026).length < 2 ^ (prefixWord ++ tailWord_2355026).sum := by decide
  have hdescent : baseEnd_2355026 < baseStart_2355026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355052 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_2355052 : Nat := 118140960795 + 2355052 * 2 ^ 59
def prefixEnd_2355052 : Nat := 4983230072969 + 3 ^ 40 * 2355052 * 2
def baseEnd_2355052 : Nat := 403091214110808360639773

theorem tailTrace_2355052 : CollatzResearch.WordTrace tailWord_2355052 prefixEnd_2355052 403091214110808360639773 := by
  unfold tailWord_2355052
  simp only [CollatzResearch.WordTrace]
  refine ⟨42947901532028144852533705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57263868709370859803378273 42947901532028144852533705)
  ·
    refine ⟨32210926149021108639400279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42947901532028144852533705 32210926149021108639400279)
    ·
      refine ⟨48316389223531662959100419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32210926149021108639400279 48316389223531662959100419)
      ·
        refine ⟨72474583835297494438650629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48316389223531662959100419 72474583835297494438650629)
        ·
          refine ⟨13588984469118280207246993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72474583835297494438650629 13588984469118280207246993)
          ·
            refine ⟨10191738351838710155435245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13588984469118280207246993 10191738351838710155435245)
            ·
              refine ⟨3821901881939516308288217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10191738351838710155435245 3821901881939516308288217)
              ·
                refine ⟨2866426411454637231216163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821901881939516308288217 2866426411454637231216163)
                ·
                  refine ⟨4299639617181955846824245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866426411454637231216163 4299639617181955846824245)
                  ·
                    refine ⟨403091214110808360639773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4299639617181955846824245 403091214110808360639773)
                    ·
                      rfl

theorem cell23_2355052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_2355052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355052 prefixEnd_2355052 := by exact prefixLift 2355052
  have htrace : WordTrace (prefixWord ++ tailWord_2355052) baseStart_2355052 baseEnd_2355052 := by
    simpa [prefixWord, tailWord_2355052, baseEnd_2355052] using wordTrace_append hprefix tailTrace_2355052
  have hstable : (prefixWord ++ tailWord_2355052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355052).length < 2 ^ (prefixWord ++ tailWord_2355052).sum := by decide
  have hdescent : baseEnd_2355052 < baseStart_2355052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355065 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 1, 6]
def baseStart_2355065 : Nat := 118140960795 + 2355065 * 2 ^ 59
def prefixEnd_2355065 : Nat := 4983230072969 + 3 ^ 40 * 2355065 * 2
def baseEnd_2355065 : Nat := 403093439193644510352253

theorem tailTrace_2355065 : CollatzResearch.WordTrace tailWord_2355065 prefixEnd_2355065 403093439193644510352253 := by
  unfold tailWord_2355065
  simp only [CollatzResearch.WordTrace]
  refine ⟨85896277213009192925290649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57264184808672795283527099 85896277213009192925290649)
  ·
    refine ⟨64422207909756894693967987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85896277213009192925290649 64422207909756894693967987)
    ·
      refine ⟨96633311864635342040951981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64422207909756894693967987 96633311864635342040951981)
      ·
        refine ⟨36237491949238253265356993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96633311864635342040951981 36237491949238253265356993)
        ·
          refine ⟨27178118961928689949017745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36237491949238253265356993 27178118961928689949017745)
          ·
            refine ⟨20383589221446517461763309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27178118961928689949017745 20383589221446517461763309)
            ·
              refine ⟨7643845958042444048161241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20383589221446517461763309 7643845958042444048161241)
              ·
                refine ⟨5732884468531833036120931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7643845958042444048161241 5732884468531833036120931)
                ·
                  refine ⟨8599326702797749554181397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5732884468531833036120931 8599326702797749554181397)
                  ·
                    refine ⟨403093439193644510352253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8599326702797749554181397 403093439193644510352253)
                    ·
                      rfl

theorem cell23_2355065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_2355065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355065 prefixEnd_2355065 := by exact prefixLift 2355065
  have htrace : WordTrace (prefixWord ++ tailWord_2355065) baseStart_2355065 baseEnd_2355065 := by
    simpa [prefixWord, tailWord_2355065, baseEnd_2355065] using wordTrace_append hprefix tailTrace_2355065
  have hstable : (prefixWord ++ tailWord_2355065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355065).length < 2 ^ (prefixWord ++ tailWord_2355065).sum := by decide
  have hdescent : baseEnd_2355065 < baseStart_2355065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355095 : List Nat := [1, 1, 3, 3, 1, 3, 3, 8]
def baseStart_2355095 : Nat := 118140960795 + 2355095 * 2 ^ 59
def prefixEnd_2355095 : Nat := 4983230072969 + 3 ^ 40 * 2355095 * 2
def baseEnd_2355095 : Nat := 44788730444465496803023

theorem tailTrace_2355095 : CollatzResearch.WordTrace tailWord_2355095 prefixEnd_2355095 44788730444465496803023 := by
  unfold tailWord_2355095
  simp only [CollatzResearch.WordTrace]
  refine ⟨85897371402900508048882739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57264914268600338699255159 85897371402900508048882739)
  ·
    refine ⟨128846057104350762073324109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85897371402900508048882739 128846057104350762073324109)
    ·
      refine ⟨48317271414131535777496541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128846057104350762073324109 48317271414131535777496541)
      ·
        refine ⟨18118976780299325916561203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48317271414131535777496541 18118976780299325916561203)
        ·
          refine ⟨27178465170448988874841805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18118976780299325916561203 27178465170448988874841805)
          ·
            refine ⟨10191924438918370828065677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27178465170448988874841805 10191924438918370828065677)
            ·
              refine ⟨3821971664594389060524629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10191924438918370828065677 3821971664594389060524629)
              ·
                refine ⟨44788730444465496803023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3821971664594389060524629 44788730444465496803023)
                ·
                  rfl

theorem cell23_2355095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 8].length) (baseStart_2355095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355095 prefixEnd_2355095 := by exact prefixLift 2355095
  have htrace : WordTrace (prefixWord ++ tailWord_2355095) baseStart_2355095 baseEnd_2355095 := by
    simpa [prefixWord, tailWord_2355095, baseEnd_2355095] using wordTrace_append hprefix tailTrace_2355095
  have hstable : (prefixWord ++ tailWord_2355095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355095).length < 2 ^ (prefixWord ++ tailWord_2355095).sum := by decide
  have hdescent : baseEnd_2355095 < baseStart_2355095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355182 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2355182 : Nat := 118140960795 + 2355182 * 2 ^ 59
def prefixEnd_2355182 : Nat := 4983230072969 + 3 ^ 40 * 2355182 * 2
def baseEnd_2355182 : Nat := 1209340394817509573293721

theorem tailTrace_2355182 : CollatzResearch.WordTrace tailWord_2355182 prefixEnd_2355182 1209340394817509573293721 := by
  unfold tailWord_2355182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10737568069198165238412475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57267029702390214604866533 10737568069198165238412475)
  ·
    refine ⟨16106352103797247857618713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10737568069198165238412475 16106352103797247857618713)
    ·
      refine ⟨12079764077847935893214035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16106352103797247857618713 12079764077847935893214035)
      ·
        refine ⟨18119646116771903839821053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12079764077847935893214035 18119646116771903839821053)
        ·
          refine ⟨6794867293789463939932895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18119646116771903839821053 6794867293789463939932895)
          ·
            refine ⟨10192300940684195909899343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6794867293789463939932895 10192300940684195909899343)
            ·
              refine ⟨15288451411026293864849015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10192300940684195909899343 15288451411026293864849015)
              ·
                refine ⟨22932677116539440797273523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15288451411026293864849015 22932677116539440797273523)
                ·
                  refine ⟨34399015674809161195910285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22932677116539440797273523 34399015674809161195910285)
                  ·
                    refine ⟨12899630878053435448466357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34399015674809161195910285 12899630878053435448466357)
                    ·
                      refine ⟨1209340394817509573293721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12899630878053435448466357 1209340394817509573293721)
                      ·
                        rfl

theorem cell23_2355182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2355182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355182 prefixEnd_2355182 := by exact prefixLift 2355182
  have htrace : WordTrace (prefixWord ++ tailWord_2355182) baseStart_2355182 baseEnd_2355182 := by
    simpa [prefixWord, tailWord_2355182, baseEnd_2355182] using wordTrace_append hprefix tailTrace_2355182
  have hstable : (prefixWord ++ tailWord_2355182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355182).length < 2 ^ (prefixWord ++ tailWord_2355182).sum := by decide
  have hdescent : baseEnd_2355182 < baseStart_2355182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355196 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_2355196 : Nat := 118140960795 + 2355196 * 2 ^ 59
def prefixEnd_2355196 : Nat := 4983230072969 + 3 ^ 40 * 2355196 * 2
def baseEnd_2355196 : Nat := 1209347583546672518518657

theorem tailTrace_2355196 : CollatzResearch.WordTrace tailWord_2355196 prefixEnd_2355196 1209347583546672518518657 := by
  unfold tailWord_2355196
  simp only [CollatzResearch.WordTrace]
  refine ⟨42950527587767301149154721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57267370117023068198872961 42950527587767301149154721)
  ·
    refine ⟨32212895690825475861866041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42950527587767301149154721 32212895690825475861866041)
    ·
      refine ⟨24159671768119106896399531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32212895690825475861866041 24159671768119106896399531)
      ·
        refine ⟨36239507652178660344599297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24159671768119106896399531 36239507652178660344599297)
        ·
          refine ⟨27179630739133995258449473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36239507652178660344599297 27179630739133995258449473)
          ·
            refine ⟨20384723054350496443837105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27179630739133995258449473 20384723054350496443837105)
            ·
              refine ⟨15288542290762872332877829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20384723054350496443837105 15288542290762872332877829)
              ·
                refine ⟨2866601679518038562414593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15288542290762872332877829 2866601679518038562414593)
                ·
                  refine ⟨2149951259638528921810945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2866601679518038562414593 2149951259638528921810945)
                  ·
                    refine ⟨1612463444728896691358209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2149951259638528921810945 1612463444728896691358209)
                    ·
                      refine ⟨1209347583546672518518657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612463444728896691358209 1209347583546672518518657)
                      ·
                        rfl

theorem cell23_2355196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_2355196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355196 prefixEnd_2355196 := by exact prefixLift 2355196
  have htrace : WordTrace (prefixWord ++ tailWord_2355196) baseStart_2355196 baseEnd_2355196 := by
    simpa [prefixWord, tailWord_2355196, baseEnd_2355196] using wordTrace_append hprefix tailTrace_2355196
  have hstable : (prefixWord ++ tailWord_2355196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355196).length < 2 ^ (prefixWord ++ tailWord_2355196).sum := by decide
  have hdescent : baseEnd_2355196 < baseStart_2355196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355212 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2355212 : Nat := 118140960795 + 2355212 * 2 ^ 59
def prefixEnd_2355212 : Nat := 4983230072969 + 3 ^ 40 * 2355212 * 2
def baseEnd_2355212 : Nat := 1209355799237144455918583

theorem tailTrace_2355212 : CollatzResearch.WordTrace tailWord_2355212 prefixEnd_2355212 1209355799237144455918583 := by
  unfold tailWord_2355212
  simp only [CollatzResearch.WordTrace]
  refine ⟨42950819371738318515445945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57267759162317758020594593 42950819371738318515445945)
  ·
    refine ⟨32213114528803738886584459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42950819371738318515445945 32213114528803738886584459)
    ·
      refine ⟨48319671793205608329876689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32213114528803738886584459 48319671793205608329876689)
      ·
        refine ⟨36239753844904206247407517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48319671793205608329876689 36239753844904206247407517)
        ·
          refine ⟨13589907691839077342777819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36239753844904206247407517 13589907691839077342777819)
          ·
            refine ⟨20384861537758616014166729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13589907691839077342777819 20384861537758616014166729)
            ·
              refine ⟨15288646153318962010625047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20384861537758616014166729 15288646153318962010625047)
              ·
                refine ⟨22932969229978443015937571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15288646153318962010625047 22932969229978443015937571)
                ·
                  refine ⟨34399453844967664523906357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22932969229978443015937571 34399453844967664523906357)
                  ·
                    refine ⟨3224948797965718549116221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34399453844967664523906357 3224948797965718549116221)
                    ·
                      refine ⟨1209355799237144455918583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3224948797965718549116221 1209355799237144455918583)
                      ·
                        rfl

theorem cell23_2355212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2355212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355212 prefixEnd_2355212 := by exact prefixLift 2355212
  have htrace : WordTrace (prefixWord ++ tailWord_2355212) baseStart_2355212 baseEnd_2355212 := by
    simpa [prefixWord, tailWord_2355212, baseEnd_2355212] using wordTrace_append hprefix tailTrace_2355212
  have hstable : (prefixWord ++ tailWord_2355212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355212).length < 2 ^ (prefixWord ++ tailWord_2355212).sum := by decide
  have hdescent : baseEnd_2355212 < baseStart_2355212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355225 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_2355225 : Nat := 118140960795 + 2355225 * 2 ^ 59
def prefixEnd_2355225 : Nat := 4983230072969 + 3 ^ 40 * 2355225 * 2
def baseEnd_2355225 : Nat := 1209362474485652905056023

theorem tailTrace_2355225 : CollatzResearch.WordTrace tailWord_2355225 prefixEnd_2355225 1209362474485652905056023 := by
  unfold tailWord_2355225
  simp only [CollatzResearch.WordTrace]
  refine ⟨85902112892429540251115129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57268075261619693500743419 85902112892429540251115129)
  ·
    refine ⟨64426584669322155188336347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85902112892429540251115129 64426584669322155188336347)
    ·
      refine ⟨96639877003983232782504521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64426584669322155188336347 96639877003983232782504521)
      ·
        refine ⟨72479907752987424586878391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96639877003983232782504521 72479907752987424586878391)
        ·
          refine ⟨108719861629481136880317587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72479907752987424586878391 108719861629481136880317587)
          ·
            refine ⟨163079792444221705320476381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108719861629481136880317587 163079792444221705320476381)
            ·
              refine ⟨61154922166583139495178643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163079792444221705320476381 61154922166583139495178643)
              ·
                refine ⟨91732383249874709242767965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61154922166583139495178643 91732383249874709242767965)
                ·
                  refine ⟨34399643718703015966037987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91732383249874709242767965 34399643718703015966037987)
                  ·
                    refine ⟨51599465578054523949056981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34399643718703015966037987 51599465578054523949056981)
                    ·
                      refine ⟨1209362474485652905056023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51599465578054523949056981 1209362474485652905056023)
                      ·
                        rfl

theorem cell23_2355225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_2355225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355225 prefixEnd_2355225 := by exact prefixLift 2355225
  have htrace : WordTrace (prefixWord ++ tailWord_2355225) baseStart_2355225 baseEnd_2355225 := by
    simpa [prefixWord, tailWord_2355225, baseEnd_2355225] using wordTrace_append hprefix tailTrace_2355225
  have hstable : (prefixWord ++ tailWord_2355225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355225).length < 2 ^ (prefixWord ++ tailWord_2355225).sum := by decide
  have hdescent : baseEnd_2355225 < baseStart_2355225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355296 : List Nat := [2, 1, 1, 3, 2, 3, 1, 5, 1, 4]
def baseStart_2355296 : Nat := 118140960795 + 2355296 * 2 ^ 59
def prefixEnd_2355296 : Nat := 4983230072969 + 3 ^ 40 * 2355296 * 2
def baseEnd_2355296 : Nat := 403132977204040709089399

theorem tailTrace_2355296 : CollatzResearch.WordTrace tailWord_2355296 prefixEnd_2355296 403132977204040709089399 := by
  unfold tailWord_2355296
  simp only [CollatzResearch.WordTrace]
  refine ⟨42952351237586159688474871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57269801650114879584633161 42952351237586159688474871)
  ·
    refine ⟨64428526856379239532712307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42952351237586159688474871 64428526856379239532712307)
    ·
      refine ⟨96642790284568859299068461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64428526856379239532712307 96642790284568859299068461)
      ·
        refine ⟨36241046356713322237150673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96642790284568859299068461 36241046356713322237150673)
        ·
          refine ⟨27180784767534991677863005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36241046356713322237150673 27180784767534991677863005)
          ·
            refine ⟨10192794287825621879198627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27180784767534991677863005 10192794287825621879198627)
            ·
              refine ⟨15289191431738432818797941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10192794287825621879198627 15289191431738432818797941)
              ·
                refine ⟨1433361696725478076762307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15289191431738432818797941 1433361696725478076762307)
                ·
                  refine ⟨2150042545088217115143461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433361696725478076762307 2150042545088217115143461)
                  ·
                    refine ⟨403132977204040709089399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2150042545088217115143461 403132977204040709089399)
                    ·
                      rfl

theorem cell23_2355296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 4].length) (baseStart_2355296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355296 prefixEnd_2355296 := by exact prefixLift 2355296
  have htrace : WordTrace (prefixWord ++ tailWord_2355296) baseStart_2355296 baseEnd_2355296 := by
    simpa [prefixWord, tailWord_2355296, baseEnd_2355296] using wordTrace_append hprefix tailTrace_2355296
  have hstable : (prefixWord ++ tailWord_2355296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355296).length < 2 ^ (prefixWord ++ tailWord_2355296).sum := by decide
  have hdescent : baseEnd_2355296 < baseStart_2355296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355312 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_2355312 : Nat := 118140960795 + 2355312 * 2 ^ 59
def prefixEnd_2355312 : Nat := 4983230072969 + 3 ^ 40 * 2355312 * 2
def baseEnd_2355312 : Nat := 1209407147302594064668123

theorem tailTrace_2355312 : CollatzResearch.WordTrace tailWord_2355312 prefixEnd_2355312 1209407147302594064668123 := by
  unfold tailWord_2355312
  simp only [CollatzResearch.WordTrace]
  refine ⟨42952643021557177054766095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57270190695409569406354793 42952643021557177054766095)
  ·
    refine ⟨64428964532335765582149143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42952643021557177054766095 64428964532335765582149143)
    ·
      refine ⟨96643446798503648373223715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64428964532335765582149143 96643446798503648373223715)
      ·
        refine ⟨144965170197755472559835573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96643446798503648373223715 144965170197755472559835573)
        ·
          refine ⟨13590484706039575552484585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144965170197755472559835573 13590484706039575552484585)
          ·
            refine ⟨10192863529529681664363439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13590484706039575552484585 10192863529529681664363439)
            ·
              refine ⟨15289295294294522496545159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10192863529529681664363439 15289295294294522496545159)
              ·
                refine ⟨22933942941441783744817739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15289295294294522496545159 22933942941441783744817739)
                ·
                  refine ⟨34400914412162675617226609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22933942941441783744817739 34400914412162675617226609)
                  ·
                    refine ⟨25800685809122006712919957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34400914412162675617226609 25800685809122006712919957)
                    ·
                      refine ⟨1209407147302594064668123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25800685809122006712919957 1209407147302594064668123)
                      ·
                        rfl

theorem cell23_2355312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_2355312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355312 prefixEnd_2355312 := by exact prefixLift 2355312
  have htrace : WordTrace (prefixWord ++ tailWord_2355312) baseStart_2355312 baseEnd_2355312 := by
    simpa [prefixWord, tailWord_2355312, baseEnd_2355312] using wordTrace_append hprefix tailTrace_2355312
  have hstable : (prefixWord ++ tailWord_2355312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355312).length < 2 ^ (prefixWord ++ tailWord_2355312).sum := by decide
  have hdescent : baseEnd_2355312 < baseStart_2355312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355346 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_2355346 : Nat := 118140960795 + 2355346 * 2 ^ 59
def prefixEnd_2355346 : Nat := 4983230072969 + 3 ^ 40 * 2355346 * 2
def baseEnd_2355346 : Nat := 1209424605644846931642967

theorem tailTrace_2355346 : CollatzResearch.WordTrace tailWord_2355346 prefixEnd_2355346 1209424605644846931642967 := by
  unfold tailWord_2355346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21476631531247794479067473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57271017416660785277513261 21476631531247794479067473)
  ·
    refine ⟨16107473648435845859300605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21476631531247794479067473 16107473648435845859300605)
    ·
      refine ⟨6040302618163442197237727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16107473648435845859300605 6040302618163442197237727)
      ·
        refine ⟨9060453927245163295856591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6040302618163442197237727 9060453927245163295856591)
        ·
          refine ⟨13590680890867744943784887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9060453927245163295856591 13590680890867744943784887)
          ·
            refine ⟨20386021336301617415677331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13590680890867744943784887 20386021336301617415677331)
            ·
              refine ⟨30579032004452426123515997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20386021336301617415677331 30579032004452426123515997)
              ·
                refine ⟨11467137001669659796318499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30579032004452426123515997 11467137001669659796318499)
                ·
                  refine ⟨17200705502504489694477749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11467137001669659796318499 17200705502504489694477749)
                  ·
                    refine ⟨1612566140859795908857289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17200705502504489694477749 1612566140859795908857289)
                    ·
                      refine ⟨1209424605644846931642967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612566140859795908857289 1209424605644846931642967)
                      ·
                        rfl

theorem cell23_2355346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_2355346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355346 prefixEnd_2355346 := by exact prefixLift 2355346
  have htrace : WordTrace (prefixWord ++ tailWord_2355346) baseStart_2355346 baseEnd_2355346 := by
    simpa [prefixWord, tailWord_2355346, baseEnd_2355346] using wordTrace_append hprefix tailTrace_2355346
  have hstable : (prefixWord ++ tailWord_2355346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355346).length < 2 ^ (prefixWord ++ tailWord_2355346).sum := by decide
  have hdescent : baseEnd_2355346 < baseStart_2355346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355379 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 3]
def baseStart_2355379 : Nat := 118140960795 + 2355379 * 2 ^ 59
def prefixEnd_2355379 : Nat := 4983230072969 + 3 ^ 40 * 2355379 * 2
def baseEnd_2355379 : Nat := 1209441550506445302530315

theorem tailTrace_2355379 : CollatzResearch.WordTrace tailWord_2355379 prefixEnd_2355379 1209441550506445302530315 := by
  unfold tailWord_2355379
  simp only [CollatzResearch.WordTrace]
  refine ⟨85907729733871624552221191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57271819822581083034814127 85907729733871624552221191)
  ·
    refine ⟨128861594600807436828331787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85907729733871624552221191 128861594600807436828331787)
    ·
      refine ⟨193292391901211155242497681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128861594600807436828331787 193292391901211155242497681)
      ·
        refine ⟨144969293925908366431873261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193292391901211155242497681 144969293925908366431873261)
        ·
          refine ⟨54363485222215637411952473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144969293925908366431873261 54363485222215637411952473)
          ·
            refine ⟨40772613916661728058964355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54363485222215637411952473 40772613916661728058964355)
            ·
              refine ⟨61158920874992592088446533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40772613916661728058964355 61158920874992592088446533)
              ·
                refine ⟨11467297664061111016583725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61158920874992592088446533 11467297664061111016583725)
                ·
                  refine ⟨4300236624022916631218897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11467297664061111016583725 4300236624022916631218897)
                  ·
                    refine ⟨3225177468017187473414173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300236624022916631218897 3225177468017187473414173)
                    ·
                      refine ⟨1209441550506445302530315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3225177468017187473414173 1209441550506445302530315)
                      ·
                        rfl

theorem cell23_2355379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_2355379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355379 prefixEnd_2355379 := by exact prefixLift 2355379
  have htrace : WordTrace (prefixWord ++ tailWord_2355379) baseStart_2355379 baseEnd_2355379 := by
    simpa [prefixWord, tailWord_2355379, baseEnd_2355379] using wordTrace_append hprefix tailTrace_2355379
  have hstable : (prefixWord ++ tailWord_2355379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355379).length < 2 ^ (prefixWord ++ tailWord_2355379).sum := by decide
  have hdescent : baseEnd_2355379 < baseStart_2355379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355389 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_2355389 : Nat := 118140960795 + 2355389 * 2 ^ 59
def prefixEnd_2355389 : Nat := 4983230072969 + 3 ^ 40 * 2355389 * 2
def baseEnd_2355389 : Nat := 1209446685312990263405269

theorem tailTrace_2355389 : CollatzResearch.WordTrace tailWord_2355389 prefixEnd_2355389 1209446685312990263405269 := by
  unfold tailWord_2355389
  simp only [CollatzResearch.WordTrace]
  refine ⟨85908094463835396260085221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57272062975890264173390147 85908094463835396260085221)
  ·
    refine ⟨16107767711969136798765979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85908094463835396260085221 16107767711969136798765979)
    ·
      refine ⟨24161651567953705198148969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16107767711969136798765979 24161651567953705198148969)
      ·
        refine ⟨18121238675965278898611727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24161651567953705198148969 18121238675965278898611727)
        ·
          refine ⟨27181858013947918347917591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18121238675965278898611727 27181858013947918347917591)
          ·
            refine ⟨40772787020921877521876387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27181858013947918347917591 40772787020921877521876387)
            ·
              refine ⟨61159180531382816282814581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40772787020921877521876387 61159180531382816282814581)
              ·
                refine ⟨5733673174817139026513867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61159180531382816282814581 5733673174817139026513867)
                ·
                  refine ⟨8600509762225708539770801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5733673174817139026513867 8600509762225708539770801)
                  ·
                    refine ⟨6450382321669281404828101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8600509762225708539770801 6450382321669281404828101)
                    ·
                      refine ⟨1209446685312990263405269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6450382321669281404828101 1209446685312990263405269)
                      ·
                        rfl

theorem cell23_2355389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_2355389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355389 prefixEnd_2355389 := by exact prefixLift 2355389
  have htrace : WordTrace (prefixWord ++ tailWord_2355389) baseStart_2355389 baseEnd_2355389 := by
    simpa [prefixWord, tailWord_2355389, baseEnd_2355389] using wordTrace_append hprefix tailTrace_2355389
  have hstable : (prefixWord ++ tailWord_2355389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355389).length < 2 ^ (prefixWord ++ tailWord_2355389).sum := by decide
  have hdescent : baseEnd_2355389 < baseStart_2355389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355390 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2355390 : Nat := 118140960795 + 2355390 * 2 ^ 59
def prefixEnd_2355390 : Nat := 4983230072969 + 3 ^ 40 * 2355390 * 2
def baseEnd_2355390 : Nat := 403149066264548253164255

theorem tailTrace_2355390 : CollatzResearch.WordTrace tailWord_2355390 prefixEnd_2355390 403149066264548253164255 := by
  unfold tailWord_2355390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738516367103971678858953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57272087291221182287247749 10738516367103971678858953)
  ·
    refine ⟨8053887275327978759144215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10738516367103971678858953 8053887275327978759144215)
    ·
      refine ⟨12080830912991968138716323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8053887275327978759144215 12080830912991968138716323)
      ·
        refine ⟨18121246369487952208074485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12080830912991968138716323 18121246369487952208074485)
        ·
          refine ⟨1698866847139495519506983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18121246369487952208074485 1698866847139495519506983)
          ·
            refine ⟨2548300270709243279260475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698866847139495519506983 2548300270709243279260475)
            ·
              refine ⟨3822450406063864918890713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548300270709243279260475 3822450406063864918890713)
              ·
                refine ⟨2866837804547898689168035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822450406063864918890713 2866837804547898689168035)
                ·
                  refine ⟨4300256706821848033752053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866837804547898689168035 4300256706821848033752053)
                  ·
                    refine ⟨403149066264548253164255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4300256706821848033752053 403149066264548253164255)
                    ·
                      rfl

theorem cell23_2355390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2355390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355390 prefixEnd_2355390 := by exact prefixLift 2355390
  have htrace : WordTrace (prefixWord ++ tailWord_2355390) baseStart_2355390 baseEnd_2355390 := by
    simpa [prefixWord, tailWord_2355390, baseEnd_2355390] using wordTrace_append hprefix tailTrace_2355390
  have hstable : (prefixWord ++ tailWord_2355390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355390).length < 2 ^ (prefixWord ++ tailWord_2355390).sum := by decide
  have hdescent : baseEnd_2355390 < baseStart_2355390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355393 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2355393 : Nat := 118140960795 + 2355393 * 2 ^ 59
def prefixEnd_2355393 : Nat := 4983230072969 + 3 ^ 40 * 2355393 * 2
def baseEnd_2355393 : Nat := 1209448739235608247755251

theorem tailTrace_2355393 : CollatzResearch.WordTrace tailWord_2355393 prefixEnd_2355393 1209448739235608247755251 := by
  unfold tailWord_2355393
  simp only [CollatzResearch.WordTrace]
  refine ⟨85908240355820904943230833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57272160237213936628820555 85908240355820904943230833)
  ·
    refine ⟨64431180266865678707423125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85908240355820904943230833 64431180266865678707423125)
    ·
      refine ⟨3020211575009328689410459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64431180266865678707423125 3020211575009328689410459)
      ·
        refine ⟨4530317362513993034115689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3020211575009328689410459 4530317362513993034115689)
        ·
          refine ⟨3397738021885494775586767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4530317362513993034115689 3397738021885494775586767)
          ·
            refine ⟨5096607032828242163380151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397738021885494775586767 5096607032828242163380151)
            ·
              refine ⟨7644910549242363245070227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096607032828242163380151 7644910549242363245070227)
              ·
                refine ⟨11467365823863544867605341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7644910549242363245070227 11467365823863544867605341)
                ·
                  refine ⟨4300262183948829325352003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11467365823863544867605341 4300262183948829325352003)
                  ·
                    refine ⟨6450393275923243988028005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4300262183948829325352003 6450393275923243988028005)
                    ·
                      refine ⟨1209448739235608247755251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6450393275923243988028005 1209448739235608247755251)
                      ·
                        rfl

theorem cell23_2355393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2355393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355393 prefixEnd_2355393 := by exact prefixLift 2355393
  have htrace : WordTrace (prefixWord ++ tailWord_2355393) baseStart_2355393 baseEnd_2355393 := by
    simpa [prefixWord, tailWord_2355393, baseEnd_2355393] using wordTrace_append hprefix tailTrace_2355393
  have hstable : (prefixWord ++ tailWord_2355393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355393).length < 2 ^ (prefixWord ++ tailWord_2355393).sum := by decide
  have hdescent : baseEnd_2355393 < baseStart_2355393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355406 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2355406 : Nat := 118140960795 + 2355406 * 2 ^ 59
def prefixEnd_2355406 : Nat := 4983230072969 + 3 ^ 40 * 2355406 * 2
def baseEnd_2355406 : Nat := 1209455414484116696892691

theorem tailTrace_2355406 : CollatzResearch.WordTrace tailWord_2355406 prefixEnd_2355406 1209455414484116696892691 := by
  unfold tailWord_2355406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738589313096726020431759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57272476336515872108969381 10738589313096726020431759)
  ·
    refine ⟨16107883969645089030647639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10738589313096726020431759 16107883969645089030647639)
    ·
      refine ⟨24161825954467633545971459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16107883969645089030647639 24161825954467633545971459)
      ·
        refine ⟨36242738931701450318957189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24161825954467633545971459 36242738931701450318957189)
        ·
          refine ⟨6795513549694021934804473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36242738931701450318957189 6795513549694021934804473)
          ·
            refine ⟨5096635162270516451103355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6795513549694021934804473 5096635162270516451103355)
            ·
              refine ⟨7644952743405774676655033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096635162270516451103355 7644952743405774676655033)
              ·
                refine ⟨5733714557554331007491275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7644952743405774676655033 5733714557554331007491275)
                ·
                  refine ⟨8600571836331496511236913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5733714557554331007491275 8600571836331496511236913)
                  ·
                    refine ⟨6450428877248622383427685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8600571836331496511236913 6450428877248622383427685)
                    ·
                      refine ⟨1209455414484116696892691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6450428877248622383427685 1209455414484116696892691)
                      ·
                        rfl

theorem cell23_2355406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2355406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355406 prefixEnd_2355406 := by exact prefixLift 2355406
  have htrace : WordTrace (prefixWord ++ tailWord_2355406) baseStart_2355406 baseEnd_2355406 := by
    simpa [prefixWord, tailWord_2355406, baseEnd_2355406] using wordTrace_append hprefix tailTrace_2355406
  have hstable : (prefixWord ++ tailWord_2355406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355406).length < 2 ^ (prefixWord ++ tailWord_2355406).sum := by decide
  have hdescent : baseEnd_2355406 < baseStart_2355406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355409 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_2355409 : Nat := 118140960795 + 2355409 * 2 ^ 59
def prefixEnd_2355409 : Nat := 4983230072969 + 3 ^ 40 * 2355409 * 2
def baseEnd_2355409 : Nat := 1209456954926080185155177

theorem tailTrace_2355409 : CollatzResearch.WordTrace tailWord_2355409 prefixEnd_2355409 1209456954926080185155177 := by
  unfold tailWord_2355409
  simp only [CollatzResearch.WordTrace]
  refine ⟨85908823923762939675813281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57272549282508626450542187 85908823923762939675813281)
  ·
    refine ⟨64431617942822204756859961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85908823923762939675813281 64431617942822204756859961)
    ·
      refine ⟨48323713457116653567644971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64431617942822204756859961 48323713457116653567644971)
      ·
        refine ⟨72485570185674980351467457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48323713457116653567644971 72485570185674980351467457)
        ·
          refine ⟨54364177639256235263600593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72485570185674980351467457 54364177639256235263600593)
          ·
            refine ⟨40773133229442176447700445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54364177639256235263600593 40773133229442176447700445)
            ·
              refine ⟨15289924961040816167887667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40773133229442176447700445 15289924961040816167887667)
              ·
                refine ⟨22934887441561224251831501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15289924961040816167887667 22934887441561224251831501)
                ·
                  refine ⟨8600582790585459094436813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22934887441561224251831501 8600582790585459094436813)
                  ·
                    refine ⟨3225218546469547160413805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8600582790585459094436813 3225218546469547160413805)
                    ·
                      refine ⟨1209456954926080185155177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3225218546469547160413805 1209456954926080185155177)
                      ·
                        rfl

theorem cell23_2355409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_2355409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355409 prefixEnd_2355409 := by exact prefixLift 2355409
  have htrace : WordTrace (prefixWord ++ tailWord_2355409) baseStart_2355409 baseEnd_2355409 := by
    simpa [prefixWord, tailWord_2355409, baseEnd_2355409] using wordTrace_append hprefix tailTrace_2355409
  have hstable : (prefixWord ++ tailWord_2355409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355409).length < 2 ^ (prefixWord ++ tailWord_2355409).sum := by decide
  have hdescent : baseEnd_2355409 < baseStart_2355409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355413 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2355413 : Nat := 118140960795 + 2355413 * 2 ^ 59
def prefixEnd_2355413 : Nat := 4983230072969 + 3 ^ 40 * 2355413 * 2
def baseEnd_2355413 : Nat := 1209459008848698169505159

theorem tailTrace_2355413 : CollatzResearch.WordTrace tailWord_2355413 prefixEnd_2355413 1209459008848698169505159 := by
  unfold tailWord_2355413
  simp only [CollatzResearch.WordTrace]
  refine ⟨85908969815748448358958893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57272646543832298905972595 85908969815748448358958893)
  ·
    refine ⟨32215863680905668134609585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85908969815748448358958893 32215863680905668134609585)
    ·
      refine ⟨24161897760679251100957189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32215863680905668134609585 24161897760679251100957189)
      ·
        refine ⟨4530355830127359581429473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24161897760679251100957189 4530355830127359581429473)
        ·
          refine ⟨3397766872595519686072105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4530355830127359581429473 3397766872595519686072105)
          ·
            refine ⟨2548325154446639764554079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3397766872595519686072105 2548325154446639764554079)
            ·
              refine ⟨3822487731669959646831119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548325154446639764554079 3822487731669959646831119)
              ·
                refine ⟨5733731597504939470246679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3822487731669959646831119 5733731597504939470246679)
                ·
                  refine ⟨8600597396257409205370019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5733731597504939470246679 8600597396257409205370019)
                  ·
                    refine ⟨12900896094386113808055029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8600597396257409205370019 12900896094386113808055029)
                    ·
                      refine ⟨1209459008848698169505159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12900896094386113808055029 1209459008848698169505159)
                      ·
                        rfl

theorem cell23_2355413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2355413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355413 prefixEnd_2355413 := by exact prefixLift 2355413
  have htrace : WordTrace (prefixWord ++ tailWord_2355413) baseStart_2355413 baseEnd_2355413 := by
    simpa [prefixWord, tailWord_2355413, baseEnd_2355413] using wordTrace_append hprefix tailTrace_2355413
  have hstable : (prefixWord ++ tailWord_2355413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355413).length < 2 ^ (prefixWord ++ tailWord_2355413).sum := by decide
  have hdescent : baseEnd_2355413 < baseStart_2355413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355429 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_2355429 : Nat := 118140960795 + 2355429 * 2 ^ 59
def prefixEnd_2355429 : Nat := 4983230072969 + 3 ^ 40 * 2355429 * 2
def baseEnd_2355429 : Nat := 403155741513056702301695

theorem tailTrace_2355429 : CollatzResearch.WordTrace tailWord_2355429 prefixEnd_2355429 403155741513056702301695 := by
  unfold tailWord_2355429
  simp only [CollatzResearch.WordTrace]
  refine ⟨85909553383690483091541341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57273035589126988727694227 85909553383690483091541341)
  ·
    refine ⟨32216082518883931159328003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85909553383690483091541341 32216082518883931159328003)
    ·
      refine ⟨48324123778325896738992005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32216082518883931159328003 48324123778325896738992005)
      ·
        refine ⟨9060773208436105638561001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48324123778325896738992005 9060773208436105638561001)
        ·
          refine ⟨6795579906327079228920751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9060773208436105638561001 6795579906327079228920751)
          ·
            refine ⟨10193369859490618843381127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795579906327079228920751 10193369859490618843381127)
            ·
              refine ⟨15290054789235928265071691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10193369859490618843381127 15290054789235928265071691)
              ·
                refine ⟨22935082183853892397607537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15290054789235928265071691 22935082183853892397607537)
                ·
                  refine ⟨17201311637890419298205653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22935082183853892397607537 17201311637890419298205653)
                  ·
                    refine ⟨403155741513056702301695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17201311637890419298205653 403155741513056702301695)
                    ·
                      rfl

theorem cell23_2355429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_2355429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355429 prefixEnd_2355429 := by exact prefixLift 2355429
  have htrace : WordTrace (prefixWord ++ tailWord_2355429) baseStart_2355429 baseEnd_2355429 := by
    simpa [prefixWord, tailWord_2355429, baseEnd_2355429] using wordTrace_append hprefix tailTrace_2355429
  have hstable : (prefixWord ++ tailWord_2355429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355429).length < 2 ^ (prefixWord ++ tailWord_2355429).sum := by decide
  have hdescent : baseEnd_2355429 < baseStart_2355429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355436 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 5, 3, 2]
def baseStart_2355436 : Nat := 118140960795 + 2355436 * 2 ^ 59
def prefixEnd_2355436 : Nat := 4983230072969 + 3 ^ 40 * 2355436 * 2
def baseEnd_2355436 : Nat := 1209470818903751579517553

theorem tailTrace_2355436 : CollatzResearch.WordTrace tailWord_2355436 prefixEnd_2355436 1209470818903751579517553 := by
  unfold tailWord_2355436
  simp only [CollatzResearch.WordTrace]
  refine ⟨42954904347332561643523081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57273205796443415524697441 42954904347332561643523081)
  ·
    refine ⟨32216178260499421232642311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42954904347332561643523081 32216178260499421232642311)
    ·
      refine ⟨48324267390749131848963467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32216178260499421232642311 48324267390749131848963467)
      ·
        refine ⟨72486401086123697773445201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48324267390749131848963467 72486401086123697773445201)
        ·
          refine ⟨54364800814592773330083901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72486401086123697773445201 54364800814592773330083901)
          ·
            refine ⟨20386800305472289998781463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54364800814592773330083901 20386800305472289998781463)
            ·
              refine ⟨30580200458208434998172195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20386800305472289998781463 30580200458208434998172195)
              ·
                refine ⟨45870300687312652497258293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30580200458208434998172195 45870300687312652497258293)
                ·
                  refine ⟨4300340689435561171617965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45870300687312652497258293 4300340689435561171617965)
                  ·
                    refine ⟨1612627758538335439356737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4300340689435561171617965 1612627758538335439356737)
                    ·
                      refine ⟨1209470818903751579517553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612627758538335439356737 1209470818903751579517553)
                      ·
                        rfl

theorem cell23_2355436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_2355436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355436 prefixEnd_2355436 := by exact prefixLift 2355436
  have htrace : WordTrace (prefixWord ++ tailWord_2355436) baseStart_2355436 baseEnd_2355436 := by
    simpa [prefixWord, tailWord_2355436, baseEnd_2355436] using wordTrace_append hprefix tailTrace_2355436
  have hstable : (prefixWord ++ tailWord_2355436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355436).length < 2 ^ (prefixWord ++ tailWord_2355436).sum := by decide
  have hdescent : baseEnd_2355436 < baseStart_2355436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355489 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 7]
def baseStart_2355489 : Nat := 118140960795 + 2355489 * 2 ^ 59
def prefixEnd_2355489 : Nat := 4983230072969 + 3 ^ 40 * 2355489 * 2
def baseEnd_2355489 : Nat := 134388670375382208017201

theorem tailTrace_2355489 : CollatzResearch.WordTrace tailWord_2355489 prefixEnd_2355489 134388670375382208017201 := by
  unfold tailWord_2355489
  simp only [CollatzResearch.WordTrace]
  refine ⟨85911741763473113338725521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57274494508982075559150347 85911741763473113338725521)
  ·
    refine ⟨64433806322604835004044141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85911741763473113338725521 64433806322604835004044141)
    ·
      refine ⟨24162677370976813126516553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64433806322604835004044141 24162677370976813126516553)
      ·
        refine ⟨18122008028232609844887415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24162677370976813126516553 18122008028232609844887415)
        ·
          refine ⟨27183012042348914767331123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18122008028232609844887415 27183012042348914767331123)
          ·
            refine ⟨40774518063523372150996685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27183012042348914767331123 40774518063523372150996685)
            ·
              refine ⟨15290444273821264556623757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40774518063523372150996685 15290444273821264556623757)
              ·
                refine ⟨5733916602682974208733909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15290444273821264556623757 5733916602682974208733909)
                ·
                  refine ⟨134388670375382208017201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5733916602682974208733909 134388670375382208017201)
                  ·
                    rfl

theorem cell23_2355489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 7].length) (baseStart_2355489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355489 prefixEnd_2355489 := by exact prefixLift 2355489
  have htrace : WordTrace (prefixWord ++ tailWord_2355489) baseStart_2355489 baseEnd_2355489 := by
    simpa [prefixWord, tailWord_2355489, baseEnd_2355489] using wordTrace_append hprefix tailTrace_2355489
  have hstable : (prefixWord ++ tailWord_2355489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355489).length < 2 ^ (prefixWord ++ tailWord_2355489).sum := by decide
  have hdescent : baseEnd_2355489 < baseStart_2355489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355519 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 1, 7]
def baseStart_2355519 : Nat := 118140960795 + 2355519 * 2 ^ 59
def prefixEnd_2355519 : Nat := 4983230072969 + 3 ^ 40 * 2355519 * 2
def baseEnd_2355519 : Nat := 403171145932691584926557

theorem tailTrace_2355519 : CollatzResearch.WordTrace tailWord_2355519 prefixEnd_2355519 403171145932691584926557 := by
  unfold tailWord_2355519
  simp only [CollatzResearch.WordTrace]
  refine ⟨85912835953364428462317611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57275223968909618974878407 85912835953364428462317611)
  ·
    refine ⟨128869253930046642693476417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85912835953364428462317611 128869253930046642693476417)
    ·
      refine ⟨96651940447534982020107313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128869253930046642693476417 96651940447534982020107313)
      ·
        refine ⟨72488955335651236515080485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96651940447534982020107313 72488955335651236515080485)
        ·
          refine ⟨13591679125434606846577591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72488955335651236515080485 13591679125434606846577591)
          ·
            refine ⟨20387518688151910269866387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13591679125434606846577591 20387518688151910269866387)
            ·
              refine ⟨30581278032227865404799581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20387518688151910269866387 30581278032227865404799581)
              ·
                refine ⟨11467979262085449526799843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30581278032227865404799581 11467979262085449526799843)
                ·
                  refine ⟨17201968893128174290199765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11467979262085449526799843 17201968893128174290199765)
                  ·
                    refine ⟨403171145932691584926557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17201968893128174290199765 403171145932691584926557)
                    ·
                      rfl

theorem cell23_2355519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_2355519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355519 prefixEnd_2355519 := by exact prefixLift 2355519
  have htrace : WordTrace (prefixWord ++ tailWord_2355519) baseStart_2355519 baseEnd_2355519 := by
    simpa [prefixWord, tailWord_2355519, baseEnd_2355519] using wordTrace_append hprefix tailTrace_2355519
  have hstable : (prefixWord ++ tailWord_2355519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355519).length < 2 ^ (prefixWord ++ tailWord_2355519).sum := by decide
  have hdescent : baseEnd_2355519 < baseStart_2355519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355529 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_2355529 : Nat := 118140960795 + 2355529 * 2 ^ 59
def prefixEnd_2355529 : Nat := 4983230072969 + 3 ^ 40 * 2355529 * 2
def baseEnd_2355529 : Nat := 1209518572604619715654625

theorem tailTrace_2355529 : CollatzResearch.WordTrace tailWord_2355529 prefixEnd_2355529 1209518572604619715654625 := by
  unfold tailWord_2355529
  simp only [CollatzResearch.WordTrace]
  refine ⟨85913200683328200170181641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57275467122218800113454427 85913200683328200170181641)
  ·
    refine ⟨64434900512496150127636231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85913200683328200170181641 64434900512496150127636231)
    ·
      refine ⟨96652350768744225191454347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64434900512496150127636231 96652350768744225191454347)
      ·
        refine ⟨144978526153116337787181521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96652350768744225191454347 144978526153116337787181521)
        ·
          refine ⟨108733894614837253340386141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144978526153116337787181521 108733894614837253340386141)
          ·
            refine ⟨40775210480563970002644803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108733894614837253340386141 40775210480563970002644803)
            ·
              refine ⟨61162815720845955003967205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40775210480563970002644803 61162815720845955003967205)
              ·
                refine ⟨11468027947658616563243851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61162815720845955003967205 11468027947658616563243851)
                ·
                  refine ⟨17202041921487924844865777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11468027947658616563243851 17202041921487924844865777)
                  ·
                    refine ⟨12901531441115943633649333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17202041921487924844865777 12901531441115943633649333)
                    ·
                      refine ⟨1209518572604619715654625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12901531441115943633649333 1209518572604619715654625)
                      ·
                        rfl

theorem cell23_2355529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_2355529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355529 prefixEnd_2355529 := by exact prefixLift 2355529
  have htrace : WordTrace (prefixWord ++ tailWord_2355529) baseStart_2355529 baseEnd_2355529 := by
    simpa [prefixWord, tailWord_2355529, baseEnd_2355529] using wordTrace_append hprefix tailTrace_2355529
  have hstable : (prefixWord ++ tailWord_2355529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355529).length < 2 ^ (prefixWord ++ tailWord_2355529).sum := by decide
  have hdescent : baseEnd_2355529 < baseStart_2355529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355536 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 2, 5]
def baseStart_2355536 : Nat := 118140960795 + 2355536 * 2 ^ 59
def prefixEnd_2355536 : Nat := 4983230072969 + 3 ^ 40 * 2355536 * 2
def baseEnd_2355536 : Nat := 403174055656400396089031

theorem tailTrace_2355536 : CollatzResearch.WordTrace tailWord_2355536 prefixEnd_2355536 403174055656400396089031 := by
  unfold tailWord_2355536
  simp only [CollatzResearch.WordTrace]
  refine ⟨42956727997151420182843231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57275637329535226910457641 42956727997151420182843231)
  ·
    refine ⟨64435091995727130274264847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42956727997151420182843231 64435091995727130274264847)
    ·
      refine ⟨96652637993590695411397271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64435091995727130274264847 96652637993590695411397271)
      ·
        refine ⟨144978956990386043117095907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96652637993590695411397271 144978956990386043117095907)
        ·
          refine ⟨217468435485579064675643861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144978956990386043117095907 217468435485579064675643861)
          ·
            refine ⟨5096916456693259328335403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 217468435485579064675643861 5096916456693259328335403)
            ·
              refine ⟨7645374685039888992503105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096916456693259328335403 7645374685039888992503105)
              ·
                refine ⟨5734031013779916744377329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7645374685039888992503105 5734031013779916744377329)
                ·
                  refine ⟨4300523260334937558282997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5734031013779916744377329 4300523260334937558282997)
                  ·
                    refine ⟨403174055656400396089031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4300523260334937558282997 403174055656400396089031)
                    ·
                      rfl

theorem cell23_2355536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_2355536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355536 prefixEnd_2355536 := by exact prefixLift 2355536
  have htrace : WordTrace (prefixWord ++ tailWord_2355536) baseStart_2355536 baseEnd_2355536 := by
    simpa [prefixWord, tailWord_2355536, baseEnd_2355536] using wordTrace_append hprefix tailTrace_2355536
  have hstable : (prefixWord ++ tailWord_2355536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355536).length < 2 ^ (prefixWord ++ tailWord_2355536).sum := by decide
  have hdescent : baseEnd_2355536 < baseStart_2355536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355539 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4]
def baseStart_2355539 : Nat := 118140960795 + 2355539 * 2 ^ 59
def prefixEnd_2355539 : Nat := 4983230072969 + 3 ^ 40 * 2355539 * 2
def baseEnd_2355539 : Nat := 1209523707411164676529579

theorem tailTrace_2355539 : CollatzResearch.WordTrace tailWord_2355539 prefixEnd_2355539 1209523707411164676529579 := by
  unfold tailWord_2355539
  simp only [CollatzResearch.WordTrace]
  refine ⟨85913565413291971878045671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57275710275527981252030447 85913565413291971878045671)
  ·
    refine ⟨128870348119937957817068507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85913565413291971878045671 128870348119937957817068507)
    ·
      refine ⟨193305522179906936725602761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128870348119937957817068507 193305522179906936725602761)
      ·
        refine ⟨144979141634930202544202071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193305522179906936725602761 144979141634930202544202071)
        ·
          refine ⟨217468712452395303816303107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144979141634930202544202071 217468712452395303816303107)
          ·
            refine ⟨326203068678592955724454661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217468712452395303816303107 326203068678592955724454661)
            ·
              refine ⟨61163075377236179198335249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 326203068678592955724454661 61163075377236179198335249)
              ·
                refine ⟨45872306532927134398751437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61163075377236179198335249 45872306532927134398751437)
                ·
                  refine ⟨17202114949847675399531789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45872306532927134398751437 17202114949847675399531789)
                  ·
                    refine ⟨6450793106192878274824421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17202114949847675399531789 6450793106192878274824421)
                    ·
                      refine ⟨1209523707411164676529579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6450793106192878274824421 1209523707411164676529579)
                      ·
                        rfl

theorem cell23_2355539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_2355539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355539 prefixEnd_2355539 := by exact prefixLift 2355539
  have htrace : WordTrace (prefixWord ++ tailWord_2355539) baseStart_2355539 baseEnd_2355539 := by
    simpa [prefixWord, tailWord_2355539, baseEnd_2355539] using wordTrace_append hprefix tailTrace_2355539
  have hstable : (prefixWord ++ tailWord_2355539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355539).length < 2 ^ (prefixWord ++ tailWord_2355539).sum := by decide
  have hdescent : baseEnd_2355539 < baseStart_2355539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355540 : List Nat := [2, 4, 1, 1, 2, 3, 3, 2, 5]
def baseStart_2355540 : Nat := 118140960795 + 2355540 * 2 ^ 59
def prefixEnd_2355540 : Nat := 4983230072969 + 3 ^ 40 * 2355540 * 2
def baseEnd_2355540 : Nat := 134391580099091019179675

theorem tailTrace_2355540 : CollatzResearch.WordTrace tailWord_2355540 prefixEnd_2355540 134391580099091019179675 := by
  unfold tailWord_2355540
  simp only [CollatzResearch.WordTrace]
  refine ⟨42956800943144174524416037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57275734590858899365888049 42956800943144174524416037)
  ·
    refine ⟨8054400176839532723328007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42956800943144174524416037 8054400176839532723328007)
    ·
      refine ⟨12081600265259299084992011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8054400176839532723328007 12081600265259299084992011)
      ·
        refine ⟨18122400397888948627488017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12081600265259299084992011 18122400397888948627488017)
        ·
          refine ⟨13591800298416711470616013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18122400397888948627488017 13591800298416711470616013)
          ·
            refine ⟨5096925111906266801481005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13591800298416711470616013 5096925111906266801481005)
            ·
              refine ⟨1911346916964850050555377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5096925111906266801481005 1911346916964850050555377)
              ·
                refine ⟨1433510187723637537916533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911346916964850050555377 1433510187723637537916533)
                ·
                  refine ⟨134391580099091019179675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1433510187723637537916533 134391580099091019179675)
                  ·
                    rfl

theorem cell23_2355540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_2355540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355540 prefixEnd_2355540 := by exact prefixLift 2355540
  have htrace : WordTrace (prefixWord ++ tailWord_2355540) baseStart_2355540 baseEnd_2355540 := by
    simpa [prefixWord, tailWord_2355540, baseEnd_2355540] using wordTrace_append hprefix tailTrace_2355540
  have hstable : (prefixWord ++ tailWord_2355540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355540).length < 2 ^ (prefixWord ++ tailWord_2355540).sum := by decide
  have hdescent : baseEnd_2355540 < baseStart_2355540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355556 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_2355556 : Nat := 118140960795 + 2355556 * 2 ^ 59
def prefixEnd_2355556 : Nat := 4983230072969 + 3 ^ 40 * 2355556 * 2
def baseEnd_2355556 : Nat := 1209532436582291110017001

theorem tailTrace_2355556 : CollatzResearch.WordTrace tailWord_2355556 prefixEnd_2355556 1209532436582291110017001 := by
  unfold tailWord_2355556
  simp only [CollatzResearch.WordTrace]
  refine ⟨42957092727115191890707261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57276123636153589187609681 42957092727115191890707261)
  ·
    refine ⟨16108909772668196959015223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42957092727115191890707261 16108909772668196959015223)
    ·
      refine ⟨24163364659002295438522835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16108909772668196959015223 24163364659002295438522835)
      ·
        refine ⟨36245046988503443157784253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24163364659002295438522835 36245046988503443157784253)
        ·
          refine ⟨13591892620688791184169095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36245046988503443157784253 13591892620688791184169095)
          ·
            refine ⟨20387838931033186776253643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13591892620688791184169095 20387838931033186776253643)
            ·
              refine ⟨30581758396549780164380465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20387838931033186776253643 30581758396549780164380465)
              ·
                refine ⟨22936318797412335123285349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30581758396549780164380465 22936318797412335123285349)
                ·
                  refine ⟨4300559774514812835616003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22936318797412335123285349 4300559774514812835616003)
                  ·
                    refine ⟨6450839661772219253424005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4300559774514812835616003 6450839661772219253424005)
                    ·
                      refine ⟨1209532436582291110017001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6450839661772219253424005 1209532436582291110017001)
                      ·
                        rfl

theorem cell23_2355556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_2355556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355556 prefixEnd_2355556 := by exact prefixLift 2355556
  have htrace : WordTrace (prefixWord ++ tailWord_2355556) baseStart_2355556 baseEnd_2355556 := by
    simpa [prefixWord, tailWord_2355556, baseEnd_2355556] using wordTrace_append hprefix tailTrace_2355556
  have hstable : (prefixWord ++ tailWord_2355556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355556).length < 2 ^ (prefixWord ++ tailWord_2355556).sum := by decide
  have hdescent : baseEnd_2355556 < baseStart_2355556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355569 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2355569 : Nat := 118140960795 + 2355569 * 2 ^ 59
def prefixEnd_2355569 : Nat := 4983230072969 + 3 ^ 40 * 2355569 * 2
def baseEnd_2355569 : Nat := 1209539111830799559154441

theorem tailTrace_2355569 : CollatzResearch.WordTrace tailWord_2355569 prefixEnd_2355569 1209539111830799559154441 := by
  unfold tailWord_2355569
  simp only [CollatzResearch.WordTrace]
  refine ⟨85914659603183287001637761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57276439735455524667758507 85914659603183287001637761)
  ·
    refine ⟨64435994702387465251228321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85914659603183287001637761 64435994702387465251228321)
    ·
      refine ⟨48326996026790598938421241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64435994702387465251228321 48326996026790598938421241)
      ·
        refine ⟨36245247020092949203815931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48326996026790598938421241 36245247020092949203815931)
        ·
          refine ⟨54367870530139423805723897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36245247020092949203815931 54367870530139423805723897)
          ·
            refine ⟨40775902897604567854292923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54367870530139423805723897 40775902897604567854292923)
            ·
              refine ⟨61163854346406851781439385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40775902897604567854292923 61163854346406851781439385)
              ·
                refine ⟨45872890759805138836079539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61163854346406851781439385 45872890759805138836079539)
                ·
                  refine ⟨68809336139707708254119309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45872890759805138836079539 68809336139707708254119309)
                  ·
                    refine ⟨25803501052390390595294741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68809336139707708254119309 25803501052390390595294741)
                    ·
                      refine ⟨1209539111830799559154441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25803501052390390595294741 1209539111830799559154441)
                      ·
                        rfl

theorem cell23_2355569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2355569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355569 prefixEnd_2355569 := by exact prefixLift 2355569
  have htrace : WordTrace (prefixWord ++ tailWord_2355569) baseStart_2355569 baseEnd_2355569 := by
    simpa [prefixWord, tailWord_2355569, baseEnd_2355569] using wordTrace_append hprefix tailTrace_2355569
  have hstable : (prefixWord ++ tailWord_2355569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355569).length < 2 ^ (prefixWord ++ tailWord_2355569).sum := by decide
  have hdescent : baseEnd_2355569 < baseStart_2355569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355573 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2355573 : Nat := 118140960795 + 2355573 * 2 ^ 59
def prefixEnd_2355573 : Nat := 4983230072969 + 3 ^ 40 * 2355573 * 2
def baseEnd_2355573 : Nat := 1209541165753417543504423

theorem tailTrace_2355573 : CollatzResearch.WordTrace tailWord_2355573 prefixEnd_2355573 1209541165753417543504423 := by
  unfold tailWord_2355573
  simp only [CollatzResearch.WordTrace]
  refine ⟨85914805495168795684783373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57276536996779197123188915 85914805495168795684783373)
  ·
    refine ⟨32218052060688298381793765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85914805495168795684783373 32218052060688298381793765)
    ·
      refine ⟨6040884761379055946586331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32218052060688298381793765 6040884761379055946586331)
      ·
        refine ⟨9061327142068583919879497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6040884761379055946586331 9061327142068583919879497)
        ·
          refine ⟨6795995356551437939909623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9061327142068583919879497 6795995356551437939909623)
          ·
            refine ⟨10193993034827156909864435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795995356551437939909623 10193993034827156909864435)
            ·
              refine ⟨15290989552240735364796653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10193993034827156909864435 15290989552240735364796653)
              ·
                refine ⟨5734121082090275761798745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15290989552240735364796653 5734121082090275761798745)
                ·
                  refine ⟨4300590811567706821349059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5734121082090275761798745 4300590811567706821349059)
                  ·
                    refine ⟨6450886217351560232023589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4300590811567706821349059 6450886217351560232023589)
                    ·
                      refine ⟨1209541165753417543504423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6450886217351560232023589 1209541165753417543504423)
                      ·
                        rfl

theorem cell23_2355573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2355573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355573 prefixEnd_2355573 := by exact prefixLift 2355573
  have htrace : WordTrace (prefixWord ++ tailWord_2355573) baseStart_2355573 baseEnd_2355573 := by
    simpa [prefixWord, tailWord_2355573, baseEnd_2355573] using wordTrace_append hprefix tailTrace_2355573
  have hstable : (prefixWord ++ tailWord_2355573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355573).length < 2 ^ (prefixWord ++ tailWord_2355573).sum := by decide
  have hdescent : baseEnd_2355573 < baseStart_2355573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355593 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 3]
def baseStart_2355593 : Nat := 118140960795 + 2355593 * 2 ^ 59
def prefixEnd_2355593 : Nat := 4983230072969 + 3 ^ 40 * 2355593 * 2
def baseEnd_2355593 : Nat := 1209551435366507465254331

theorem tailTrace_2355593 : CollatzResearch.WordTrace tailWord_2355593 prefixEnd_2355593 1209551435366507465254331 := by
  unfold tailWord_2355593
  simp only [CollatzResearch.WordTrace]
  refine ⟨85915534955096339100511433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57277023303397559400340955 85915534955096339100511433)
  ·
    refine ⟨64436651216322254325383575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85915534955096339100511433 64436651216322254325383575)
    ·
      refine ⟨96654976824483381488075363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64436651216322254325383575 96654976824483381488075363)
      ·
        refine ⟨144982465236725072232113045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96654976824483381488075363 144982465236725072232113045)
        ·
          refine ⟨6796053057971487760880299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144982465236725072232113045 6796053057971487760880299)
          ·
            refine ⟨10194079586957231641320449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796053057971487760880299 10194079586957231641320449)
            ·
              refine ⟨7645559690217923730990337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10194079586957231641320449 7645559690217923730990337)
              ·
                refine ⟨5734169767663442798242753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7645559690217923730990337 5734169767663442798242753)
                ·
                  refine ⟨4300627325747582098682065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5734169767663442798242753 4300627325747582098682065)
                  ·
                    refine ⟨3225470494310686574011549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300627325747582098682065 3225470494310686574011549)
                    ·
                      refine ⟨1209551435366507465254331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3225470494310686574011549 1209551435366507465254331)
                      ·
                        rfl

theorem cell23_2355593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_2355593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355593 prefixEnd_2355593 := by exact prefixLift 2355593
  have htrace : WordTrace (prefixWord ++ tailWord_2355593) baseStart_2355593 baseEnd_2355593 := by
    simpa [prefixWord, tailWord_2355593, baseEnd_2355593] using wordTrace_append hprefix tailTrace_2355593
  have hstable : (prefixWord ++ tailWord_2355593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355593).length < 2 ^ (prefixWord ++ tailWord_2355593).sum := by decide
  have hdescent : baseEnd_2355593 < baseStart_2355593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355596 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 6]
def baseStart_2355596 : Nat := 118140960795 + 2355596 * 2 ^ 59
def prefixEnd_2355596 : Nat := 4983230072969 + 3 ^ 40 * 2355596 * 2
def baseEnd_2355596 : Nat := 134394775089830105946313

theorem tailTrace_2355596 : CollatzResearch.WordTrace tailWord_2355596 prefixEnd_2355596 134394775089830105946313 := by
  unfold tailWord_2355596
  simp only [CollatzResearch.WordTrace]
  refine ⟨42957822187042735306435321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57277096249390313741913761 42957822187042735306435321)
  ·
    refine ⟨32218366640282051479826491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42957822187042735306435321 32218366640282051479826491)
    ·
      refine ⟨48327549960423077219739737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32218366640282051479826491 48327549960423077219739737)
      ·
        refine ⟨36245662470317307914804803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48327549960423077219739737 36245662470317307914804803)
        ·
          refine ⟨54368493705475961872207205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36245662470317307914804803 54368493705475961872207205)
          ·
            refine ⟨10194092569776742851038851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54368493705475961872207205 10194092569776742851038851)
            ·
              refine ⟨15291138854665114276558277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10194092569776742851038851 15291138854665114276558277)
              ·
                refine ⟨2867088535249708926854677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15291138854665114276558277 2867088535249708926854677)
                ·
                  refine ⟨134394775089830105946313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2867088535249708926854677 134394775089830105946313)
                  ·
                    rfl

theorem cell23_2355596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_2355596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355596 prefixEnd_2355596 := by exact prefixLift 2355596
  have htrace : WordTrace (prefixWord ++ tailWord_2355596) baseStart_2355596 baseEnd_2355596 := by
    simpa [prefixWord, tailWord_2355596, baseEnd_2355596] using wordTrace_append hprefix tailTrace_2355596
  have hstable : (prefixWord ++ tailWord_2355596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355596).length < 2 ^ (prefixWord ++ tailWord_2355596).sum := by decide
  have hdescent : baseEnd_2355596 < baseStart_2355596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355680 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 3, 2, 2]
def baseStart_2355680 : Nat := 118140960795 + 2355680 * 2 ^ 59
def prefixEnd_2355680 : Nat := 4983230072969 + 3 ^ 40 * 2355680 * 2
def baseEnd_2355680 : Nat := 1209596108183448624866431

theorem tailTrace_2355680 : CollatzResearch.WordTrace tailWord_2355680 prefixEnd_2355680 1209596108183448624866431 := by
  unfold tailWord_2355680
  simp only [CollatzResearch.WordTrace]
  refine ⟨42959354052890576479464247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57279138737187435305952329 42959354052890576479464247)
  ·
    refine ⟨64439031079335864719196371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42959354052890576479464247 64439031079335864719196371)
    ·
      refine ⟨96658546619003797078794557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64439031079335864719196371 96658546619003797078794557)
      ·
        refine ⟨36246954982126423904547959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96658546619003797078794557 36246954982126423904547959)
        ·
          refine ⟨54370432473189635856821939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36246954982126423904547959 54370432473189635856821939)
          ·
            refine ⟨81555648709784453785232909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54370432473189635856821939 81555648709784453785232909)
            ·
              refine ⟨30583368266169170169462341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81555648709784453785232909 30583368266169170169462341)
              ·
                refine ⟨5734381549906719406774189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30583368266169170169462341 5734381549906719406774189)
                ·
                  refine ⟨2150393081215019777540321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5734381549906719406774189 2150393081215019777540321)
                  ·
                    refine ⟨1612794810911264833155241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2150393081215019777540321 1612794810911264833155241)
                    ·
                      refine ⟨1209596108183448624866431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612794810911264833155241 1209596108183448624866431)
                      ·
                        rfl

theorem cell23_2355680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_2355680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355680 prefixEnd_2355680 := by exact prefixLift 2355680
  have htrace : WordTrace (prefixWord ++ tailWord_2355680) baseStart_2355680 baseEnd_2355680 := by
    simpa [prefixWord, tailWord_2355680, baseEnd_2355680] using wordTrace_append hprefix tailTrace_2355680
  have hstable : (prefixWord ++ tailWord_2355680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355680).length < 2 ^ (prefixWord ++ tailWord_2355680).sum := by decide
  have hdescent : baseEnd_2355680 < baseStart_2355680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355751 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2355751 : Nat := 118140960795 + 2355751 * 2 ^ 59
def prefixEnd_2355751 : Nat := 4983230072969 + 3 ^ 40 * 2355751 * 2
def baseEnd_2355751 : Nat := 1209632565309917847078605

theorem tailTrace_2355751 : CollatzResearch.WordTrace tailWord_2355751 prefixEnd_2355751 1209632565309917847078605 := by
  unfold tailWord_2355751
  simp only [CollatzResearch.WordTrace]
  refine ⟨85921297688523932084763107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57280865125682621389842071 85921297688523932084763107)
  ·
    refine ⟨128881946532785898127144661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85921297688523932084763107 128881946532785898127144661)
    ·
      refine ⟨3020670621862169487354953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 128881946532785898127144661 3020670621862169487354953)
      ·
        refine ⟨2265502966396627115516215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3020670621862169487354953 2265502966396627115516215)
        ·
          refine ⟨3398254449594940673274323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265502966396627115516215 3398254449594940673274323)
          ·
            refine ⟨5097381674392411009911485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3398254449594940673274323 5097381674392411009911485)
            ·
              refine ⟨1911518127897154128716807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5097381674392411009911485 1911518127897154128716807)
              ·
                refine ⟨2867277191845731193075211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911518127897154128716807 2867277191845731193075211)
                ·
                  refine ⟨4300915787768596789612817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867277191845731193075211 4300915787768596789612817)
                  ·
                    refine ⟨3225686840826447592209613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300915787768596789612817 3225686840826447592209613)
                    ·
                      refine ⟨1209632565309917847078605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3225686840826447592209613 1209632565309917847078605)
                      ·
                        rfl

theorem cell23_2355751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2355751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355751 prefixEnd_2355751 := by exact prefixLift 2355751
  have htrace : WordTrace (prefixWord ++ tailWord_2355751) baseStart_2355751 baseEnd_2355751 := by
    simpa [prefixWord, tailWord_2355751, baseEnd_2355751] using wordTrace_append hprefix tailTrace_2355751
  have hstable : (prefixWord ++ tailWord_2355751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355751).length < 2 ^ (prefixWord ++ tailWord_2355751).sum := by decide
  have hdescent : baseEnd_2355751 < baseStart_2355751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355783 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_2355783 : Nat := 118140960795 + 2355783 * 2 ^ 59
def prefixEnd_2355783 : Nat := 4983230072969 + 3 ^ 40 * 2355783 * 2
def baseEnd_2355783 : Nat := 1209648996690861721878457

theorem tailTrace_2355783 : CollatzResearch.WordTrace tailWord_2355783 prefixEnd_2355783 1209648996690861721878457 := by
  unfold tailWord_2355783
  simp only [CollatzResearch.WordTrace]
  refine ⟨85922464824408001549928003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57281643216272001033285335 85922464824408001549928003)
  ·
    refine ⟨128883697236612002324892005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85922464824408001549928003 128883697236612002324892005)
    ·
      refine ⟨24165693231864750435917251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128883697236612002324892005 24165693231864750435917251)
      ·
        refine ⟨36248539847797125653875877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24165693231864750435917251 36248539847797125653875877)
        ·
          refine ⟨6796601221461961060101727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36248539847797125653875877 6796601221461961060101727)
          ·
            refine ⟨10194901832192941590152591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796601221461961060101727 10194901832192941590152591)
            ·
              refine ⟨15292352748289412385228887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10194901832192941590152591 15292352748289412385228887)
              ·
                refine ⟨22938529122434118577843331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15292352748289412385228887 22938529122434118577843331)
                ·
                  refine ⟨34407793683651177866764997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22938529122434118577843331 34407793683651177866764997)
                  ·
                    refine ⟨6451461315684595850018437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34407793683651177866764997 6451461315684595850018437)
                    ·
                      refine ⟨1209648996690861721878457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6451461315684595850018437 1209648996690861721878457)
                      ·
                        rfl

theorem cell23_2355783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_2355783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355783 prefixEnd_2355783 := by exact prefixLift 2355783
  have htrace : WordTrace (prefixWord ++ tailWord_2355783) baseStart_2355783 baseEnd_2355783 := by
    simpa [prefixWord, tailWord_2355783, baseEnd_2355783] using wordTrace_append hprefix tailTrace_2355783
  have hstable : (prefixWord ++ tailWord_2355783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355783).length < 2 ^ (prefixWord ++ tailWord_2355783).sum := by decide
  have hdescent : baseEnd_2355783 < baseStart_2355783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355787 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 2, 2, 2]
def baseStart_2355787 : Nat := 118140960795 + 2355787 * 2 ^ 59
def prefixEnd_2355787 : Nat := 4983230072969 + 3 ^ 40 * 2355787 * 2
def baseEnd_2355787 : Nat := 1209651050613479706228439

theorem tailTrace_2355787 : CollatzResearch.WordTrace tailWord_2355787 prefixEnd_2355787 1209651050613479706228439 := by
  unfold tailWord_2355787
  simp only [CollatzResearch.WordTrace]
  refine ⟨85922610716393510233073615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57281740477595673488715743 85922610716393510233073615)
  ·
    refine ⟨128883916074590265349610423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85922610716393510233073615 128883916074590265349610423)
    ·
      refine ⟨193325874111885398024415635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128883916074590265349610423 193325874111885398024415635)
      ·
        refine ⟨289988811167828097036623453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193325874111885398024415635 289988811167828097036623453)
        ·
          refine ⟨108745804187935536388733795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289988811167828097036623453 108745804187935536388733795)
          ·
            refine ⟨163118706281903304583100693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108745804187935536388733795 163118706281903304583100693)
            ·
              refine ⟨7646189356964217402332845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163118706281903304583100693 7646189356964217402332845)
              ·
                refine ⟨2867321008861581525874817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7646189356964217402332845 2867321008861581525874817)
                ·
                  refine ⟨2150490756646186144406113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2867321008861581525874817 2150490756646186144406113)
                  ·
                    refine ⟨1612868067484639608304585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2150490756646186144406113 1612868067484639608304585)
                    ·
                      refine ⟨1209651050613479706228439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612868067484639608304585 1209651050613479706228439)
                      ·
                        rfl

theorem cell23_2355787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 2, 2].length) (baseStart_2355787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355787 prefixEnd_2355787 := by exact prefixLift 2355787
  have htrace : WordTrace (prefixWord ++ tailWord_2355787) baseStart_2355787 baseEnd_2355787 := by
    simpa [prefixWord, tailWord_2355787, baseEnd_2355787] using wordTrace_append hprefix tailTrace_2355787
  have hstable : (prefixWord ++ tailWord_2355787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355787).length < 2 ^ (prefixWord ++ tailWord_2355787).sum := by decide
  have hdescent : baseEnd_2355787 < baseStart_2355787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355793 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 7]
def baseStart_2355793 : Nat := 118140960795 + 2355793 * 2 ^ 59
def prefixEnd_2355793 : Nat := 4983230072969 + 3 ^ 40 * 2355793 * 2
def baseEnd_2355793 : Nat := 134406014610822964750379

theorem tailTrace_2355793 : CollatzResearch.WordTrace tailWord_2355793 prefixEnd_2355793 134406014610822964750379 := by
  unfold tailWord_2355793
  simp only [CollatzResearch.WordTrace]
  refine ⟨85922829554371773257792033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57281886369581182171861355 85922829554371773257792033)
  ·
    refine ⟨64442122165778829943344025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85922829554371773257792033 64442122165778829943344025)
    ·
      refine ⟨48331591624334122457508019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64442122165778829943344025 48331591624334122457508019)
      ·
        refine ⟨72497387436501183686262029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48331591624334122457508019 72497387436501183686262029)
        ·
          refine ⟨27186520288687943882348261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72497387436501183686262029 27186520288687943882348261)
          ·
            refine ⟨5097472554128989477940299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27186520288687943882348261 5097472554128989477940299)
            ·
              refine ⟨7646208831193484216910449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097472554128989477940299 7646208831193484216910449)
              ·
                refine ⟨5734656623395113162682837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7646208831193484216910449 5734656623395113162682837)
                ·
                  refine ⟨134406014610822964750379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5734656623395113162682837 134406014610822964750379)
                  ·
                    rfl

theorem cell23_2355793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 7].length) (baseStart_2355793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355793 prefixEnd_2355793 := by exact prefixLift 2355793
  have htrace : WordTrace (prefixWord ++ tailWord_2355793) baseStart_2355793 baseEnd_2355793 := by
    simpa [prefixWord, tailWord_2355793, baseEnd_2355793] using wordTrace_append hprefix tailTrace_2355793
  have hstable : (prefixWord ++ tailWord_2355793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355793).length < 2 ^ (prefixWord ++ tailWord_2355793).sum := by decide
  have hdescent : baseEnd_2355793 < baseStart_2355793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355821 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_2355821 : Nat := 118140960795 + 2355821 * 2 ^ 59
def prefixEnd_2355821 : Nat := 4983230072969 + 3 ^ 40 * 2355821 * 2
def baseEnd_2355821 : Nat := 1209668508955732573203283

theorem tailTrace_2355821 : CollatzResearch.WordTrace tailWord_2355821 prefixEnd_2355821 1209668508955732573203283 := by
  unfold tailWord_2355821
  simp only [CollatzResearch.WordTrace]
  refine ⟨85923850798270334039811317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57282567198846889359874211 85923850798270334039811317)
  ·
    refine ⟨8055361012337843816232311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85923850798270334039811317 8055361012337843816232311)
    ·
      refine ⟨12083041518506765724348467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8055361012337843816232311 12083041518506765724348467)
      ·
        refine ⟨18124562277760148586522701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12083041518506765724348467 18124562277760148586522701)
        ·
          refine ⟨6796710854160055719946013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18124562277760148586522701 6796710854160055719946013)
          ·
            refine ⟨2548766570310020894979755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6796710854160055719946013 2548766570310020894979755)
            ·
              refine ⟨3823149855465031342469633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548766570310020894979755 3823149855465031342469633)
              ·
                refine ⟨2867362391598773506852225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3823149855465031342469633 2867362391598773506852225)
                ·
                  refine ⟨2150521793699080130139169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2867362391598773506852225 2150521793699080130139169)
                  ·
                    refine ⟨1612891345274310097604377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2150521793699080130139169 1612891345274310097604377)
                    ·
                      refine ⟨1209668508955732573203283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612891345274310097604377 1209668508955732573203283)
                      ·
                        rfl

theorem cell23_2355821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_2355821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355821 prefixEnd_2355821 := by exact prefixLift 2355821
  have htrace : WordTrace (prefixWord ++ tailWord_2355821) baseStart_2355821 baseEnd_2355821 := by
    simpa [prefixWord, tailWord_2355821, baseEnd_2355821] using wordTrace_append hprefix tailTrace_2355821
  have hstable : (prefixWord ++ tailWord_2355821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355821).length < 2 ^ (prefixWord ++ tailWord_2355821).sum := by decide
  have hdescent : baseEnd_2355821 < baseStart_2355821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355823 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 2, 5]
def baseStart_2355823 : Nat := 118140960795 + 2355823 * 2 ^ 59
def prefixEnd_2355823 : Nat := 4983230072969 + 3 ^ 40 * 2355823 * 2
def baseEnd_2355823 : Nat := 403223178639013855126091

theorem tailTrace_2355823 : CollatzResearch.WordTrace tailWord_2355823 prefixEnd_2355823 403223178639013855126091 := by
  unfold tailWord_2355823
  simp only [CollatzResearch.WordTrace]
  refine ⟨85923923744263088381384123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57282615829508725587589415 85923923744263088381384123)
  ·
    refine ⟨128885885616394632572076185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85923923744263088381384123 128885885616394632572076185)
    ·
      refine ⟨96664414212295974429057139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128885885616394632572076185 96664414212295974429057139)
      ·
        refine ⟨144996621318443961643585709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96664414212295974429057139 144996621318443961643585709)
        ·
          refine ⟨54373732994416485616344641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144996621318443961643585709 54373732994416485616344641)
          ·
            refine ⟨40780299745812364212258481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54373732994416485616344641 40780299745812364212258481)
            ·
              refine ⟨30585224809359273159193861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40780299745812364212258481 30585224809359273159193861)
              ·
                refine ⟨5734729651754863717348849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30585224809359273159193861 5734729651754863717348849)
                ·
                  refine ⟨4301047238816147788011637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5734729651754863717348849 4301047238816147788011637)
                  ·
                    refine ⟨403223178639013855126091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4301047238816147788011637 403223178639013855126091)
                    ·
                      rfl

theorem cell23_2355823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_2355823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355823 prefixEnd_2355823 := by exact prefixLift 2355823
  have htrace : WordTrace (prefixWord ++ tailWord_2355823) baseStart_2355823 baseEnd_2355823 := by
    simpa [prefixWord, tailWord_2355823, baseEnd_2355823] using wordTrace_append hprefix tailTrace_2355823
  have hstable : (prefixWord ++ tailWord_2355823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355823).length < 2 ^ (prefixWord ++ tailWord_2355823).sum := by decide
  have hdescent : baseEnd_2355823 < baseStart_2355823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355843 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4]
def baseStart_2355843 : Nat := 118140960795 + 2355843 * 2 ^ 59
def prefixEnd_2355843 : Nat := 4983230072969 + 3 ^ 40 * 2355843 * 2
def baseEnd_2355843 : Nat := 1209679805530131487128181

theorem tailTrace_2355843 : CollatzResearch.WordTrace tailWord_2355843 prefixEnd_2355843 1209679805530131487128181 := by
  unfold tailWord_2355843
  simp only [CollatzResearch.WordTrace]
  refine ⟨85924653204190631797112183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57283102136127087864741455 85924653204190631797112183)
  ·
    refine ⟨128886979806285947695668275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85924653204190631797112183 128886979806285947695668275)
    ·
      refine ⟨193330469709428921543502413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128886979806285947695668275 193330469709428921543502413)
      ·
        refine ⟨72498926141035845578813405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193330469709428921543502413 72498926141035845578813405)
        ·
          refine ⟨27187097302888442092055027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72498926141035845578813405 27187097302888442092055027)
          ·
            refine ⟨40780645954332663138082541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27187097302888442092055027 40780645954332663138082541)
            ·
              refine ⟨15292742232874748676780953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40780645954332663138082541 15292742232874748676780953)
              ·
                refine ⟨11469556674656061507585715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15292742232874748676780953 11469556674656061507585715)
                ·
                  refine ⟨17204335011984092261378573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11469556674656061507585715 17204335011984092261378573)
                  ·
                    refine ⟨6451625629494034598016965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17204335011984092261378573 6451625629494034598016965)
                    ·
                      refine ⟨1209679805530131487128181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6451625629494034598016965 1209679805530131487128181)
                      ·
                        rfl

theorem cell23_2355843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_2355843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355843 prefixEnd_2355843 := by exact prefixLift 2355843
  have htrace : WordTrace (prefixWord ++ tailWord_2355843) baseStart_2355843 baseEnd_2355843 := by
    simpa [prefixWord, tailWord_2355843, baseEnd_2355843] using wordTrace_append hprefix tailTrace_2355843
  have hstable : (prefixWord ++ tailWord_2355843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355843).length < 2 ^ (prefixWord ++ tailWord_2355843).sum := by decide
  have hdescent : baseEnd_2355843 < baseStart_2355843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355887 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 3, 4]
def baseStart_2355887 : Nat := 118140960795 + 2355887 * 2 ^ 59
def prefixEnd_2355887 : Nat := 4983230072969 + 3 ^ 40 * 2355887 * 2
def baseEnd_2355887 : Nat := 403234132892976438325993

theorem tailTrace_2355887 : CollatzResearch.WordTrace tailWord_2355887 prefixEnd_2355887 403234132892976438325993 := by
  unfold tailWord_2355887
  simp only [CollatzResearch.WordTrace]
  refine ⟨85926258016031227311713915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57284172010687484874475943 85926258016031227311713915)
  ·
    refine ⟨128889387024046840967570873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85926258016031227311713915 128889387024046840967570873)
    ·
      refine ⟨96667040268035130725678155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128889387024046840967570873 96667040268035130725678155)
      ·
        refine ⟨145000560402052696088517233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96667040268035130725678155 145000560402052696088517233)
        ·
          refine ⟨108750420301539522066387925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145000560402052696088517233 108750420301539522066387925)
          ·
            refine ⟨2548837975817332548430967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 108750420301539522066387925 2548837975817332548430967)
            ·
              refine ⟨3823256963725998822646451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548837975817332548430967 3823256963725998822646451)
              ·
                refine ⟨5734885445588998233969677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823256963725998822646451 5734885445588998233969677)
                ·
                  refine ⟨2150582042095874337738629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5734885445588998233969677 2150582042095874337738629)
                  ·
                    refine ⟨403234132892976438325993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2150582042095874337738629 403234132892976438325993)
                    ·
                      rfl

theorem cell23_2355887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_2355887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355887 prefixEnd_2355887 := by exact prefixLift 2355887
  have htrace : WordTrace (prefixWord ++ tailWord_2355887) baseStart_2355887 baseEnd_2355887 := by
    simpa [prefixWord, tailWord_2355887, baseEnd_2355887] using wordTrace_append hprefix tailTrace_2355887
  have hstable : (prefixWord ++ tailWord_2355887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355887).length < 2 ^ (prefixWord ++ tailWord_2355887).sum := by decide
  have hdescent : baseEnd_2355887 < baseStart_2355887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355900 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 6]
def baseStart_2355900 : Nat := 118140960795 + 2355900 * 2 ^ 59
def prefixEnd_2355900 : Nat := 4983230072969 + 3 ^ 40 * 2355900 * 2
def baseEnd_2355900 : Nat := 134412119325270862679491

theorem tailTrace_2355900 : CollatzResearch.WordTrace tailWord_2355900 prefixEnd_2355900 134412119325270862679491 := by
  unfold tailWord_2355900
  simp only [CollatzResearch.WordTrace]
  refine ⟨42963366082492065265968577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57284488109989420354624769 42963366082492065265968577)
  ·
    refine ⟨32222524561869048949476433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42963366082492065265968577 32222524561869048949476433)
    ·
      refine ⟨24166893421401786712107325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32222524561869048949476433 24166893421401786712107325)
      ·
        refine ⟨9062585033025670017040247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24166893421401786712107325 9062585033025670017040247)
        ·
          refine ⟨13593877549538505025560371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9062585033025670017040247 13593877549538505025560371)
          ·
            refine ⟨20390816324307757538340557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13593877549538505025560371 20390816324307757538340557)
            ·
              refine ⟨7646556121615409076877709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20390816324307757538340557 7646556121615409076877709)
              ·
                refine ⟨2867458545605778403829141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7646556121615409076877709 2867458545605778403829141)
                ·
                  refine ⟨134412119325270862679491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2867458545605778403829141 134412119325270862679491)
                  ·
                    rfl

theorem cell23_2355900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_2355900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355900 prefixEnd_2355900 := by exact prefixLift 2355900
  have htrace : WordTrace (prefixWord ++ tailWord_2355900) baseStart_2355900 baseEnd_2355900 := by
    simpa [prefixWord, tailWord_2355900, baseEnd_2355900] using wordTrace_append hprefix tailTrace_2355900
  have hstable : (prefixWord ++ tailWord_2355900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355900).length < 2 ^ (prefixWord ++ tailWord_2355900).sum := by decide
  have hdescent : baseEnd_2355900 < baseStart_2355900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355920 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 5, 5, 2]
def baseStart_2355920 : Nat := 118140960795 + 2355920 * 2 ^ 59
def prefixEnd_2355920 : Nat := 4983230072969 + 3 ^ 40 * 2355920 * 2
def baseEnd_2355920 : Nat := 1209719343540527685865327

theorem tailTrace_2355920 : CollatzResearch.WordTrace tailWord_2355920 prefixEnd_2355920 1209719343540527685865327 := by
  unfold tailWord_2355920
  simp only [CollatzResearch.WordTrace]
  refine ⟨42963730812455836973832607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57284974416607782631776809 42963730812455836973832607)
  ·
    refine ⟨64445596218683755460748911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42963730812455836973832607 64445596218683755460748911)
    ·
      refine ⟨96668394328025633191123367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64445596218683755460748911 96668394328025633191123367)
      ·
        refine ⟨145002591492038449786685051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96668394328025633191123367 145002591492038449786685051)
        ·
          refine ⟨217503887238057674680027577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145002591492038449786685051 217503887238057674680027577)
          ·
            refine ⟨163127915428543256010020683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217503887238057674680027577 163127915428543256010020683)
            ·
              refine ⟨244691873142814884015031025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163127915428543256010020683 244691873142814884015031025)
              ·
                refine ⟨183518904857111163011273269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244691873142814884015031025 183518904857111163011273269)
                ·
                  refine ⟨17204897330354171532306869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183518904857111163011273269 17204897330354171532306869)
                  ·
                    refine ⟨1612959124720703581153769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17204897330354171532306869 1612959124720703581153769)
                    ·
                      refine ⟨1209719343540527685865327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1612959124720703581153769 1209719343540527685865327)
                      ·
                        rfl

theorem cell23_2355920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 5, 2].length) (baseStart_2355920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355920 prefixEnd_2355920 := by exact prefixLift 2355920
  have htrace : WordTrace (prefixWord ++ tailWord_2355920) baseStart_2355920 baseEnd_2355920 := by
    simpa [prefixWord, tailWord_2355920, baseEnd_2355920] using wordTrace_append hprefix tailTrace_2355920
  have hstable : (prefixWord ++ tailWord_2355920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355920).length < 2 ^ (prefixWord ++ tailWord_2355920).sum := by decide
  have hdescent : baseEnd_2355920 < baseStart_2355920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355960 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 1, 6]
def baseStart_2355960 : Nat := 118140960795 + 2355960 * 2 ^ 59
def prefixEnd_2355960 : Nat := 4983230072969 + 3 ^ 40 * 2355960 * 2
def baseEnd_2355960 : Nat := 403246627588902509788381

theorem tailTrace_2355960 : CollatzResearch.WordTrace tailWord_2355960 prefixEnd_2355960 403246627588902509788381 := by
  unfold tailWord_2355960
  simp only [CollatzResearch.WordTrace]
  refine ⟨42964460272383380389560667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57285947029844507186080889 42964460272383380389560667)
  ·
    refine ⟨64446690408575070584341001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42964460272383380389560667 64446690408575070584341001)
    ·
      refine ⟨48335017806431302938255751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64446690408575070584341001 48335017806431302938255751)
      ·
        refine ⟨72502526709646954407383627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48335017806431302938255751 72502526709646954407383627)
        ·
          refine ⟨108753790064470431611075441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72502526709646954407383627 108753790064470431611075441)
          ·
            refine ⟨81565342548352823708306581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108753790064470431611075441 81565342548352823708306581)
            ·
              refine ⟨3823375431954038611326871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81565342548352823708306581 3823375431954038611326871)
              ·
                refine ⟨5735063147931057916990307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823375431954038611326871 5735063147931057916990307)
                ·
                  refine ⟨8602594721896586875485461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5735063147931057916990307 8602594721896586875485461)
                  ·
                    refine ⟨403246627588902509788381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8602594721896586875485461 403246627588902509788381)
                    ·
                      rfl

theorem cell23_2355960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_2355960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355960 prefixEnd_2355960 := by exact prefixLift 2355960
  have htrace : WordTrace (prefixWord ++ tailWord_2355960) baseStart_2355960 baseEnd_2355960 := by
    simpa [prefixWord, tailWord_2355960, baseEnd_2355960] using wordTrace_append hprefix tailTrace_2355960
  have hstable : (prefixWord ++ tailWord_2355960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355960).length < 2 ^ (prefixWord ++ tailWord_2355960).sum := by decide
  have hdescent : baseEnd_2355960 < baseStart_2355960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355963 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6]
def baseStart_2355963 : Nat := 118140960795 + 2355963 * 2 ^ 59
def prefixEnd_2355963 : Nat := 4983230072969 + 3 ^ 40 * 2355963 * 2
def baseEnd_2355963 : Nat := 1209741423208671017627629

theorem tailTrace_2355963 : CollatzResearch.WordTrace tailWord_2355963 prefixEnd_2355963 1209741423208671017627629 := by
  unfold tailWord_2355963
  simp only [CollatzResearch.WordTrace]
  refine ⟨85929029963755892291480543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57286019975837261527653695 85929029963755892291480543)
  ·
    refine ⟨128893544945633838437220815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85929029963755892291480543 128893544945633838437220815)
    ·
      refine ⟨193340317418450757655831223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128893544945633838437220815 193340317418450757655831223)
      ·
        refine ⟨290010476127676136483746835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193340317418450757655831223 290010476127676136483746835)
        ·
          refine ⟨435015714191514204725620253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290010476127676136483746835 435015714191514204725620253)
          ·
            refine ⟨163130892821817826772107595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 435015714191514204725620253 163130892821817826772107595)
            ·
              refine ⟨244696339232726740158161393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163130892821817826772107595 244696339232726740158161393)
              ·
                refine ⟨183522254424545055118621045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244696339232726740158161393 183522254424545055118621045)
                ·
                  refine ⟨17205211352301098917370723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183522254424545055118621045 17205211352301098917370723)
                  ·
                    refine ⟨25807817028451648376056085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17205211352301098917370723 25807817028451648376056085)
                    ·
                      refine ⟨1209741423208671017627629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25807817028451648376056085 1209741423208671017627629)
                      ·
                        rfl

theorem cell23_2355963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_2355963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355963 prefixEnd_2355963 := by exact prefixLift 2355963
  have htrace : WordTrace (prefixWord ++ tailWord_2355963) baseStart_2355963 baseEnd_2355963 := by
    simpa [prefixWord, tailWord_2355963, baseEnd_2355963] using wordTrace_append hprefix tailTrace_2355963
  have hstable : (prefixWord ++ tailWord_2355963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355963).length < 2 ^ (prefixWord ++ tailWord_2355963).sum := by decide
  have hdescent : baseEnd_2355963 < baseStart_2355963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355973 : List Nat := [1, 3, 1, 1, 2, 1, 1, 13]
def baseStart_2355973 : Nat := 118140960795 + 2355973 * 2 ^ 59
def prefixEnd_2355973 : Nat := 4983230072969 + 3 ^ 40 * 2355973 * 2
def baseEnd_2355973 : Nat := 44805428074637628833429

theorem tailTrace_2355973 : CollatzResearch.WordTrace tailWord_2355973 prefixEnd_2355973 44805428074637628833429 := by
  unfold tailWord_2355973
  simp only [CollatzResearch.WordTrace]
  refine ⟨85929394693719663999344573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57286263129146442666229715 85929394693719663999344573)
  ·
    refine ⟨32223523010144873999754215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85929394693719663999344573 32223523010144873999754215)
    ·
      refine ⟨48335284515217310999631323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32223523010144873999754215 48335284515217310999631323)
      ·
        refine ⟨72502926772825966499446985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48335284515217310999631323 72502926772825966499446985)
        ·
          refine ⟨54377195079619474874585239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72502926772825966499446985 54377195079619474874585239)
          ·
            refine ⟨81565792619429212311877859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54377195079619474874585239 81565792619429212311877859)
            ·
              refine ⟨122348688929143818467816789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81565792619429212311877859 122348688929143818467816789)
              ·
                refine ⟨44805428074637628833429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 122348688929143818467816789 44805428074637628833429)
                ·
                  rfl

theorem cell23_2355973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 13].length) (baseStart_2355973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355973 prefixEnd_2355973 := by exact prefixLift 2355973
  have htrace : WordTrace (prefixWord ++ tailWord_2355973) baseStart_2355973 baseEnd_2355973 := by
    simpa [prefixWord, tailWord_2355973, baseEnd_2355973] using wordTrace_append hprefix tailTrace_2355973
  have hstable : (prefixWord ++ tailWord_2355973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355973).length < 2 ^ (prefixWord ++ tailWord_2355973).sum := by decide
  have hdescent : baseEnd_2355973 < baseStart_2355973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355987 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 3]
def baseStart_2355987 : Nat := 118140960795 + 2355987 * 2 ^ 59
def prefixEnd_2355987 : Nat := 4983230072969 + 3 ^ 40 * 2355987 * 2
def baseEnd_2355987 : Nat := 1209753746744378923727519

theorem tailTrace_2355987 : CollatzResearch.WordTrace tailWord_2355987 prefixEnd_2355987 1209753746744378923727519 := by
  unfold tailWord_2355987
  simp only [CollatzResearch.WordTrace]
  refine ⟨85929905315668944390354215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57286603543779296260236143 85929905315668944390354215)
  ·
    refine ⟨128894857973503416585531323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85929905315668944390354215 128894857973503416585531323)
    ·
      refine ⟨193342286960255124878296985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128894857973503416585531323 193342286960255124878296985)
      ·
        refine ⟨145006715220191343658722739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193342286960255124878296985 145006715220191343658722739)
        ·
          refine ⟨217510072830287015488084109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145006715220191343658722739 217510072830287015488084109)
          ·
            refine ⟨81566277311357630808031541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217510072830287015488084109 81566277311357630808031541)
            ·
              refine ⟨7646838497939777888252957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81566277311357630808031541 7646838497939777888252957)
              ·
                refine ⟨2867564436727416708094859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7646838497939777888252957 2867564436727416708094859)
                ·
                  refine ⟨4301346655091125062142289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867564436727416708094859 4301346655091125062142289)
                  ·
                    refine ⟨3226009991318343796606717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4301346655091125062142289 3226009991318343796606717)
                    ·
                      refine ⟨1209753746744378923727519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3226009991318343796606717 1209753746744378923727519)
                      ·
                        rfl

theorem cell23_2355987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_2355987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2355987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2355987 prefixEnd_2355987 := by exact prefixLift 2355987
  have htrace : WordTrace (prefixWord ++ tailWord_2355987) baseStart_2355987 baseEnd_2355987 := by
    simpa [prefixWord, tailWord_2355987, baseEnd_2355987] using wordTrace_append hprefix tailTrace_2355987
  have hstable : (prefixWord ++ tailWord_2355987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355987).length < 2 ^ (prefixWord ++ tailWord_2355987).sum := by decide
  have hdescent : baseEnd_2355987 < baseStart_2355987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356001 : List Nat := [1, 2, 3, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_2356001 : Nat := 118140960795 + 2356001 * 2 ^ 59
def prefixEnd_2356001 : Nat := 4983230072969 + 3 ^ 40 * 2356001 * 2
def baseEnd_2356001 : Nat := 1209760935473541868952455

theorem tailTrace_2356001 : CollatzResearch.WordTrace tailWord_2356001 prefixEnd_2356001 1209760935473541868952455 := by
  unfold tailWord_2356001
  simp only [CollatzResearch.WordTrace]
  refine ⟨85930415937618224781363857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57286943958412149854242571 85930415937618224781363857)
  ·
    refine ⟨64447811953213668586022893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85930415937618224781363857 64447811953213668586022893)
    ·
      refine ⟨24167929482455125719758585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64447811953213668586022893 24167929482455125719758585)
      ·
        refine ⟨18125947111841344289818939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24167929482455125719758585 18125947111841344289818939)
        ·
          refine ⟨27188920667762016434728409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18125947111841344289818939 27188920667762016434728409)
          ·
            refine ⟨20391690500821512326046307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27188920667762016434728409 20391690500821512326046307)
            ·
              refine ⟨30587535751232268489069461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20391690500821512326046307 30587535751232268489069461)
              ·
                refine ⟨1433790738339012585425131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30587535751232268489069461 1433790738339012585425131)
                ·
                  refine ⟨2150686107508518878137697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433790738339012585425131 2150686107508518878137697)
                  ·
                    refine ⟨1613014580631389158603273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2150686107508518878137697 1613014580631389158603273)
                    ·
                      refine ⟨1209760935473541868952455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1613014580631389158603273 1209760935473541868952455)
                      ·
                        rfl

theorem cell23_2356001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_2356001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356001 prefixEnd_2356001 := by exact prefixLift 2356001
  have htrace : WordTrace (prefixWord ++ tailWord_2356001) baseStart_2356001 baseEnd_2356001 := by
    simpa [prefixWord, tailWord_2356001, baseEnd_2356001] using wordTrace_append hprefix tailTrace_2356001
  have hstable : (prefixWord ++ tailWord_2356001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356001).length < 2 ^ (prefixWord ++ tailWord_2356001).sum := by decide
  have hdescent : baseEnd_2356001 < baseStart_2356001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356014 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2356014 : Nat := 118140960795 + 2356014 * 2 ^ 59
def prefixEnd_2356014 : Nat := 4983230072969 + 3 ^ 40 * 2356014 * 2
def baseEnd_2356014 : Nat := 1209767610722050318089895

theorem tailTrace_2356014 : CollatzResearch.WordTrace tailWord_2356014 prefixEnd_2356014 1209767610722050318089895 := by
  unfold tailWord_2356014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10741361260821391000198387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57287260057714085334391397 10741361260821391000198387)
  ·
    refine ⟨16112041891232086500297581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10741361260821391000198387 16112041891232086500297581)
    ·
      refine ⟨6042015709212032437611593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16112041891232086500297581 6042015709212032437611593)
      ·
        refine ⟨4531511781909024328208695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6042015709212032437611593 4531511781909024328208695)
        ·
          refine ⟨6797267672863536492313043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531511781909024328208695 6797267672863536492313043)
          ·
            refine ⟨10195901509295304738469565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797267672863536492313043 10195901509295304738469565)
            ·
              refine ⟨3823463065985739276926087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10195901509295304738469565 3823463065985739276926087)
              ·
                refine ⟨5735194598978608915389131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823463065985739276926087 5735194598978608915389131)
                ·
                  refine ⟨8602791898467913373083697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5735194598978608915389131 8602791898467913373083697)
                  ·
                    refine ⟨6452093923850935029812773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8602791898467913373083697 6452093923850935029812773)
                    ·
                      refine ⟨1209767610722050318089895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6452093923850935029812773 1209767610722050318089895)
                      ·
                        rfl

theorem cell23_2356014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2356014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356014 prefixEnd_2356014 := by exact prefixLift 2356014
  have htrace : WordTrace (prefixWord ++ tailWord_2356014) baseStart_2356014 baseEnd_2356014 := by
    simpa [prefixWord, tailWord_2356014, baseEnd_2356014] using wordTrace_append hprefix tailTrace_2356014
  have hstable : (prefixWord ++ tailWord_2356014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356014).length < 2 ^ (prefixWord ++ tailWord_2356014).sum := by decide
  have hdescent : baseEnd_2356014 < baseStart_2356014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356068 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_2356068 : Nat := 118140960795 + 2356068 * 2 ^ 59
def prefixEnd_2356068 : Nat := 4983230072969 + 3 ^ 40 * 2356068 * 2
def baseEnd_2356068 : Nat := 1209795338677393106814647

theorem tailTrace_2356068 : CollatzResearch.WordTrace tailWord_2356068 prefixEnd_2356068 1209795338677393106814647 := by
  unfold tailWord_2356068
  simp only [CollatzResearch.WordTrace]
  refine ⟨42966429814187747612026429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57288573085583663482701905 42966429814187747612026429)
  ·
    refine ⟨16112411180320405354509911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42966429814187747612026429 16112411180320405354509911)
    ·
      refine ⟨24168616770480608031764867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16112411180320405354509911 24168616770480608031764867)
      ·
        refine ⟨36252925155720912047647301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24168616770480608031764867 36252925155720912047647301)
        ·
          refine ⟨6797423466697671008933869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36252925155720912047647301 6797423466697671008933869)
          ·
            refine ⟨2549033800011626628350201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6797423466697671008933869 2549033800011626628350201)
            ·
              refine ⟨1911775350008719971262651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549033800011626628350201 1911775350008719971262651)
              ·
                refine ⟨2867663025013079956893977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911775350008719971262651 2867663025013079956893977)
                ·
                  refine ⟨2150747268759809967670483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2867663025013079956893977 2150747268759809967670483)
                  ·
                    refine ⟨3226120903139714951505725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2150747268759809967670483 3226120903139714951505725)
                    ·
                      refine ⟨1209795338677393106814647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3226120903139714951505725 1209795338677393106814647)
                      ·
                        rfl

theorem cell23_2356068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_2356068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356068 prefixEnd_2356068 := by exact prefixLift 2356068
  have htrace : WordTrace (prefixWord ++ tailWord_2356068) baseStart_2356068 baseEnd_2356068 := by
    simpa [prefixWord, tailWord_2356068, baseEnd_2356068] using wordTrace_append hprefix tailTrace_2356068
  have hstable : (prefixWord ++ tailWord_2356068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356068).length < 2 ^ (prefixWord ++ tailWord_2356068).sum := by decide
  have hdescent : baseEnd_2356068 < baseStart_2356068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356080 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 7]
def baseStart_2356080 : Nat := 118140960795 + 2356080 * 2 ^ 59
def prefixEnd_2356080 : Nat := 4983230072969 + 3 ^ 40 * 2356080 * 2
def baseEnd_2356080 : Nat := 134422388938360784429399

theorem tailTrace_2356080 : CollatzResearch.WordTrace tailWord_2356080 prefixEnd_2356080 134422388938360784429399 := by
  unfold tailWord_2356080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42966648652166010636744847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57288864869554680848993129 42966648652166010636744847)
  ·
    refine ⟨64449972978249015955117271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42966648652166010636744847 64449972978249015955117271)
    ·
      refine ⟨96674959467373523932675907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64449972978249015955117271 96674959467373523932675907)
      ·
        refine ⟨145012439201060285899013861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96674959467373523932675907 145012439201060285899013861)
        ·
          refine ⟨27189832350198803606065099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145012439201060285899013861 27189832350198803606065099)
          ·
            refine ⟨40784748525298205409097649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27189832350198803606065099 40784748525298205409097649)
            ·
              refine ⟨30588561393973654056823237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40784748525298205409097649 30588561393973654056823237)
              ·
                refine ⟨5735355261370060135654357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30588561393973654056823237 5735355261370060135654357)
                ·
                  refine ⟨134422388938360784429399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5735355261370060135654357 134422388938360784429399)
                  ·
                    rfl

theorem cell23_2356080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_2356080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356080 prefixEnd_2356080 := by exact prefixLift 2356080
  have htrace : WordTrace (prefixWord ++ tailWord_2356080) baseStart_2356080 baseEnd_2356080 := by
    simpa [prefixWord, tailWord_2356080, baseEnd_2356080] using wordTrace_append hprefix tailTrace_2356080
  have hstable : (prefixWord ++ tailWord_2356080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356080).length < 2 ^ (prefixWord ++ tailWord_2356080).sum := by decide
  have hdescent : baseEnd_2356080 < baseStart_2356080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356140 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_2356140 : Nat := 118140960795 + 2356140 * 2 ^ 59
def prefixEnd_2356140 : Nat := 4983230072969 + 3 ^ 40 * 2356140 * 2
def baseEnd_2356140 : Nat := 403277436428172275038105

theorem tailTrace_2356140 : CollatzResearch.WordTrace tailWord_2356140 prefixEnd_2356140 403277436428172275038105 := by
  unfold tailWord_2356140
  simp only [CollatzResearch.WordTrace]
  refine ⟨42967742842057325760336937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57290323789409767680449249 42967742842057325760336937)
  ·
    refine ⟨32225807131542994320252703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42967742842057325760336937 32225807131542994320252703)
    ·
      refine ⟨48338710697314491480379055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32225807131542994320252703 48338710697314491480379055)
      ·
        refine ⟨72508066045971737220568583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48338710697314491480379055 72508066045971737220568583)
        ·
          refine ⟨108762099068957605830852875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72508066045971737220568583 108762099068957605830852875)
          ·
            refine ⟨163143148603436408746279313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108762099068957605830852875 163143148603436408746279313)
            ·
              refine ⟨122357361452577306559709485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163143148603436408746279313 122357361452577306559709485)
              ·
                refine ⟨45884010544716489959891057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122357361452577306559709485 45884010544716489959891057)
                ·
                  refine ⟨34413007908537367469918293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45884010544716489959891057 34413007908537367469918293)
                  ·
                    refine ⟨403277436428172275038105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34413007908537367469918293 403277436428172275038105)
                    ·
                      rfl

theorem cell23_2356140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_2356140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356140 prefixEnd_2356140 := by exact prefixLift 2356140
  have htrace : WordTrace (prefixWord ++ tailWord_2356140) baseStart_2356140 baseEnd_2356140 := by
    simpa [prefixWord, tailWord_2356140, baseEnd_2356140] using wordTrace_append hprefix tailTrace_2356140
  have hstable : (prefixWord ++ tailWord_2356140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356140).length < 2 ^ (prefixWord ++ tailWord_2356140).sum := by decide
  have hdescent : baseEnd_2356140 < baseStart_2356140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356147 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 4]
def baseStart_2356147 : Nat := 118140960795 + 2356147 * 2 ^ 59
def prefixEnd_2356147 : Nat := 4983230072969 + 3 ^ 40 * 2356147 * 2
def baseEnd_2356147 : Nat := 1209835903649098297726783

theorem tailTrace_2356147 : CollatzResearch.WordTrace tailWord_2356147 prefixEnd_2356147 1209835903649098297726783 := by
  unfold tailWord_2356147
  simp only [CollatzResearch.WordTrace]
  refine ⟨85935740995089291716178695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57290493996726194477452463 85935740995089291716178695)
  ·
    refine ⟨128903611492633937574268043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85935740995089291716178695 128903611492633937574268043)
    ·
      refine ⟨193355417238950906361402065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128903611492633937574268043 193355417238950906361402065)
      ·
        refine ⟨145016562929213179771051549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193355417238950906361402065 145016562929213179771051549)
        ·
          refine ⟨54381211098454942414144331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145016562929213179771051549 54381211098454942414144331)
          ·
            refine ⟨81571816647682413621216497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54381211098454942414144331 81571816647682413621216497)
            ·
              refine ⟨61178862485761810215912373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81571816647682413621216497 61178862485761810215912373)
              ·
                refine ⟨5735518358040169707741785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61178862485761810215912373 5735518358040169707741785)
                ·
                  refine ⟨4301638768530127280806339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5735518358040169707741785 4301638768530127280806339)
                  ·
                    refine ⟨6452458152795190921209509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4301638768530127280806339 6452458152795190921209509)
                    ·
                      refine ⟨1209835903649098297726783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6452458152795190921209509 1209835903649098297726783)
                      ·
                        rfl

theorem cell23_2356147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_2356147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356147 prefixEnd_2356147 := by exact prefixLift 2356147
  have htrace : WordTrace (prefixWord ++ tailWord_2356147) baseStart_2356147 baseEnd_2356147 := by
    simpa [prefixWord, tailWord_2356147, baseEnd_2356147] using wordTrace_append hprefix tailTrace_2356147
  have hstable : (prefixWord ++ tailWord_2356147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356147).length < 2 ^ (prefixWord ++ tailWord_2356147).sum := by decide
  have hdescent : baseEnd_2356147 < baseStart_2356147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356148 : List Nat := [2, 5, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2356148 : Nat := 118140960795 + 2356148 * 2 ^ 59
def prefixEnd_2356148 : Nat := 4983230072969 + 3 ^ 40 * 2356148 * 2
def baseEnd_2356148 : Nat := 134426268569972532646031

theorem tailTrace_2356148 : CollatzResearch.WordTrace tailWord_2356148 prefixEnd_2356148 134426268569972532646031 := by
  unfold tailWord_2356148
  simp only [CollatzResearch.WordTrace]
  refine ⟨42967888734042834443482549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57290518312057112591310065 42967888734042834443482549)
  ·
    refine ⟨4028239568816515729076489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42967888734042834443482549 4028239568816515729076489)
    ·
      refine ⟨3021179676612386796807367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4028239568816515729076489 3021179676612386796807367)
      ·
        refine ⟨4531769514918580195211051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021179676612386796807367 4531769514918580195211051)
        ·
          refine ⟨6797654272377870292816577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531769514918580195211051 6797654272377870292816577)
          ·
            refine ⟨5098240704283402719612433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6797654272377870292816577 5098240704283402719612433)
            ·
              refine ⟨3823680528212552039709325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098240704283402719612433 3823680528212552039709325)
              ·
                refine ⟨1433880198079707014890997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3823680528212552039709325 1433880198079707014890997)
                ·
                  refine ⟨134426268569972532646031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1433880198079707014890997 134426268569972532646031)
                  ·
                    rfl

theorem cell23_2356148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2356148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356148 prefixEnd_2356148 := by exact prefixLift 2356148
  have htrace : WordTrace (prefixWord ++ tailWord_2356148) baseStart_2356148 baseEnd_2356148 := by
    simpa [prefixWord, tailWord_2356148, baseEnd_2356148] using wordTrace_append hprefix tailTrace_2356148
  have hstable : (prefixWord ++ tailWord_2356148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356148).length < 2 ^ (prefixWord ++ tailWord_2356148).sum := by decide
  have hdescent : baseEnd_2356148 < baseStart_2356148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356174 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_2356174 : Nat := 118140960795 + 2356174 * 2 ^ 59
def prefixEnd_2356174 : Nat := 4983230072969 + 3 ^ 40 * 2356174 * 2
def baseEnd_2356174 : Nat := 403283255875589897363053

theorem tailTrace_2356174 : CollatzResearch.WordTrace tailWord_2356174 prefixEnd_2356174 403283255875589897363053 := by
  unfold tailWord_2356174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742090720748934415926447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57291150510660983551607717 10742090720748934415926447)
  ·
    refine ⟨16113136081123401623889671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10742090720748934415926447 16113136081123401623889671)
    ·
      refine ⟨24169704121685102435834507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16113136081123401623889671 24169704121685102435834507)
      ·
        refine ⟨36254556182527653653751761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24169704121685102435834507 36254556182527653653751761)
        ·
          refine ⟨27190917136895740240313821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36254556182527653653751761 27190917136895740240313821)
          ·
            refine ⟨10196593926335902590117683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27190917136895740240313821 10196593926335902590117683)
            ·
              refine ⟨15294890889503853885176525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10196593926335902590117683 15294890889503853885176525)
              ·
                refine ⟨5735584083563945206941197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15294890889503853885176525 5735584083563945206941197)
                ·
                  refine ⟨2150844031336479452602949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5735584083563945206941197 2150844031336479452602949)
                  ·
                    refine ⟨403283255875589897363053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2150844031336479452602949 403283255875589897363053)
                    ·
                      rfl

theorem cell23_2356174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_2356174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356174 prefixEnd_2356174 := by exact prefixLift 2356174
  have htrace : WordTrace (prefixWord ++ tailWord_2356174) baseStart_2356174 baseEnd_2356174 := by
    simpa [prefixWord, tailWord_2356174, baseEnd_2356174] using wordTrace_append hprefix tailTrace_2356174
  have hstable : (prefixWord ++ tailWord_2356174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356174).length < 2 ^ (prefixWord ++ tailWord_2356174).sum := by decide
  have hdescent : baseEnd_2356174 < baseStart_2356174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356258 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_2356258 : Nat := 118140960795 + 2356258 * 2 ^ 59
def prefixEnd_2356258 : Nat := 4983230072969 + 3 ^ 40 * 2356258 * 2
def baseEnd_2356258 : Nat := 1209892900001747363438773

theorem tailTrace_2356258 : CollatzResearch.WordTrace tailWord_2356258 prefixEnd_2356258 1209892900001747363438773 := by
  unfold tailWord_2356258
  simp only [CollatzResearch.WordTrace]
  refine ⟨21484947374421789418367357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57293192998458105115646285 21484947374421789418367357)
  ·
    refine ⟨8056855265408171031887759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21484947374421789418367357 8056855265408171031887759)
    ·
      refine ⟨12085282898112256547831639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8056855265408171031887759 12085282898112256547831639)
      ·
        refine ⟨18127924347168384821747459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12085282898112256547831639 18127924347168384821747459)
        ·
          refine ⟨27191886520752577232621189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18127924347168384821747459 27191886520752577232621189)
          ·
            refine ⟨5098478722641108231116473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27191886520752577232621189 5098478722641108231116473)
            ·
              refine ⟨3823859041980831173337355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098478722641108231116473 3823859041980831173337355)
              ·
                refine ⟨5735788562971246760006033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823859041980831173337355 5735788562971246760006033)
                ·
                  refine ⟨4301841422228435070004525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5735788562971246760006033 4301841422228435070004525)
                  ·
                    refine ⟨1613190533335663151251697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4301841422228435070004525 1613190533335663151251697)
                    ·
                      refine ⟨1209892900001747363438773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1613190533335663151251697 1209892900001747363438773)
                      ·
                        rfl

theorem cell23_2356258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_2356258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356258 prefixEnd_2356258 := by exact prefixLift 2356258
  have htrace : WordTrace (prefixWord ++ tailWord_2356258) baseStart_2356258 baseEnd_2356258 := by
    simpa [prefixWord, tailWord_2356258, baseEnd_2356258] using wordTrace_append hprefix tailTrace_2356258
  have hstable : (prefixWord ++ tailWord_2356258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356258).length < 2 ^ (prefixWord ++ tailWord_2356258).sum := by decide
  have hdescent : baseEnd_2356258 < baseStart_2356258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356281 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 2, 4]
def baseStart_2356281 : Nat := 118140960795 + 2356281 * 2 ^ 59
def prefixEnd_2356281 : Nat := 4983230072969 + 3 ^ 40 * 2356281 * 2
def baseEnd_2356281 : Nat := 403301570018933591150389

theorem tailTrace_2356281 : CollatzResearch.WordTrace tailWord_2356281 prefixEnd_2356281 403301570018933591150389 := by
  unfold tailWord_2356281
  simp only [CollatzResearch.WordTrace]
  refine ⟨85940628376603832601556697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57293752251069221734371131 85940628376603832601556697)
  ·
    refine ⟨64455471282452874451167523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85940628376603832601556697 64455471282452874451167523)
    ·
      refine ⟨96683206923679311676751285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64455471282452874451167523 96683206923679311676751285)
      ·
        refine ⟨9064050649094935469695433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96683206923679311676751285 9064050649094935469695433)
        ·
          refine ⟨6798037986821201602271575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9064050649094935469695433 6798037986821201602271575)
          ·
            refine ⟨10197056980231802403407363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6798037986821201602271575 10197056980231802403407363)
            ·
              refine ⟨15295585470347703605111045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10197056980231802403407363 15295585470347703605111045)
              ·
                refine ⟨2867922275690194425958321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15295585470347703605111045 2867922275690194425958321)
                ·
                  refine ⟨2150941706767645819468741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2867922275690194425958321 2150941706767645819468741)
                  ·
                    refine ⟨403301570018933591150389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2150941706767645819468741 403301570018933591150389)
                    ·
                      rfl

theorem cell23_2356281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_2356281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356281 prefixEnd_2356281 := by exact prefixLift 2356281
  have htrace : WordTrace (prefixWord ++ tailWord_2356281) baseStart_2356281 baseEnd_2356281 := by
    simpa [prefixWord, tailWord_2356281, baseEnd_2356281] using wordTrace_append hprefix tailTrace_2356281
  have hstable : (prefixWord ++ tailWord_2356281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356281).length < 2 ^ (prefixWord ++ tailWord_2356281).sum := by decide
  have hdescent : baseEnd_2356281 < baseStart_2356281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356301 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2356301 : Nat := 118140960795 + 2356301 * 2 ^ 59
def prefixEnd_2356301 : Nat := 4983230072969 + 3 ^ 40 * 2356301 * 2
def baseEnd_2356301 : Nat := 1209914979669890695201075

theorem tailTrace_2356301 : CollatzResearch.WordTrace tailWord_2356301 prefixEnd_2356301 1209914979669890695201075 := by
  unfold tailWord_2356301
  simp only [CollatzResearch.WordTrace]
  refine ⟨85941357836531376017284757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57294238557687584011523171 85941357836531376017284757)
  ·
    refine ⟨4028501148587408250810223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85941357836531376017284757 4028501148587408250810223)
    ·
      refine ⟨6042751722881112376215335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4028501148587408250810223 6042751722881112376215335)
      ·
        refine ⟨9064127584321668564323003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042751722881112376215335 9064127584321668564323003)
        ·
          refine ⟨13596191376482502846484505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9064127584321668564323003 13596191376482502846484505)
          ·
            refine ⟨10197143532361877134863379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13596191376482502846484505 10197143532361877134863379)
            ·
              refine ⟨15295715298542815702295069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10197143532361877134863379 15295715298542815702295069)
              ·
                refine ⟨5735893236953555888360651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15295715298542815702295069 5735893236953555888360651)
                ·
                  refine ⟨8603839855430333832540977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5735893236953555888360651 8603839855430333832540977)
                  ·
                    refine ⟨6452879891572750374405733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8603839855430333832540977 6452879891572750374405733)
                    ·
                      refine ⟨1209914979669890695201075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6452879891572750374405733 1209914979669890695201075)
                      ·
                        rfl

theorem cell23_2356301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2356301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356301 prefixEnd_2356301 := by exact prefixLift 2356301
  have htrace : WordTrace (prefixWord ++ tailWord_2356301) baseStart_2356301 baseEnd_2356301 := by
    simpa [prefixWord, tailWord_2356301, baseEnd_2356301] using wordTrace_append hprefix tailTrace_2356301
  have hstable : (prefixWord ++ tailWord_2356301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356301).length < 2 ^ (prefixWord ++ tailWord_2356301).sum := by decide
  have hdescent : baseEnd_2356301 < baseStart_2356301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356322 : List Nat := [3, 3, 2, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2356322 : Nat := 118140960795 + 2356322 * 2 ^ 59
def prefixEnd_2356322 : Nat := 4983230072969 + 3 ^ 40 * 2356322 * 2
def baseEnd_2356322 : Nat := 1209925762763635113038479

theorem tailTrace_2356322 : CollatzResearch.WordTrace tailWord_2356322 prefixEnd_2356322 1209925762763635113038479 := by
  unfold tailWord_2356322
  simp only [CollatzResearch.WordTrace]
  refine ⟨21485530942363824150949805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57294749179636864402532813 21485530942363824150949805)
  ·
    refine ⟨8057074103386434056606177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21485530942363824150949805 8057074103386434056606177)
    ·
      refine ⟨6042805577539825542454633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8057074103386434056606177 6042805577539825542454633)
      ·
        refine ⟨4532104183154869156840975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6042805577539825542454633 4532104183154869156840975)
        ·
          refine ⟨6798156274732303735261463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532104183154869156840975 6798156274732303735261463)
          ·
            refine ⟨10197234412098455602892195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6798156274732303735261463 10197234412098455602892195)
            ·
              refine ⟨15295851618147683404338293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10197234412098455602892195 15295851618147683404338293)
              ·
                refine ⟨1433986089201345319156715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15295851618147683404338293 1433986089201345319156715)
                ·
                  refine ⟨2150979133802017978735073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433986089201345319156715 2150979133802017978735073)
                  ·
                    refine ⟨1613234350351513484051305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2150979133802017978735073 1613234350351513484051305)
                    ·
                      refine ⟨1209925762763635113038479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1613234350351513484051305 1209925762763635113038479)
                      ·
                        rfl

theorem cell23_2356322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2356322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356322 prefixEnd_2356322 := by exact prefixLift 2356322
  have htrace : WordTrace (prefixWord ++ tailWord_2356322) baseStart_2356322 baseEnd_2356322 := by
    simpa [prefixWord, tailWord_2356322, baseEnd_2356322] using wordTrace_append hprefix tailTrace_2356322
  have hstable : (prefixWord ++ tailWord_2356322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356322).length < 2 ^ (prefixWord ++ tailWord_2356322).sum := by decide
  have hdescent : baseEnd_2356322 < baseStart_2356322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356364 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2356364 : Nat := 118140960795 + 2356364 * 2 ^ 59
def prefixEnd_2356364 : Nat := 4983230072969 + 3 ^ 40 * 2356364 * 2
def baseEnd_2356364 : Nat := 1209947328951123948713285

theorem tailTrace_2356364 : CollatzResearch.WordTrace tailWord_2356364 prefixEnd_2356364 1209947328951123948713285 := by
  unfold tailWord_2356364
  simp only [CollatzResearch.WordTrace]
  refine ⟨42971827817651568888414073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57295770423535425184552097 42971827817651568888414073)
  ·
    refine ⟨32228870863238676666310555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42971827817651568888414073 32228870863238676666310555)
    ·
      refine ⟨48343306294858014999465833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32228870863238676666310555 48343306294858014999465833)
      ·
        refine ⟨36257479721143511249599375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48343306294858014999465833 36257479721143511249599375)
        ·
          refine ⟨54386219581715266874399063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36257479721143511249599375 54386219581715266874399063)
          ·
            refine ⟨81579329372572900311598595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54386219581715266874399063 81579329372572900311598595)
            ·
              refine ⟨122368994058859350467397893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81579329372572900311598595 122368994058859350467397893)
              ·
                refine ⟨22944186386036128212637105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122368994058859350467397893 22944186386036128212637105)
                ·
                  refine ⟨17208139789527096159477829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22944186386036128212637105 17208139789527096159477829)
                  ·
                    refine ⟨3226526210536330529902093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17208139789527096159477829 3226526210536330529902093)
                    ·
                      refine ⟨1209947328951123948713285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3226526210536330529902093 1209947328951123948713285)
                      ·
                        rfl

theorem cell23_2356364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2356364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356364 prefixEnd_2356364 := by exact prefixLift 2356364
  have htrace : WordTrace (prefixWord ++ tailWord_2356364) baseStart_2356364 baseEnd_2356364 := by
    simpa [prefixWord, tailWord_2356364, baseEnd_2356364] using wordTrace_append hprefix tailTrace_2356364
  have hstable : (prefixWord ++ tailWord_2356364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356364).length < 2 ^ (prefixWord ++ tailWord_2356364).sum := by decide
  have hdescent : baseEnd_2356364 < baseStart_2356364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356367 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 13]
def baseStart_2356367 : Nat := 118140960795 + 2356367 * 2 ^ 59
def prefixEnd_2356367 : Nat := 4983230072969 + 3 ^ 40 * 2356367 * 2
def baseEnd_2356367 : Nat := 134438763265898604108419

theorem tailTrace_2356367 : CollatzResearch.WordTrace tailWord_2356367 prefixEnd_2356367 134438763265898604108419 := by
  unfold tailWord_2356367
  simp only [CollatzResearch.WordTrace]
  refine ⟨85943765054292269289187355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57295843369528179526124903 85943765054292269289187355)
  ·
    refine ⟨128915647581438403933781033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85943765054292269289187355 128915647581438403933781033)
    ·
      refine ⟨96686735686078802950335775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128915647581438403933781033 96686735686078802950335775)
      ·
        refine ⟨145030103529118204425503663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96686735686078802950335775 145030103529118204425503663)
        ·
          refine ⟨217545155293677306638255495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145030103529118204425503663 217545155293677306638255495)
          ·
            refine ⟨326317732940515959957383243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217545155293677306638255495 326317732940515959957383243)
            ·
              refine ⟨489476599410773939936074865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326317732940515959957383243 489476599410773939936074865)
              ·
                refine ⟨367107449558080454952056149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489476599410773939936074865 367107449558080454952056149)
                ·
                  refine ⟨134438763265898604108419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 367107449558080454952056149 134438763265898604108419)
                  ·
                    rfl

theorem cell23_2356367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 13].length) (baseStart_2356367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356367 prefixEnd_2356367 := by exact prefixLift 2356367
  have htrace : WordTrace (prefixWord ++ tailWord_2356367) baseStart_2356367 baseEnd_2356367 := by
    simpa [prefixWord, tailWord_2356367, baseEnd_2356367] using wordTrace_append hprefix tailTrace_2356367
  have hstable : (prefixWord ++ tailWord_2356367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356367).length < 2 ^ (prefixWord ++ tailWord_2356367).sum := by decide
  have hdescent : baseEnd_2356367 < baseStart_2356367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356401 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 7]
def baseStart_2356401 : Nat := 118140960795 + 2356401 * 2 ^ 59
def prefixEnd_2356401 : Nat := 4983230072969 + 3 ^ 40 * 2356401 * 2
def baseEnd_2356401 : Nat := 134440703081704478216735

theorem tailTrace_2356401 : CollatzResearch.WordTrace tailWord_2356401 prefixEnd_2356401 134440703081704478216735 := by
  unfold tailWord_2356401
  simp only [CollatzResearch.WordTrace]
  refine ⟨85945005136169093095925057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57296670090779395397283371 85945005136169093095925057)
  ·
    refine ⟨64458753852126819821943793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85945005136169093095925057 64458753852126819821943793)
    ·
      refine ⟨48344065389095114866457845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64458753852126819821943793 48344065389095114866457845)
      ·
        refine ⟨4532256130227667018730423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48344065389095114866457845 4532256130227667018730423)
        ·
          refine ⟨6798384195341500528095635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532256130227667018730423 6798384195341500528095635)
          ·
            refine ⟨10197576293012250792143453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6798384195341500528095635 10197576293012250792143453)
            ·
              refine ⟨3824091109879594047053795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10197576293012250792143453 3824091109879594047053795)
              ·
                refine ⟨5736136664819391070580693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824091109879594047053795 5736136664819391070580693)
                ·
                  refine ⟨134440703081704478216735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5736136664819391070580693 134440703081704478216735)
                  ·
                    rfl

theorem cell23_2356401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 7].length) (baseStart_2356401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356401 prefixEnd_2356401 := by exact prefixLift 2356401
  have htrace : WordTrace (prefixWord ++ tailWord_2356401) baseStart_2356401 baseEnd_2356401 := by
    simpa [prefixWord, tailWord_2356401, baseEnd_2356401] using wordTrace_append hprefix tailTrace_2356401
  have hstable : (prefixWord ++ tailWord_2356401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356401).length < 2 ^ (prefixWord ++ tailWord_2356401).sum := by decide
  have hdescent : baseEnd_2356401 < baseStart_2356401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356406 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2356406 : Nat := 118140960795 + 2356406 * 2 ^ 59
def prefixEnd_2356406 : Nat := 4983230072969 + 3 ^ 40 * 2356406 * 2
def baseEnd_2356406 : Nat := 1209968895138612784388093

theorem tailTrace_2356406 : CollatzResearch.WordTrace tailWord_2356406 prefixEnd_2356406 1209968895138612784388093 := by
  unfold tailWord_2356406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371574218821936184366067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57296791667433985966571381 5371574218821936184366067)
  ·
    refine ⟨8057361328232904276549101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5371574218821936184366067 8057361328232904276549101)
    ·
      refine ⟨3021510498087339103705913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8057361328232904276549101 3021510498087339103705913)
      ·
        refine ⟨2266132873565504327779435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3021510498087339103705913 2266132873565504327779435)
        ·
          refine ⟨3399199310348256491669153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266132873565504327779435 3399199310348256491669153)
          ·
            refine ⟨2549399482761192368751865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3399199310348256491669153 2549399482761192368751865)
            ·
              refine ⟨1912049612070894276563899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549399482761192368751865 1912049612070894276563899)
              ·
                refine ⟨2868074418106341414845849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912049612070894276563899 2868074418106341414845849)
                ·
                  refine ⟨2151055813579756061134387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868074418106341414845849 2151055813579756061134387)
                  ·
                    refine ⟨3226583720369634091701581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2151055813579756061134387 3226583720369634091701581)
                    ·
                      refine ⟨1209968895138612784388093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3226583720369634091701581 1209968895138612784388093)
                      ·
                        rfl

theorem cell23_2356406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2356406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356406 prefixEnd_2356406 := by exact prefixLift 2356406
  have htrace : WordTrace (prefixWord ++ tailWord_2356406) baseStart_2356406 baseEnd_2356406 := by
    simpa [prefixWord, tailWord_2356406, baseEnd_2356406] using wordTrace_append hprefix tailTrace_2356406
  have hstable : (prefixWord ++ tailWord_2356406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356406).length < 2 ^ (prefixWord ++ tailWord_2356406).sum := by decide
  have hdescent : baseEnd_2356406 < baseStart_2356406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356412 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_2356412 : Nat := 118140960795 + 2356412 * 2 ^ 59
def prefixEnd_2356412 : Nat := 4983230072969 + 3 ^ 40 * 2356412 * 2
def baseEnd_2356412 : Nat := 1209971976022539760913065

theorem tailTrace_2356412 : CollatzResearch.WordTrace tailWord_2356412 prefixEnd_2356412 1209971976022539760913065 := by
  unfold tailWord_2356412
  simp only [CollatzResearch.WordTrace]
  refine ⟨42972703169564620987287745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57296937559419494649716993 42972703169564620987287745)
  ·
    refine ⟨32229527377173465740465809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42972703169564620987287745 32229527377173465740465809)
    ·
      refine ⟨24172145532880099305349357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32229527377173465740465809 24172145532880099305349357)
      ·
        refine ⟨9064554574830037239506009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24172145532880099305349357 9064554574830037239506009)
        ·
          refine ⟨6798415931122527929629507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9064554574830037239506009 6798415931122527929629507)
          ·
            refine ⟨10197623896683791894444261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6798415931122527929629507 10197623896683791894444261)
            ·
              refine ⟨1912054480628210980208299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10197623896683791894444261 1912054480628210980208299)
              ·
                refine ⟨2868081720942316470312449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912054480628210980208299 2868081720942316470312449)
                ·
                  refine ⟨2151061290706737352734337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868081720942316470312449 2151061290706737352734337)
                  ·
                    refine ⟨1613295968030053014550753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2151061290706737352734337 1613295968030053014550753)
                    ·
                      refine ⟨1209971976022539760913065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1613295968030053014550753 1209971976022539760913065)
                      ·
                        rfl

theorem cell23_2356412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_2356412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356412 prefixEnd_2356412 := by exact prefixLift 2356412
  have htrace : WordTrace (prefixWord ++ tailWord_2356412) baseStart_2356412 baseEnd_2356412 := by
    simpa [prefixWord, tailWord_2356412, baseEnd_2356412] using wordTrace_append hprefix tailTrace_2356412
  have hstable : (prefixWord ++ tailWord_2356412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356412).length < 2 ^ (prefixWord ++ tailWord_2356412).sum := by decide
  have hdescent : baseEnd_2356412 < baseStart_2356412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356464 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_2356464 : Nat := 118140960795 + 2356464 * 2 ^ 59
def prefixEnd_2356464 : Nat := 4983230072969 + 3 ^ 40 * 2356464 * 2
def baseEnd_2356464 : Nat := 1209998677016573557462825

theorem tailTrace_2356464 : CollatzResearch.WordTrace tailWord_2356464 prefixEnd_2356464 1209998677016573557462825 := by
  unfold tailWord_2356464
  simp only [CollatzResearch.WordTrace]
  refine ⟨42973651467470427427734223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57298201956627236570312297 42973651467470427427734223)
  ·
    refine ⟨64460477201205641141601335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42973651467470427427734223 64460477201205641141601335)
    ·
      refine ⟨96690715801808461712402003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64460477201205641141601335 96690715801808461712402003)
      ·
        refine ⟨145036073702712692568603005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96690715801808461712402003 145036073702712692568603005)
        ·
          refine ⟨54388527638517259713226127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145036073702712692568603005 54388527638517259713226127)
          ·
            refine ⟨81582791457775889569839191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54388527638517259713226127 81582791457775889569839191)
            ·
              refine ⟨122374187186663834354758787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81582791457775889569839191 122374187186663834354758787)
              ·
                refine ⟨183561280779995751532138181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122374187186663834354758787 183561280779995751532138181)
                ·
                  refine ⟨34417740146249203412275909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183561280779995751532138181 34417740146249203412275909)
                  ·
                    refine ⟨6453326277421725639801733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34417740146249203412275909 6453326277421725639801733)
                    ·
                      refine ⟨1209998677016573557462825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6453326277421725639801733 1209998677016573557462825)
                      ·
                        rfl

theorem cell23_2356464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_2356464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356464 prefixEnd_2356464 := by exact prefixLift 2356464
  have htrace : WordTrace (prefixWord ++ tailWord_2356464) baseStart_2356464 baseEnd_2356464 := by
    simpa [prefixWord, tailWord_2356464, baseEnd_2356464] using wordTrace_append hprefix tailTrace_2356464
  have hstable : (prefixWord ++ tailWord_2356464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356464).length < 2 ^ (prefixWord ++ tailWord_2356464).sum := by decide
  have hdescent : baseEnd_2356464 < baseStart_2356464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356478 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2356478 : Nat := 118140960795 + 2356478 * 2 ^ 59
def prefixEnd_2356478 : Nat := 4983230072969 + 3 ^ 40 * 2356478 * 2
def baseEnd_2356478 : Nat := 403335288581912167562587

theorem tailTrace_2356478 : CollatzResearch.WordTrace tailWord_2356478 prefixEnd_2356478 403335288581912167562587 := by
  unfold tailWord_2356478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10743476694611266905809761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57298542371260090164318725 10743476694611266905809761)
  ·
    refine ⟨8057607520958450179357321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10743476694611266905809761 8057607520958450179357321)
    ·
      refine ⟨6043205640718837634517991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8057607520958450179357321 6043205640718837634517991)
      ·
        refine ⟨9064808461078256451776987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6043205640718837634517991 9064808461078256451776987)
        ·
          refine ⟨13597212691617384677665481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9064808461078256451776987 13597212691617384677665481)
          ·
            refine ⟨10197909518713038508249111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13597212691617384677665481 10197909518713038508249111)
            ·
              refine ⟨15296864278069557762373667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10197909518713038508249111 15296864278069557762373667)
              ·
                refine ⟨22945296417104336643560501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15296864278069557762373667 22945296417104336643560501)
                ·
                  refine ⟨2151121539103531560333797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22945296417104336643560501 2151121539103531560333797)
                  ·
                    refine ⟨403335288581912167562587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151121539103531560333797 403335288581912167562587)
                    ·
                      rfl

theorem cell23_2356478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2356478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356478 prefixEnd_2356478 := by exact prefixLift 2356478
  have htrace : WordTrace (prefixWord ++ tailWord_2356478) baseStart_2356478 baseEnd_2356478 := by
    simpa [prefixWord, tailWord_2356478, baseEnd_2356478] using wordTrace_append hprefix tailTrace_2356478
  have hstable : (prefixWord ++ tailWord_2356478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356478).length < 2 ^ (prefixWord ++ tailWord_2356478).sum := by decide
  have hdescent : baseEnd_2356478 < baseStart_2356478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356482 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2356482 : Nat := 118140960795 + 2356482 * 2 ^ 59
def prefixEnd_2356482 : Nat := 4983230072969 + 3 ^ 40 * 2356482 * 2
def baseEnd_2356482 : Nat := 403335973222784829012581

theorem tailTrace_2356482 : CollatzResearch.WordTrace tailWord_2356482 prefixEnd_2356482 403335973222784829012581 := by
  unfold tailWord_2356482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21486989862218910982405925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57298639632583762619749133 21486989862218910982405925)
  ·
    refine ⟨4028810599166045809201111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21486989862218910982405925 4028810599166045809201111)
    ·
      refine ⟨6043215898749068713801667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4028810599166045809201111 6043215898749068713801667)
      ·
        refine ⟨9064823848123603070702501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6043215898749068713801667 9064823848123603070702501)
        ·
          refine ⟨1699654471523175575756719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9064823848123603070702501 1699654471523175575756719)
          ·
            refine ⟨2549481707284763363635079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699654471523175575756719 2549481707284763363635079)
            ·
              refine ⟨3824222560927145045452619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549481707284763363635079 3824222560927145045452619)
              ·
                refine ⟨5736333841390717568178929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824222560927145045452619 5736333841390717568178929)
                ·
                  refine ⟨4302250381043038176134197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5736333841390717568178929 4302250381043038176134197)
                  ·
                    refine ⟨403335973222784829012581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4302250381043038176134197 403335973222784829012581)
                    ·
                      rfl

theorem cell23_2356482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2356482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356482 prefixEnd_2356482 := by exact prefixLift 2356482
  have htrace : WordTrace (prefixWord ++ tailWord_2356482) baseStart_2356482 baseEnd_2356482 := by
    simpa [prefixWord, tailWord_2356482, baseEnd_2356482] using wordTrace_append hprefix tailTrace_2356482
  have hstable : (prefixWord ++ tailWord_2356482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356482).length < 2 ^ (prefixWord ++ tailWord_2356482).sum := by decide
  have hdescent : baseEnd_2356482 < baseStart_2356482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356488 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_2356488 : Nat := 118140960795 + 2356488 * 2 ^ 59
def prefixEnd_2356488 : Nat := 4983230072969 + 3 ^ 40 * 2356488 * 2
def baseEnd_2356488 : Nat := 1210011000552281463562715

theorem tailTrace_2356488 : CollatzResearch.WordTrace tailWord_2356488 prefixEnd_2356488 1210011000552281463562715 := by
  unfold tailWord_2356488
  simp only [CollatzResearch.WordTrace]
  refine ⟨42974089143426953477171059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57298785524569271302894745 42974089143426953477171059)
  ·
    refine ⟨64461133715140430215756589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42974089143426953477171059 64461133715140430215756589)
    ·
      refine ⟨24172925143177661330908721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64461133715140430215756589 24172925143177661330908721)
      ·
        refine ⟨18129693857383245998181541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24172925143177661330908721 18129693857383245998181541)
        ·
          refine ⟨3399317598259358624659039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18129693857383245998181541 3399317598259358624659039)
          ·
            refine ⟨5098976397389037936988559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399317598259358624659039 5098976397389037936988559)
            ·
              refine ⟨7648464596083556905482839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5098976397389037936988559 7648464596083556905482839)
              ·
                refine ⟨11472696894125335358224259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648464596083556905482839 11472696894125335358224259)
                ·
                  refine ⟨17209045341188003037336389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11472696894125335358224259 17209045341188003037336389)
                  ·
                    refine ⟨3226696001472750569500573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17209045341188003037336389 3226696001472750569500573)
                    ·
                      refine ⟨1210011000552281463562715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3226696001472750569500573 1210011000552281463562715)
                      ·
                        rfl

theorem cell23_2356488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_2356488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356488 prefixEnd_2356488 := by exact prefixLift 2356488
  have htrace : WordTrace (prefixWord ++ tailWord_2356488) baseStart_2356488 baseEnd_2356488 := by
    simpa [prefixWord, tailWord_2356488, baseEnd_2356488] using wordTrace_append hprefix tailTrace_2356488
  have hstable : (prefixWord ++ tailWord_2356488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356488).length < 2 ^ (prefixWord ++ tailWord_2356488).sum := by decide
  have hdescent : baseEnd_2356488 < baseStart_2356488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356538 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_2356538 : Nat := 118140960795 + 2356538 * 2 ^ 59
def prefixEnd_2356538 : Nat := 4983230072969 + 3 ^ 40 * 2356538 * 2
def baseEnd_2356538 : Nat := 403345558195002089312495

theorem tailTrace_2356538 : CollatzResearch.WordTrace tailWord_2356538 prefixEnd_2356538 403345558195002089312495 := by
  unfold tailWord_2356538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21487500484168191373415567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57300001291115176995774845 21487500484168191373415567)
  ·
    refine ⟨32231250726252287060123351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21487500484168191373415567 32231250726252287060123351)
    ·
      refine ⟨48346876089378430590185027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32231250726252287060123351 48346876089378430590185027)
      ·
        refine ⟨72520314134067645885277541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48346876089378430590185027 72520314134067645885277541)
        ·
          refine ⟨13597558900137683603489539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72520314134067645885277541 13597558900137683603489539)
          ·
            refine ⟨20396338350206525405234309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13597558900137683603489539 20396338350206525405234309)
            ·
              refine ⟨3824313440663723513481433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20396338350206525405234309 3824313440663723513481433)
              ·
                refine ⟨2868235080497792635111075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3824313440663723513481433 2868235080497792635111075)
                ·
                  refine ⟨4302352620746688952666613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868235080497792635111075 4302352620746688952666613)
                  ·
                    refine ⟨403345558195002089312495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4302352620746688952666613 403345558195002089312495)
                    ·
                      rfl

theorem cell23_2356538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_2356538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356538 prefixEnd_2356538 := by exact prefixLift 2356538
  have htrace : WordTrace (prefixWord ++ tailWord_2356538) baseStart_2356538 baseEnd_2356538 := by
    simpa [prefixWord, tailWord_2356538, baseEnd_2356538] using wordTrace_append hprefix tailTrace_2356538
  have hstable : (prefixWord ++ tailWord_2356538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356538).length < 2 ^ (prefixWord ++ tailWord_2356538).sum := by decide
  have hdescent : baseEnd_2356538 < baseStart_2356538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356545 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2356545 : Nat := 118140960795 + 2356545 * 2 ^ 59
def prefixEnd_2356545 : Nat := 4983230072969 + 3 ^ 40 * 2356545 * 2
def baseEnd_2356545 : Nat := 1210040268949587740549953

theorem tailTrace_2356545 : CollatzResearch.WordTrace tailWord_2356545 prefixEnd_2356545 1210040268949587740549953 := by
  unfold tailWord_2356545
  simp only [CollatzResearch.WordTrace]
  refine ⟨85950257247647405689167089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57300171498431603792778059 85950257247647405689167089)
  ·
    refine ⟨64462692935735554266875317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85950257247647405689167089 64462692935735554266875317)
    ·
      refine ⟨6043377462725208212519561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64462692935735554266875317 6043377462725208212519561)
      ·
        refine ⟨4532533097043906159389671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6043377462725208212519561 4532533097043906159389671)
        ·
          refine ⟨6798799645565859239084507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532533097043906159389671 6798799645565859239084507)
          ·
            refine ⟨10198199468348788858626761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6798799645565859239084507 10198199468348788858626761)
            ·
              refine ⟨7648649601261591643970071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10198199468348788858626761 7648649601261591643970071)
              ·
                refine ⟨11472974401892387465955107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648649601261591643970071 11472974401892387465955107)
                ·
                  refine ⟨17209461602838581198932661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11472974401892387465955107 17209461602838581198932661)
                  ·
                    refine ⟨1613387025266116987399937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17209461602838581198932661 1613387025266116987399937)
                    ·
                      refine ⟨1210040268949587740549953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1613387025266116987399937 1210040268949587740549953)
                      ·
                        rfl

theorem cell23_2356545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2356545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356545 prefixEnd_2356545 := by exact prefixLift 2356545
  have htrace : WordTrace (prefixWord ++ tailWord_2356545) baseStart_2356545 baseEnd_2356545 := by
    simpa [prefixWord, tailWord_2356545, baseEnd_2356545] using wordTrace_append hprefix tailTrace_2356545
  have hstable : (prefixWord ++ tailWord_2356545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356545).length < 2 ^ (prefixWord ++ tailWord_2356545).sum := by decide
  have hdescent : baseEnd_2356545 < baseStart_2356545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356558 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_2356558 : Nat := 118140960795 + 2356558 * 2 ^ 59
def prefixEnd_2356558 : Nat := 4983230072969 + 3 ^ 40 * 2356558 * 2
def baseEnd_2356558 : Nat := 1210046944198096189687393

theorem tailTrace_2356558 : CollatzResearch.WordTrace tailWord_2356558 prefixEnd_2356558 1210046944198096189687393 := by
  unfold tailWord_2356558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10743841424575038613673791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57300487597733539272926885 10743841424575038613673791)
  ·
    refine ⟨16115762136862557920510687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10743841424575038613673791 16115762136862557920510687)
    ·
      refine ⟨24173643205293836880766031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16115762136862557920510687 24173643205293836880766031)
      ·
        refine ⟨36260464807940755321149047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24173643205293836880766031 36260464807940755321149047)
        ·
          refine ⟨54390697211911132981723571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36260464807940755321149047 54390697211911132981723571)
          ·
            refine ⟨81586045817866699472585357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54390697211911132981723571 81586045817866699472585357)
            ·
              refine ⟨30594767181700012302219509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81586045817866699472585357 30594767181700012302219509)
              ·
                refine ⟨2868259423284376153333079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30594767181700012302219509 2868259423284376153333079)
                ·
                  refine ⟨4302389134926564229999619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868259423284376153333079 4302389134926564229999619)
                  ·
                    refine ⟨6453583702389846344999429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302389134926564229999619 6453583702389846344999429)
                    ·
                      refine ⟨1210046944198096189687393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6453583702389846344999429 1210046944198096189687393)
                      ·
                        rfl

theorem cell23_2356558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_2356558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356558 prefixEnd_2356558 := by exact prefixLift 2356558
  have htrace : WordTrace (prefixWord ++ tailWord_2356558) baseStart_2356558 baseEnd_2356558 := by
    simpa [prefixWord, tailWord_2356558, baseEnd_2356558] using wordTrace_append hprefix tailTrace_2356558
  have hstable : (prefixWord ++ tailWord_2356558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356558).length < 2 ^ (prefixWord ++ tailWord_2356558).sum := by decide
  have hdescent : baseEnd_2356558 < baseStart_2356558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356568 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 2, 4]
def baseStart_2356568 : Nat := 118140960795 + 2356568 * 2 ^ 59
def prefixEnd_2356568 : Nat := 4983230072969 + 3 ^ 40 * 2356568 * 2
def baseEnd_2356568 : Nat := 403350693001547050187449

theorem tailTrace_2356568 : CollatzResearch.WordTrace tailWord_2356568 prefixEnd_2356568 403350693001547050187449 := by
  unfold tailWord_2356568
  simp only [CollatzResearch.WordTrace]
  refine ⟨42975548063282040308627179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57300730751042720411502905 42975548063282040308627179)
  ·
    refine ⟨64463322094923060462940769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42975548063282040308627179 64463322094923060462940769)
    ·
      refine ⟨48347491571192295347205577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64463322094923060462940769 48347491571192295347205577)
      ·
        refine ⟨36260618678394221510404183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48347491571192295347205577 36260618678394221510404183)
        ·
          refine ⟨54390928017591332265606275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36260618678394221510404183 54390928017591332265606275)
          ·
            refine ⟨81586392026386998398409413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54390928017591332265606275 81586392026386998398409413)
            ·
              refine ⟨15297448504947562199701765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81586392026386998398409413 15297448504947562199701765)
              ·
                refine ⟨2868271594677667912444081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15297448504947562199701765 2868271594677667912444081)
                ·
                  refine ⟨2151203696008250934333061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868271594677667912444081 2151203696008250934333061)
                  ·
                    refine ⟨403350693001547050187449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151203696008250934333061 403350693001547050187449)
                    ·
                      rfl

theorem cell23_2356568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_2356568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356568 prefixEnd_2356568 := by exact prefixLift 2356568
  have htrace : WordTrace (prefixWord ++ tailWord_2356568) baseStart_2356568 baseEnd_2356568 := by
    simpa [prefixWord, tailWord_2356568, baseEnd_2356568] using wordTrace_append hprefix tailTrace_2356568
  have hstable : (prefixWord ++ tailWord_2356568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356568).length < 2 ^ (prefixWord ++ tailWord_2356568).sum := by decide
  have hdescent : baseEnd_2356568 < baseStart_2356568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356578 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2356578 : Nat := 118140960795 + 2356578 * 2 ^ 59
def prefixEnd_2356578 : Nat := 4983230072969 + 3 ^ 40 * 2356578 * 2
def baseEnd_2356578 : Nat := 1210057213811186111437301

theorem tailTrace_2356578 : CollatzResearch.WordTrace tailWord_2356578 prefixEnd_2356578 1210057213811186111437301 := by
  unfold tailWord_2356578
  simp only [CollatzResearch.WordTrace]
  refine ⟨21487865214131963081279597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57300973904351901550078925 21487865214131963081279597)
  ·
    refine ⟨8057949455299486155479849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21487865214131963081279597 8057949455299486155479849)
    ·
      refine ⟨6043462091474614616609887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8057949455299486155479849 6043462091474614616609887)
      ·
        refine ⟨9065193137211921924914831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6043462091474614616609887 9065193137211921924914831)
        ·
          refine ⟨13597789705817882887372247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9065193137211921924914831 13597789705817882887372247)
          ·
            refine ⟨20396684558726824331058371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13597789705817882887372247 20396684558726824331058371)
            ·
              refine ⟨30595026838090236496587557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20396684558726824331058371 30595026838090236496587557)
              ·
                refine ⟨5736567532141919343110167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30595026838090236496587557 5736567532141919343110167)
                ·
                  refine ⟨8604851298212879014665251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736567532141919343110167 8604851298212879014665251)
                  ·
                    refine ⟨12907276947319318521997877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8604851298212879014665251 12907276947319318521997877)
                    ·
                      refine ⟨1210057213811186111437301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12907276947319318521997877 1210057213811186111437301)
                      ·
                        rfl

theorem cell23_2356578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2356578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356578 prefixEnd_2356578 := by exact prefixLift 2356578
  have htrace : WordTrace (prefixWord ++ tailWord_2356578) baseStart_2356578 baseEnd_2356578 := by
    simpa [prefixWord, tailWord_2356578, baseEnd_2356578] using wordTrace_append hprefix tailTrace_2356578
  have hstable : (prefixWord ++ tailWord_2356578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356578).length < 2 ^ (prefixWord ++ tailWord_2356578).sum := by decide
  have hdescent : baseEnd_2356578 < baseStart_2356578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356581 : List Nat := [1, 3, 1, 3, 1, 2, 4, 8]
def baseStart_2356581 : Nat := 118140960795 + 2356581 * 2 ^ 59
def prefixEnd_2356581 : Nat := 4983230072969 + 3 ^ 40 * 2356581 * 2
def baseEnd_2356581 : Nat := 44816990898264799988881

theorem tailTrace_2356581 : CollatzResearch.WordTrace tailWord_2356581 prefixEnd_2356581 44816990898264799988881 := by
  unfold tailWord_2356581
  simp only [CollatzResearch.WordTrace]
  refine ⟨85951570275516983837477597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57301046850344655891651731 85951570275516983837477597)
  ·
    refine ⟨32231838853318868939054099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85951570275516983837477597 32231838853318868939054099)
    ·
      refine ⟨48347758279978303408581149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32231838853318868939054099 48347758279978303408581149)
      ·
        refine ⟨18130409354991863778217931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48347758279978303408581149 18130409354991863778217931)
        ·
          refine ⟨27195614032487795667326897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18130409354991863778217931 27195614032487795667326897)
          ·
            refine ⟨20396710524365846750495173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27195614032487795667326897 20396710524365846750495173)
            ·
              refine ⟨3824383223318596265717845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20396710524365846750495173 3824383223318596265717845)
              ·
                refine ⟨44816990898264799988881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3824383223318596265717845 44816990898264799988881)
                ·
                  rfl

theorem cell23_2356581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 8].length) (baseStart_2356581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356581 prefixEnd_2356581 := by exact prefixLift 2356581
  have htrace : WordTrace (prefixWord ++ tailWord_2356581) baseStart_2356581 baseEnd_2356581 := by
    simpa [prefixWord, tailWord_2356581, baseEnd_2356581] using wordTrace_append hprefix tailTrace_2356581
  have hstable : (prefixWord ++ tailWord_2356581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356581).length < 2 ^ (prefixWord ++ tailWord_2356581).sum := by decide
  have hdescent : baseEnd_2356581 < baseStart_2356581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356608 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 6, 1, 3]
def baseStart_2356608 : Nat := 118140960795 + 2356608 * 2 ^ 59
def prefixEnd_2356608 : Nat := 4983230072969 + 3 ^ 40 * 2356608 * 2
def baseEnd_2356608 : Nat := 1210072618230820994062163

theorem tailTrace_2356608 : CollatzResearch.WordTrace tailWord_2356608 prefixEnd_2356608 1210072618230820994062163 := by
  unfold tailWord_2356608
  simp only [CollatzResearch.WordTrace]
  refine ⟨42976277523209583724355239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57301703364279444965806985 42976277523209583724355239)
  ·
    refine ⟨64464416284814375586532859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42976277523209583724355239 64464416284814375586532859)
    ·
      refine ⟨96696624427221563379799289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64464416284814375586532859 96696624427221563379799289)
      ·
        refine ⟨72522468320416172534849467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96696624427221563379799289 72522468320416172534849467)
        ·
          refine ⟨108783702480624258802274201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72522468320416172534849467 108783702480624258802274201)
          ·
            refine ⟨81587776860468194101705651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108783702480624258802274201 81587776860468194101705651)
            ·
              refine ⟨122381665290702291152558477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81587776860468194101705651 122381665290702291152558477)
              ·
                refine ⟨45893124484013359182209429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122381665290702291152558477 45893124484013359182209429)
                ·
                  refine ⟨2151240210188126211666067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45893124484013359182209429 2151240210188126211666067)
                  ·
                    refine ⟨3226860315282189317499101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2151240210188126211666067 3226860315282189317499101)
                    ·
                      refine ⟨1210072618230820994062163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3226860315282189317499101 1210072618230820994062163)
                      ·
                        rfl

theorem cell23_2356608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_2356608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356608 prefixEnd_2356608 := by exact prefixLift 2356608
  have htrace : WordTrace (prefixWord ++ tailWord_2356608) baseStart_2356608 baseEnd_2356608 := by
    simpa [prefixWord, tailWord_2356608, baseEnd_2356608] using wordTrace_append hprefix tailTrace_2356608
  have hstable : (prefixWord ++ tailWord_2356608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356608).length < 2 ^ (prefixWord ++ tailWord_2356608).sum := by decide
  have hdescent : baseEnd_2356608 < baseStart_2356608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356612 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_2356612 : Nat := 118140960795 + 2356612 * 2 ^ 59
def prefixEnd_2356612 : Nat := 4983230072969 + 3 ^ 40 * 2356612 * 2
def baseEnd_2356612 : Nat := 1210074672153438978412145

theorem tailTrace_2356612 : CollatzResearch.WordTrace tailWord_2356612 prefixEnd_2356612 1210074672153438978412145 := by
  unfold tailWord_2356612
  simp only [CollatzResearch.WordTrace]
  refine ⟨42976350469202338065928045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57301800625603117421237393 42976350469202338065928045)
  ·
    refine ⟨16116131425950876774723017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42976350469202338065928045 16116131425950876774723017)
    ·
      refine ⟨12087098569463157581042263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16116131425950876774723017 12087098569463157581042263)
      ·
        refine ⟨18130647854194736371563395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12087098569463157581042263 18130647854194736371563395)
        ·
          refine ⟨27195971781292104557345093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18130647854194736371563395 27195971781292104557345093)
          ·
            refine ⟨5099244708992269604502205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27195971781292104557345093 5099244708992269604502205)
            ·
              refine ⟨1912216765872101101688327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5099244708992269604502205 1912216765872101101688327)
              ·
                refine ⟨2868325148808151652532491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912216765872101101688327 2868325148808151652532491)
                ·
                  refine ⟨4302487723212227478798737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868325148808151652532491 4302487723212227478798737)
                  ·
                    refine ⟨3226865792409170609099053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4302487723212227478798737 3226865792409170609099053)
                    ·
                      refine ⟨1210074672153438978412145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3226865792409170609099053 1210074672153438978412145)
                      ·
                        rfl

theorem cell23_2356612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_2356612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356612 prefixEnd_2356612 := by exact prefixLift 2356612
  have htrace : WordTrace (prefixWord ++ tailWord_2356612) baseStart_2356612 baseEnd_2356612 := by
    simpa [prefixWord, tailWord_2356612, baseEnd_2356612] using wordTrace_append hprefix tailTrace_2356612
  have hstable : (prefixWord ++ tailWord_2356612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356612).length < 2 ^ (prefixWord ++ tailWord_2356612).sum := by decide
  have hdescent : baseEnd_2356612 < baseStart_2356612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356628 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2356628 : Nat := 118140960795 + 2356628 * 2 ^ 59
def prefixEnd_2356628 : Nat := 4983230072969 + 3 ^ 40 * 2356628 * 2
def baseEnd_2356628 : Nat := 403360962614636971937357

theorem tailTrace_2356628 : CollatzResearch.WordTrace tailWord_2356628 prefixEnd_2356628 403360962614636971937357 := by
  unfold tailWord_2356628
  simp only [CollatzResearch.WordTrace]
  refine ⟨42976642253173355432219269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57302189670897807242959025 42976642253173355432219269)
  ·
    refine ⟨8058120422470004143541113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42976642253173355432219269 8058120422470004143541113)
    ·
      refine ⟨6043590316852503107655835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8058120422470004143541113 6043590316852503107655835)
      ·
        refine ⟨9065385475278754661483753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6043590316852503107655835 9065385475278754661483753)
        ·
          refine ⟨6799039106459065996112815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9065385475278754661483753 6799039106459065996112815)
          ·
            refine ⟨10198558659688598994169223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6799039106459065996112815 10198558659688598994169223)
            ·
              refine ⟨15297837989532898491253835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10198558659688598994169223 15297837989532898491253835)
              ·
                refine ⟨22946756984299347736880753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15297837989532898491253835 22946756984299347736880753)
                ·
                  refine ⟨17210067738224510802660565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22946756984299347736880753 17210067738224510802660565)
                  ·
                    refine ⟨403360962614636971937357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17210067738224510802660565 403360962614636971937357)
                    ·
                      rfl

theorem cell23_2356628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2356628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356628 prefixEnd_2356628 := by exact prefixLift 2356628
  have htrace : WordTrace (prefixWord ++ tailWord_2356628) baseStart_2356628 baseEnd_2356628 := by
    simpa [prefixWord, tailWord_2356628, baseEnd_2356628] using wordTrace_append hprefix tailTrace_2356628
  have hstable : (prefixWord ++ tailWord_2356628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356628).length < 2 ^ (prefixWord ++ tailWord_2356628).sum := by decide
  have hdescent : baseEnd_2356628 < baseStart_2356628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356642 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2356642 : Nat := 118140960795 + 2356642 * 2 ^ 59
def prefixEnd_2356642 : Nat := 4983230072969 + 3 ^ 40 * 2356642 * 2
def baseEnd_2356642 : Nat := 1210090076573073861037007

theorem tailTrace_2356642 : CollatzResearch.WordTrace tailWord_2356642 prefixEnd_2356642 1210090076573073861037007 := by
  unfold tailWord_2356642
  simp only [CollatzResearch.WordTrace]
  refine ⟨21488448782073997813862045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57302530085530660836965453 21488448782073997813862045)
  ·
    refine ⟨8058168293277749180198267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21488448782073997813862045 8058168293277749180198267)
    ·
      refine ⟨12087252439916623770297401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8058168293277749180198267 12087252439916623770297401)
      ·
        refine ⟨9065439329937467827723051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12087252439916623770297401 9065439329937467827723051)
        ·
          refine ⟨13598158994906201741584577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9065439329937467827723051 13598158994906201741584577)
          ·
            refine ⟨10198619246179651306188433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13598158994906201741584577 10198619246179651306188433)
            ·
              refine ⟨7648964434634738479641325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10198619246179651306188433 7648964434634738479641325)
              ·
                refine ⟨2868361662988026929865497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7648964434634738479641325 2868361662988026929865497)
                ·
                  refine ⟨2151271247241020197399123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868361662988026929865497 2151271247241020197399123)
                  ·
                    refine ⟨3226906870861530296098685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2151271247241020197399123 3226906870861530296098685)
                    ·
                      refine ⟨1210090076573073861037007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3226906870861530296098685 1210090076573073861037007)
                      ·
                        rfl

theorem cell23_2356642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2356642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356642 prefixEnd_2356642 := by exact prefixLift 2356642
  have htrace : WordTrace (prefixWord ++ tailWord_2356642) baseStart_2356642 baseEnd_2356642 := by
    simpa [prefixWord, tailWord_2356642, baseEnd_2356642] using wordTrace_append hprefix tailTrace_2356642
  have hstable : (prefixWord ++ tailWord_2356642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356642).length < 2 ^ (prefixWord ++ tailWord_2356642).sum := by decide
  have hdescent : baseEnd_2356642 < baseStart_2356642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356682 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_2356682 : Nat := 118140960795 + 2356682 * 2 ^ 59
def prefixEnd_2356682 : Nat := 4983230072969 + 3 ^ 40 * 2356682 * 2
def baseEnd_2356682 : Nat := 1210110615799253704536823

theorem tailTrace_2356682 : CollatzResearch.WordTrace tailWord_2356682 prefixEnd_2356682 1210110615799253704536823 := by
  unfold tailWord_2356682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21488813512037769521726075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57303502698767385391269533 21488813512037769521726075)
  ·
    refine ⟨32233220268056654282589113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21488813512037769521726075 32233220268056654282589113)
    ·
      refine ⟨24174915201042490711941835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32233220268056654282589113 24174915201042490711941835)
      ·
        refine ⟨36262372801563736067912753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24174915201042490711941835 36262372801563736067912753)
        ·
          refine ⟨27196779601172802050934565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36262372801563736067912753 27196779601172802050934565)
          ·
            refine ⟨5099396175219900384550231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27196779601172802050934565 5099396175219900384550231)
            ·
              refine ⟨7649094262829850576825347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099396175219900384550231 7649094262829850576825347)
              ·
                refine ⟨11473641394244775865238021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7649094262829850576825347 11473641394244775865238021)
                ·
                  refine ⟨2151307761420895474732129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11473641394244775865238021 2151307761420895474732129)
                  ·
                    refine ⟨1613480821065671606049097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2151307761420895474732129 1613480821065671606049097)
                    ·
                      refine ⟨1210110615799253704536823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1613480821065671606049097 1210110615799253704536823)
                      ·
                        rfl

theorem cell23_2356682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_2356682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356682 prefixEnd_2356682 := by exact prefixLift 2356682
  have htrace : WordTrace (prefixWord ++ tailWord_2356682) baseStart_2356682 baseEnd_2356682 := by
    simpa [prefixWord, tailWord_2356682, baseEnd_2356682] using wordTrace_append hprefix tailTrace_2356682
  have hstable : (prefixWord ++ tailWord_2356682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356682).length < 2 ^ (prefixWord ++ tailWord_2356682).sum := by decide
  have hdescent : baseEnd_2356682 < baseStart_2356682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356718 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2356718 : Nat := 118140960795 + 2356718 * 2 ^ 59
def prefixEnd_2356718 : Nat := 4983230072969 + 3 ^ 40 * 2356718 * 2
def baseEnd_2356718 : Nat := 403376367034271854562219

theorem tailTrace_2356718 : CollatzResearch.WordTrace tailWord_2356718 prefixEnd_2356718 403376367034271854562219 := by
  unfold tailWord_2356718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10744570884502582029401851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57304378050680437490143205 10744570884502582029401851)
  ·
    refine ⟨16116856326753873044102777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10744570884502582029401851 16116856326753873044102777)
    ·
      refine ⟨12087642245065404783077083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16116856326753873044102777 12087642245065404783077083)
      ·
        refine ⟨18131463367598107174615625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12087642245065404783077083 18131463367598107174615625)
        ·
          refine ⟨13598597525698580380961719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18131463367598107174615625 13598597525698580380961719)
          ·
            refine ⟨20397896288547870571442579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13598597525698580380961719 20397896288547870571442579)
            ·
              refine ⟨30596844432821805857163869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20397896288547870571442579 30596844432821805857163869)
              ·
                refine ⟨11473816662308177196436451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30596844432821805857163869 11473816662308177196436451)
                ·
                  refine ⟨17210724993462265794654677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11473816662308177196436451 17210724993462265794654677)
                  ·
                    refine ⟨403376367034271854562219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17210724993462265794654677 403376367034271854562219)
                    ·
                      rfl

theorem cell23_2356718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2356718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356718 prefixEnd_2356718 := by exact prefixLift 2356718
  have htrace : WordTrace (prefixWord ++ tailWord_2356718) baseStart_2356718 baseEnd_2356718 := by
    simpa [prefixWord, tailWord_2356718, baseEnd_2356718] using wordTrace_append hprefix tailTrace_2356718
  have hstable : (prefixWord ++ tailWord_2356718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356718).length < 2 ^ (prefixWord ++ tailWord_2356718).sum := by decide
  have hdescent : baseEnd_2356718 < baseStart_2356718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356722 : List Nat := [3, 2, 1, 4, 1, 1, 3, 3, 5]
def baseStart_2356722 : Nat := 118140960795 + 2356722 * 2 ^ 59
def prefixEnd_2356722 : Nat := 4983230072969 + 3 ^ 40 * 2356722 * 2
def baseEnd_2356722 : Nat := 134459017225048172004071

theorem tailTrace_2356722 : CollatzResearch.WordTrace tailWord_2356722 prefixEnd_2356722 134459017225048172004071 := by
  unfold tailWord_2356722
  simp only [CollatzResearch.WordTrace]
  refine ⟨21489178242001541229590105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57304475312004109945573613 21489178242001541229590105)
  ·
    refine ⟨16116883681501155922192579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21489178242001541229590105 16116883681501155922192579)
    ·
      refine ⟨24175325522251733883288869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16116883681501155922192579 24175325522251733883288869)
      ·
        refine ⟨4532873535422200103116663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24175325522251733883288869 4532873535422200103116663)
        ·
          refine ⟨6799310303133300154674995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532873535422200103116663 6799310303133300154674995)
          ·
            refine ⟨10198965454699950232012493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6799310303133300154674995 10198965454699950232012493)
            ·
              refine ⟨3824612045512481337004685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10198965454699950232012493 3824612045512481337004685)
              ·
                refine ⟨1434229517067180501376757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3824612045512481337004685 1434229517067180501376757)
                ·
                  refine ⟨134459017225048172004071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1434229517067180501376757 134459017225048172004071)
                  ·
                    rfl

theorem cell23_2356722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_2356722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356722 prefixEnd_2356722 := by exact prefixLift 2356722
  have htrace : WordTrace (prefixWord ++ tailWord_2356722) baseStart_2356722 baseEnd_2356722 := by
    simpa [prefixWord, tailWord_2356722, baseEnd_2356722] using wordTrace_append hprefix tailTrace_2356722
  have hstable : (prefixWord ++ tailWord_2356722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356722).length < 2 ^ (prefixWord ++ tailWord_2356722).sum := by decide
  have hdescent : baseEnd_2356722 < baseStart_2356722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356731 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 10]
def baseStart_2356731 : Nat := 118140960795 + 2356731 * 2 ^ 59
def prefixEnd_2356731 : Nat := 4983230072969 + 3 ^ 40 * 2356731 * 2
def baseEnd_2356731 : Nat := 403378592117108004274699

theorem tailTrace_2356731 : CollatzResearch.WordTrace tailWord_2356731 prefixEnd_2356731 403378592117108004274699 := by
  unfold tailWord_2356731
  simp only [CollatzResearch.WordTrace]
  refine ⟨85957041224973559455438047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57304694149982372970292031 85957041224973559455438047)
  ·
    refine ⟨128935561837460339183157071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85957041224973559455438047 128935561837460339183157071)
    ·
      refine ⟨193403342756190508774735607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128935561837460339183157071 193403342756190508774735607)
      ·
        refine ⟨290105014134285763162103411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193403342756190508774735607 290105014134285763162103411)
        ·
          refine ⟨435157521201428644743155117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290105014134285763162103411 435157521201428644743155117)
          ·
            refine ⟨163184070450535741778683169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 435157521201428644743155117 163184070450535741778683169)
            ·
              refine ⟨122388052837901806334012377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163184070450535741778683169 122388052837901806334012377)
              ·
                refine ⟨91791039628426354750509283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122388052837901806334012377 91791039628426354750509283)
                ·
                  refine ⟨137686559442639532125763925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91791039628426354750509283 137686559442639532125763925)
                  ·
                    refine ⟨403378592117108004274699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 137686559442639532125763925 403378592117108004274699)
                    ·
                      rfl

theorem cell23_2356731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_2356731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356731 prefixEnd_2356731 := by exact prefixLift 2356731
  have htrace : WordTrace (prefixWord ++ tailWord_2356731) baseStart_2356731 baseEnd_2356731 := by
    simpa [prefixWord, tailWord_2356731, baseEnd_2356731] using wordTrace_append hprefix tailTrace_2356731
  have hstable : (prefixWord ++ tailWord_2356731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356731).length < 2 ^ (prefixWord ++ tailWord_2356731).sum := by decide
  have hdescent : baseEnd_2356731 < baseStart_2356731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356765 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2356765 : Nat := 118140960795 + 2356765 * 2 ^ 59
def prefixEnd_2356765 : Nat := 4983230072969 + 3 ^ 40 * 2356765 * 2
def baseEnd_2356765 : Nat := 403384411564525626599647

theorem tailTrace_2356765 : CollatzResearch.WordTrace tailWord_2356765 prefixEnd_2356765 403384411564525626599647 := by
  unfold tailWord_2356765
  simp only [CollatzResearch.WordTrace]
  refine ⟨85958281306850383262175749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57305520871233588841450499 85958281306850383262175749)
  ·
    refine ⟨16117177745034446861657953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85958281306850383262175749 16117177745034446861657953)
    ·
      refine ⟨12087883308775835146243465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16117177745034446861657953 12087883308775835146243465)
      ·
        refine ⟨9065912481581876359682599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12087883308775835146243465 9065912481581876359682599)
        ·
          refine ⟨13598868722372814539523899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9065912481581876359682599 13598868722372814539523899)
          ·
            refine ⟨20398303083559221809285849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13598868722372814539523899 20398303083559221809285849)
            ·
              refine ⟨15298727312669416356964387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20398303083559221809285849 15298727312669416356964387)
              ·
                refine ⟨22948090969004124535446581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15298727312669416356964387 22948090969004124535446581)
                ·
                  refine ⟨2151383528344136675198117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22948090969004124535446581 2151383528344136675198117)
                  ·
                    refine ⟨403384411564525626599647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151383528344136675198117 403384411564525626599647)
                    ·
                      rfl

theorem cell23_2356765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2356765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356765 prefixEnd_2356765 := by exact prefixLift 2356765
  have htrace : WordTrace (prefixWord ++ tailWord_2356765) baseStart_2356765 baseEnd_2356765 := by
    simpa [prefixWord, tailWord_2356765, baseEnd_2356765] using wordTrace_append hprefix tailTrace_2356765
  have hstable : (prefixWord ++ tailWord_2356765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356765).length < 2 ^ (prefixWord ++ tailWord_2356765).sum := by decide
  have hdescent : baseEnd_2356765 < baseStart_2356765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356799 : List Nat := [1, 1, 2, 2, 3, 3, 4, 2, 1, 4]
def baseStart_2356799 : Nat := 118140960795 + 2356799 * 2 ^ 59
def prefixEnd_2356799 : Nat := 4983230072969 + 3 ^ 40 * 2356799 * 2
def baseEnd_2356799 : Nat := 403390231011943248924595

theorem tailTrace_2356799 : CollatzResearch.WordTrace tailWord_2356799 prefixEnd_2356799 403390231011943248924595 := by
  unfold tailWord_2356799
  simp only [CollatzResearch.WordTrace]
  refine ⟨85959521388727207068913451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57306347592484804712608967 85959521388727207068913451)
  ·
    refine ⟨128939282083090810603370177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85959521388727207068913451 128939282083090810603370177)
    ·
      refine ⟨96704461562318107952527633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128939282083090810603370177 96704461562318107952527633)
      ·
        refine ⟨72528346171738580964395725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96704461562318107952527633 72528346171738580964395725)
        ·
          refine ⟨27198129814401967861648397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72528346171738580964395725 27198129814401967861648397)
          ·
            refine ⟨10199298680400737948118149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27198129814401967861648397 10199298680400737948118149)
            ·
              refine ⟨1912368502575138365272153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10199298680400737948118149 1912368502575138365272153)
              ·
                refine ⟨1434276376931353773954115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1912368502575138365272153 1434276376931353773954115)
                ·
                  refine ⟨2151414565397030660931173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434276376931353773954115 2151414565397030660931173)
                  ·
                    refine ⟨403390231011943248924595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151414565397030660931173 403390231011943248924595)
                    ·
                      rfl

theorem cell23_2356799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 4].length) (baseStart_2356799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356799 prefixEnd_2356799 := by exact prefixLift 2356799
  have htrace : WordTrace (prefixWord ++ tailWord_2356799) baseStart_2356799 baseEnd_2356799 := by
    simpa [prefixWord, tailWord_2356799, baseEnd_2356799] using wordTrace_append hprefix tailTrace_2356799
  have hstable : (prefixWord ++ tailWord_2356799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356799).length < 2 ^ (prefixWord ++ tailWord_2356799).sum := by decide
  have hdescent : baseEnd_2356799 < baseStart_2356799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356806 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_2356806 : Nat := 118140960795 + 2356806 * 2 ^ 59
def prefixEnd_2356806 : Nat := 4983230072969 + 3 ^ 40 * 2356806 * 2
def baseEnd_2356806 : Nat := 1210174287400411219386253

theorem tailTrace_2356806 : CollatzResearch.WordTrace tailWord_2356806 prefixEnd_2356806 1210174287400411219386253 := by
  unfold tailWord_2356806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686243021865682727013071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57306517799801231509612181 2686243021865682727013071)
  ·
    refine ⟨4029364532798524090519607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2686243021865682727013071 4029364532798524090519607)
    ·
      refine ⟨6044046799197786135779411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4029364532798524090519607 6044046799197786135779411)
      ·
        refine ⟨9066070198796679203669117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6044046799197786135779411 9066070198796679203669117)
        ·
          refine ⟨3399776324548754701375919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9066070198796679203669117 3399776324548754701375919)
          ·
            refine ⟨5099664486823132052063879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399776324548754701375919 5099664486823132052063879)
            ·
              refine ⟨7649496730234698078095819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099664486823132052063879 7649496730234698078095819)
              ·
                refine ⟨11474245095352047117143729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7649496730234698078095819 11474245095352047117143729)
                ·
                  refine ⟨8605683821514035337857797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11474245095352047117143729 8605683821514035337857797)
                  ·
                    refine ⟨1613565716533881625848337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8605683821514035337857797 1613565716533881625848337)
                    ·
                      refine ⟨1210174287400411219386253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1613565716533881625848337 1210174287400411219386253)
                      ·
                        rfl

theorem cell23_2356806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_2356806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356806 prefixEnd_2356806 := by exact prefixLift 2356806
  have htrace : WordTrace (prefixWord ++ tailWord_2356806) baseStart_2356806 baseEnd_2356806 := by
    simpa [prefixWord, tailWord_2356806, baseEnd_2356806] using wordTrace_append hprefix tailTrace_2356806
  have hstable : (prefixWord ++ tailWord_2356806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356806).length < 2 ^ (prefixWord ++ tailWord_2356806).sum := by decide
  have hdescent : baseEnd_2356806 < baseStart_2356806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356815 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 1, 5, 2]
def baseStart_2356815 : Nat := 118140960795 + 2356815 * 2 ^ 59
def prefixEnd_2356815 : Nat := 4983230072969 + 3 ^ 40 * 2356815 * 2
def baseEnd_2356815 : Nat := 1210178908726301684173711

theorem tailTrace_2356815 : CollatzResearch.WordTrace tailWord_2356815 prefixEnd_2356815 1210178908726301684173711 := by
  unfold tailWord_2356815
  simp only [CollatzResearch.WordTrace]
  refine ⟨85960104956669241801495899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57306736637779494534330599 85960104956669241801495899)
  ·
    refine ⟨128940157435003862702243849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85960104956669241801495899 128940157435003862702243849)
    ·
      refine ⟨96705118076252897026682887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128940157435003862702243849 96705118076252897026682887)
      ·
        refine ⟨145057677114379345540024331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96705118076252897026682887 145057677114379345540024331)
        ·
          refine ⟨217586515671569018310036497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145057677114379345540024331 217586515671569018310036497)
          ·
            refine ⟨163189886753676763732527373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217586515671569018310036497 163189886753676763732527373)
            ·
              refine ⟨61196207532628786399697765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163189886753676763732527373 61196207532628786399697765)
              ·
                refine ⟨11474288912367897449943331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61196207532628786399697765 11474288912367897449943331)
                ·
                  refine ⟨17211433368551846174914997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11474288912367897449943331 17211433368551846174914997)
                  ·
                    refine ⟨1613571878301735578898281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17211433368551846174914997 1613571878301735578898281)
                    ·
                      refine ⟨1210178908726301684173711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1613571878301735578898281 1210178908726301684173711)
                      ·
                        rfl

theorem cell23_2356815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5, 2].length) (baseStart_2356815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356815 prefixEnd_2356815 := by exact prefixLift 2356815
  have htrace : WordTrace (prefixWord ++ tailWord_2356815) baseStart_2356815 baseEnd_2356815 := by
    simpa [prefixWord, tailWord_2356815, baseEnd_2356815] using wordTrace_append hprefix tailTrace_2356815
  have hstable : (prefixWord ++ tailWord_2356815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356815).length < 2 ^ (prefixWord ++ tailWord_2356815).sum := by decide
  have hdescent : baseEnd_2356815 < baseStart_2356815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356839 : List Nat := [1, 1, 5, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_2356839 : Nat := 118140960795 + 2356839 * 2 ^ 59
def prefixEnd_2356839 : Nat := 4983230072969 + 3 ^ 40 * 2356839 * 2
def baseEnd_2356839 : Nat := 1210191232262009590273601

theorem tailTrace_2356839 : CollatzResearch.WordTrace tailWord_2356839 prefixEnd_2356839 1210191232262009590273601 := by
  unfold tailWord_2356839
  simp only [CollatzResearch.WordTrace]
  refine ⟨85960980308582293900369571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57307320205721529266913047 85960980308582293900369571)
  ·
    refine ⟨128941470462873440850554357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85960980308582293900369571 128941470462873440850554357)
    ·
      refine ⟨12088262855894385079739471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128941470462873440850554357 12088262855894385079739471)
      ·
        refine ⟨18132394283841577619609207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12088262855894385079739471 18132394283841577619609207)
        ·
          refine ⟨27198591425762366429413811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18132394283841577619609207 27198591425762366429413811)
          ·
            refine ⟨40797887138643549644120717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27198591425762366429413811 40797887138643549644120717)
            ·
              refine ⟨15299207676991331116545269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40797887138643549644120717 15299207676991331116545269)
              ·
                refine ⟨1434300719717937292176119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15299207676991331116545269 1434300719717937292176119)
                ·
                  refine ⟨2151451079576905938264179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434300719717937292176119 2151451079576905938264179)
                  ·
                    refine ⟨3227176619365358907396269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2151451079576905938264179 3227176619365358907396269)
                    ·
                      refine ⟨1210191232262009590273601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3227176619365358907396269 1210191232262009590273601)
                      ·
                        rfl

theorem cell23_2356839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_2356839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356839 prefixEnd_2356839 := by exact prefixLift 2356839
  have htrace : WordTrace (prefixWord ++ tailWord_2356839) baseStart_2356839 baseEnd_2356839 := by
    simpa [prefixWord, tailWord_2356839, baseEnd_2356839] using wordTrace_append hprefix tailTrace_2356839
  have hstable : (prefixWord ++ tailWord_2356839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356839).length < 2 ^ (prefixWord ++ tailWord_2356839).sum := by decide
  have hdescent : baseEnd_2356839 < baseStart_2356839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356842 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_2356842 : Nat := 118140960795 + 2356842 * 2 ^ 59
def prefixEnd_2356842 : Nat := 4983230072969 + 3 ^ 40 * 2356842 * 2
def baseEnd_2356842 : Nat := 403397590901324359512029

theorem tailTrace_2356842 : CollatzResearch.WordTrace tailWord_2356842 prefixEnd_2356842 403397590901324359512029 := by
  unfold tailWord_2356842
  simp only [CollatzResearch.WordTrace]
  refine ⟨21490272431892856353182195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57307393151714283608485853 21490272431892856353182195)
  ·
    refine ⟨32235408647839284529773293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21490272431892856353182195 32235408647839284529773293)
    ·
      refine ⟨12088278242939731698664985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32235408647839284529773293 12088278242939731698664985)
      ·
        refine ⟨9066208682204798773998739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12088278242939731698664985 9066208682204798773998739)
        ·
          refine ⟨13599313023307198160998109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9066208682204798773998739 13599313023307198160998109)
          ·
            refine ⟨5099742383740199310374291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13599313023307198160998109 5099742383740199310374291)
            ·
              refine ⟨7649613575610298965561437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099742383740199310374291 7649613575610298965561437)
              ·
                refine ⟨2868605090853862112085539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7649613575610298965561437 2868605090853862112085539)
                ·
                  refine ⟨4302907636280793168128309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868605090853862112085539 4302907636280793168128309)
                  ·
                    refine ⟨403397590901324359512029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4302907636280793168128309 403397590901324359512029)
                    ·
                      rfl

theorem cell23_2356842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_2356842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356842 prefixEnd_2356842 := by exact prefixLift 2356842
  have htrace : WordTrace (prefixWord ++ tailWord_2356842) baseStart_2356842 baseEnd_2356842 := by
    simpa [prefixWord, tailWord_2356842, baseEnd_2356842] using wordTrace_append hprefix tailTrace_2356842
  have hstable : (prefixWord ++ tailWord_2356842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356842).length < 2 ^ (prefixWord ++ tailWord_2356842).sum := by decide
  have hdescent : baseEnd_2356842 < baseStart_2356842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356865 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2356865 : Nat := 118140960795 + 2356865 * 2 ^ 59
def prefixEnd_2356865 : Nat := 4983230072969 + 3 ^ 40 * 2356865 * 2
def baseEnd_2356865 : Nat := 1210204582759026488548481

theorem tailTrace_2356865 : CollatzResearch.WordTrace tailWord_2356865 prefixEnd_2356865 1210204582759026488548481 := by
  unfold tailWord_2356865
  simp only [CollatzResearch.WordTrace]
  refine ⟨85961928606488100340816049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57307952404325400227210699 85961928606488100340816049)
  ·
    refine ⟨64471446454866075255612037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85961928606488100340816049 64471446454866075255612037)
    ·
      refine ⟨12088396210287389110427257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64471446454866075255612037 12088396210287389110427257)
      ·
        refine ⟨9066297157715541832820443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12088396210287389110427257 9066297157715541832820443)
        ·
          refine ⟨13599445736573312749230665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9066297157715541832820443 13599445736573312749230665)
          ·
            refine ⟨10199584302429984561922999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13599445736573312749230665 10199584302429984561922999)
            ·
              refine ⟨15299376453644976842884499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10199584302429984561922999 15299376453644976842884499)
              ·
                refine ⟨22949064680467465264326749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15299376453644976842884499 22949064680467465264326749)
                ·
                  refine ⟨8605899255175299474122531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22949064680467465264326749 8605899255175299474122531)
                  ·
                    refine ⟨12908848882762949211183797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8605899255175299474122531 12908848882762949211183797)
                    ·
                      refine ⟨1210204582759026488548481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12908848882762949211183797 1210204582759026488548481)
                      ·
                        rfl

theorem cell23_2356865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2356865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356865 prefixEnd_2356865 := by exact prefixLift 2356865
  have htrace : WordTrace (prefixWord ++ tailWord_2356865) baseStart_2356865 baseEnd_2356865 := by
    simpa [prefixWord, tailWord_2356865, baseEnd_2356865] using wordTrace_append hprefix tailTrace_2356865
  have hstable : (prefixWord ++ tailWord_2356865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356865).length < 2 ^ (prefixWord ++ tailWord_2356865).sum := by decide
  have hdescent : baseEnd_2356865 < baseStart_2356865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356912 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 4, 1, 3]
def baseStart_2356912 : Nat := 118140960795 + 2356912 * 2 ^ 59
def prefixEnd_2356912 : Nat := 4983230072969 + 3 ^ 40 * 2356912 * 2
def baseEnd_2356912 : Nat := 1210228716349787804660765

theorem tailTrace_2356912 : CollatzResearch.WordTrace tailWord_2356912 prefixEnd_2356912 1210228716349787804660765 := by
  unfold tailWord_2356912
  simp only [CollatzResearch.WordTrace]
  refine ⟨42981821418658913683888495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57309095224878551578517993 42981821418658913683888495)
  ·
    refine ⟨64472732127988370525832743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42981821418658913683888495 64472732127988370525832743)
    ·
      refine ⟨96709098191982555788749115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64472732127988370525832743 96709098191982555788749115)
      ·
        refine ⟨145063647287973833683123673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96709098191982555788749115 145063647287973833683123673)
        ·
          refine ⟨108797735465980375262342755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145063647287973833683123673 108797735465980375262342755)
          ·
            refine ⟨163196603198970562893514133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108797735465980375262342755 163196603198970562893514133)
            ·
              refine ⟨7649840774951745135633475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163196603198970562893514133 7649840774951745135633475)
              ·
                refine ⟨11474761162427617703450213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7649840774951745135633475 11474761162427617703450213)
                ·
                  refine ⟨2151517717955178319396915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11474761162427617703450213 2151517717955178319396915)
                  ·
                    refine ⟨3227276576932767479095373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2151517717955178319396915 3227276576932767479095373)
                    ·
                      refine ⟨1210228716349787804660765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3227276576932767479095373 1210228716349787804660765)
                      ·
                        rfl

theorem cell23_2356912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 1, 3].length) (baseStart_2356912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356912 prefixEnd_2356912 := by exact prefixLift 2356912
  have htrace : WordTrace (prefixWord ++ tailWord_2356912) baseStart_2356912 baseEnd_2356912 := by
    simpa [prefixWord, tailWord_2356912, baseEnd_2356912] using wordTrace_append hprefix tailTrace_2356912
  have hstable : (prefixWord ++ tailWord_2356912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356912).length < 2 ^ (prefixWord ++ tailWord_2356912).sum := by decide
  have hdescent : baseEnd_2356912 < baseStart_2356912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356930 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2356930 : Nat := 118140960795 + 2356930 * 2 ^ 59
def prefixEnd_2356930 : Nat := 4983230072969 + 3 ^ 40 * 2356930 * 2
def baseEnd_2356930 : Nat := 1210237959001568734235683

theorem tailTrace_2356930 : CollatzResearch.WordTrace tailWord_2356930 prefixEnd_2356930 1210237959001568734235683 := by
  unfold tailWord_2356930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21491074837813154110483061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57309532900835077627954829 21491074837813154110483061)
  ·
    refine ⟨2014788266044983197857787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21491074837813154110483061 2014788266044983197857787)
    ·
      refine ⟨3022182399067474796786681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014788266044983197857787 3022182399067474796786681)
      ·
        refine ⟨2266636799300606097590011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3022182399067474796786681 2266636799300606097590011)
        ·
          refine ⟨3399955198950909146385017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266636799300606097590011 3399955198950909146385017)
          ·
            refine ⟨2549966399213181859788763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3399955198950909146385017 2549966399213181859788763)
            ·
              refine ⟨3824949598819772789683145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549966399213181859788763 3824949598819772789683145)
              ·
                refine ⟨2868712199114829592262359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3824949598819772789683145 2868712199114829592262359)
                ·
                  refine ⟨4303068298672244388393539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868712199114829592262359 4303068298672244388393539)
                  ·
                    refine ⟨6454602448008366582590309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4303068298672244388393539 6454602448008366582590309)
                    ·
                      refine ⟨1210237959001568734235683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6454602448008366582590309 1210237959001568734235683)
                      ·
                        rfl

theorem cell23_2356930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2356930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356930 prefixEnd_2356930 := by exact prefixLift 2356930
  have htrace : WordTrace (prefixWord ++ tailWord_2356930) baseStart_2356930 baseEnd_2356930 := by
    simpa [prefixWord, tailWord_2356930, baseEnd_2356930] using wordTrace_append hprefix tailTrace_2356930
  have hstable : (prefixWord ++ tailWord_2356930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356930).length < 2 ^ (prefixWord ++ tailWord_2356930).sum := by decide
  have hdescent : baseEnd_2356930 < baseStart_2356930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356950 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2356950 : Nat := 118140960795 + 2356950 * 2 ^ 59
def prefixEnd_2356950 : Nat := 4983230072969 + 3 ^ 40 * 2356950 * 2
def baseEnd_2356950 : Nat := 1210248228614658655985591

theorem tailTrace_2356950 : CollatzResearch.WordTrace tailWord_2356950 prefixEnd_2356950 1210248228614658655985591 := by
  unfold tailWord_2356950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5372814300698759991103769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57310019207453439905106869 5372814300698759991103769)
  ·
    refine ⟨4029610725524069993327827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5372814300698759991103769 4029610725524069993327827)
    ·
      refine ⟨6044416088286104989991741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4029610725524069993327827 6044416088286104989991741)
      ·
        refine ⟨2266656033107289371246903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6044416088286104989991741 2266656033107289371246903)
        ·
          refine ⟨3399984049660934056870355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266656033107289371246903 3399984049660934056870355)
          ·
            refine ⟨5099976074491401085305533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399984049660934056870355 5099976074491401085305533)
            ·
              refine ⟨1912491027934275406989575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5099976074491401085305533 1912491027934275406989575)
              ·
                refine ⟨2868736541901413110484363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912491027934275406989575 2868736541901413110484363)
                ·
                  refine ⟨4303104812852119665726545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868736541901413110484363 4303104812852119665726545)
                  ·
                    refine ⟨3227328609639089749294909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4303104812852119665726545 3227328609639089749294909)
                    ·
                      refine ⟨1210248228614658655985591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3227328609639089749294909 1210248228614658655985591)
                      ·
                        rfl

theorem cell23_2356950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2356950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356950 prefixEnd_2356950 := by exact prefixLift 2356950
  have htrace : WordTrace (prefixWord ++ tailWord_2356950) baseStart_2356950 baseEnd_2356950 := by
    simpa [prefixWord, tailWord_2356950, baseEnd_2356950] using wordTrace_append hprefix tailTrace_2356950
  have hstable : (prefixWord ++ tailWord_2356950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356950).length < 2 ^ (prefixWord ++ tailWord_2356950).sum := by decide
  have hdescent : baseEnd_2356950 < baseStart_2356950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356975 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 7]
def baseStart_2356975 : Nat := 118140960795 + 2356975 * 2 ^ 59
def prefixEnd_2356975 : Nat := 4983230072969 + 3 ^ 40 * 2356975 * 2
def baseEnd_2356975 : Nat := 134473451736780117574775

theorem tailTrace_2356975 : CollatzResearch.WordTrace tailWord_2356975 prefixEnd_2356975 134473451736780117574775 := by
  unfold tailWord_2356975
  simp only [CollatzResearch.WordTrace]
  refine ⟨85965940636089589127320379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57310627090726392751546919 85965940636089589127320379)
  ·
    refine ⟨128948910954134383690980569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85965940636089589127320379 128948910954134383690980569)
    ·
      refine ⟨96711683215600787768235427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128948910954134383690980569 96711683215600787768235427)
      ·
        refine ⟨145067524823401181652353141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96711683215600787768235427 145067524823401181652353141)
        ·
          refine ⟨13600080452193860779908107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145067524823401181652353141 13600080452193860779908107)
          ·
            refine ⟨20400120678290791169862161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13600080452193860779908107 20400120678290791169862161)
            ·
              refine ⟨15300090508718093377396621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20400120678290791169862161 15300090508718093377396621)
              ·
                refine ⟨5737533940769285016523733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15300090508718093377396621 5737533940769285016523733)
                ·
                  refine ⟨134473451736780117574775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5737533940769285016523733 134473451736780117574775)
                  ·
                    rfl

theorem cell23_2356975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 7].length) (baseStart_2356975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356975 prefixEnd_2356975 := by exact prefixLift 2356975
  have htrace : WordTrace (prefixWord ++ tailWord_2356975) baseStart_2356975 baseEnd_2356975 := by
    simpa [prefixWord, tailWord_2356975, baseEnd_2356975] using wordTrace_append hprefix tailTrace_2356975
  have hstable : (prefixWord ++ tailWord_2356975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356975).length < 2 ^ (prefixWord ++ tailWord_2356975).sum := by decide
  have hdescent : baseEnd_2356975 < baseStart_2356975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356982 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2356982 : Nat := 118140960795 + 2356982 * 2 ^ 59
def prefixEnd_2356982 : Nat := 4983230072969 + 3 ^ 40 * 2356982 * 2
def baseEnd_2356982 : Nat := 1210264659995602530785443

theorem tailTrace_2356982 : CollatzResearch.WordTrace tailWord_2356982 prefixEnd_2356982 1210264659995602530785443 := by
  unfold tailWord_2356982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5372887246691514332676575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57310797298042819548550133 5372887246691514332676575)
  ·
    refine ⟨8059330870037271499014863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5372887246691514332676575 8059330870037271499014863)
    ·
      refine ⟨12088996305055907248522295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8059330870037271499014863 12088996305055907248522295)
      ·
        refine ⟨18133494457583860872783443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12088996305055907248522295 18133494457583860872783443)
        ·
          refine ⟨27200241686375791309175165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18133494457583860872783443 27200241686375791309175165)
          ·
            refine ⟨10200090632390921740940687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27200241686375791309175165 10200090632390921740940687)
            ·
              refine ⟨15300135948586382611411031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10200090632390921740940687 15300135948586382611411031)
              ·
                refine ⟨22950203922879573917116547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15300135948586382611411031 22950203922879573917116547)
                ·
                  refine ⟨34425305884319360875674821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22950203922879573917116547 34425305884319360875674821)
                  ·
                    refine ⟨6454744853309880164189029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34425305884319360875674821 6454744853309880164189029)
                    ·
                      refine ⟨1210264659995602530785443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6454744853309880164189029 1210264659995602530785443)
                      ·
                        rfl

theorem cell23_2356982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2356982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2356982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2356982 prefixEnd_2356982 := by exact prefixLift 2356982
  have htrace : WordTrace (prefixWord ++ tailWord_2356982) baseStart_2356982 baseEnd_2356982 := by
    simpa [prefixWord, tailWord_2356982, baseEnd_2356982] using wordTrace_append hprefix tailTrace_2356982
  have hstable : (prefixWord ++ tailWord_2356982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356982).length < 2 ^ (prefixWord ++ tailWord_2356982).sum := by decide
  have hdescent : baseEnd_2356982 < baseStart_2356982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357042 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2357042 : Nat := 118140960795 + 2357042 * 2 ^ 59
def prefixEnd_2357042 : Nat := 4983230072969 + 3 ^ 40 * 2357042 * 2
def baseEnd_2357042 : Nat := 1210295468834872296035167

theorem tailTrace_2357042 : CollatzResearch.WordTrace tailWord_2357042 prefixEnd_2357042 1210295468834872296035167 := by
  unfold tailWord_2357042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21492096081711714892502345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57312256217897906380006253 21492096081711714892502345)
  ·
    refine ⟨16119072061283786169376759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21492096081711714892502345 16119072061283786169376759)
    ·
      refine ⟨24178608091925679254065139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16119072061283786169376759 24178608091925679254065139)
      ·
        refine ⟨36267912137888518881097709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24178608091925679254065139 36267912137888518881097709)
        ·
          refine ⟨13600467051708194580411641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36267912137888518881097709 13600467051708194580411641)
          ·
            refine ⟨10200350288781145935308731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13600467051708194580411641 10200350288781145935308731)
            ·
              refine ⟨15300525433171718902963097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10200350288781145935308731 15300525433171718902963097)
              ·
                refine ⟨11475394074878789177222323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15300525433171718902963097 11475394074878789177222323)
                ·
                  refine ⟨17213091112318183765833485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11475394074878789177222323 17213091112318183765833485)
                  ·
                    refine ⟨6454909167119318912187557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17213091112318183765833485 6454909167119318912187557)
                    ·
                      refine ⟨1210295468834872296035167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6454909167119318912187557 1210295468834872296035167)
                      ·
                        rfl

theorem cell23_2357042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2357042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357042 prefixEnd_2357042 := by exact prefixLift 2357042
  have htrace : WordTrace (prefixWord ++ tailWord_2357042) baseStart_2357042 baseEnd_2357042 := by
    simpa [prefixWord, tailWord_2357042, baseEnd_2357042] using wordTrace_append hprefix tailTrace_2357042
  have hstable : (prefixWord ++ tailWord_2357042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357042).length < 2 ^ (prefixWord ++ tailWord_2357042).sum := by decide
  have hdescent : baseEnd_2357042 < baseStart_2357042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357065 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 10]
def baseStart_2357065 : Nat := 118140960795 + 2357065 * 2 ^ 59
def prefixEnd_2357065 : Nat := 4983230072969 + 3 ^ 40 * 2357065 * 2
def baseEnd_2357065 : Nat := 134478586543325078449729

theorem tailTrace_2357065 : CollatzResearch.WordTrace tailWord_2357065 prefixEnd_2357065 134478586543325078449729 := by
  unfold tailWord_2357065
  simp only [CollatzResearch.WordTrace]
  refine ⟨85969223205763534498096649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57312815470509022998731099 85969223205763534498096649)
  ·
    refine ⟨64476917404322650873572487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85969223205763534498096649 64476917404322650873572487)
    ·
      refine ⟨96715376106483976310358731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64476917404322650873572487 96715376106483976310358731)
      ·
        refine ⟨145073064159725964465538097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96715376106483976310358731 145073064159725964465538097)
        ·
          refine ⟨108804798119794473349153573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145073064159725964465538097 108804798119794473349153573)
          ·
            refine ⟨20400899647461463752966295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108804798119794473349153573 20400899647461463752966295)
            ·
              refine ⟨30601349471192195629449443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20400899647461463752966295 30601349471192195629449443)
              ·
                refine ⟨45902024206788293444174165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30601349471192195629449443 45902024206788293444174165)
                ·
                  refine ⟨134478586543325078449729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 45902024206788293444174165 134478586543325078449729)
                  ·
                    rfl

theorem cell23_2357065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_2357065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357065 prefixEnd_2357065 := by exact prefixLift 2357065
  have htrace : WordTrace (prefixWord ++ tailWord_2357065) baseStart_2357065 baseEnd_2357065 := by
    simpa [prefixWord, tailWord_2357065, baseEnd_2357065] using wordTrace_append hprefix tailTrace_2357065
  have hstable : (prefixWord ++ tailWord_2357065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357065).length < 2 ^ (prefixWord ++ tailWord_2357065).sum := by decide
  have hdescent : baseEnd_2357065 < baseStart_2357065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357082 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 6]
def baseStart_2357082 : Nat := 118140960795 + 2357082 * 2 ^ 59
def prefixEnd_2357082 : Nat := 4983230072969 + 3 ^ 40 * 2357082 * 2
def baseEnd_2357082 : Nat := 134479556451228015503887

theorem tailTrace_2357082 : CollatzResearch.WordTrace tailWord_2357082 prefixEnd_2357082 134479556451228015503887 := by
  unfold tailWord_2357082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21492460811675486600366375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57313228831134630934310333 21492460811675486600366375)
  ·
    refine ⟨32238691217513229900549563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21492460811675486600366375 32238691217513229900549563)
    ·
      refine ⟨48358036826269844850824345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32238691217513229900549563 48358036826269844850824345)
      ·
        refine ⟨36268527619702383638118259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48358036826269844850824345 36268527619702383638118259)
        ·
          refine ⟨54402791429553575457177389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36268527619702383638118259 54402791429553575457177389)
          ·
            refine ⟨20401046786082590796441521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54402791429553575457177389 20401046786082590796441521)
            ·
              refine ⟨15300785089561943097331141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20401046786082590796441521 15300785089561943097331141)
              ·
                refine ⟨2868897204292864330749589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15300785089561943097331141 2868897204292864330749589)
                ·
                  refine ⟨134479556451228015503887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2868897204292864330749589 134479556451228015503887)
                  ·
                    rfl

theorem cell23_2357082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_2357082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357082 prefixEnd_2357082 := by exact prefixLift 2357082
  have htrace : WordTrace (prefixWord ++ tailWord_2357082) baseStart_2357082 baseEnd_2357082 := by
    simpa [prefixWord, tailWord_2357082, baseEnd_2357082] using wordTrace_append hprefix tailTrace_2357082
  have hstable : (prefixWord ++ tailWord_2357082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357082).length < 2 ^ (prefixWord ++ tailWord_2357082).sum := by decide
  have hdescent : baseEnd_2357082 < baseStart_2357082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357143 : List Nat := [1, 1, 3, 3, 1, 4, 1, 4, 1, 1, 3]
def baseStart_2357143 : Nat := 118140960795 + 2357143 * 2 ^ 59
def prefixEnd_2357143 : Nat := 4983230072969 + 3 ^ 40 * 2357143 * 2
def baseEnd_2357143 : Nat := 1210347330380976400872203

theorem tailTrace_2357143 : CollatzResearch.WordTrace tailWord_2357143 prefixEnd_2357143 1210347330380976400872203 := by
  unfold tailWord_2357143
  simp only [CollatzResearch.WordTrace]
  refine ⟨85972068099480953819436083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57314712066320635879624055 85972068099480953819436083)
  ·
    refine ⟨128958102149221430729154125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85972068099480953819436083 128958102149221430729154125)
    ·
      refine ⟨48359288305958036523432797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128958102149221430729154125 48359288305958036523432797)
      ·
        refine ⟨18134733114734263696287299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48359288305958036523432797 18134733114734263696287299)
        ·
          refine ⟨27202099672101395544430949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18134733114734263696287299 27202099672101395544430949)
          ·
            refine ⟨5100393688519011664580803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27202099672101395544430949 5100393688519011664580803)
            ·
              refine ⟨7650590532778517496871205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100393688519011664580803 7650590532778517496871205)
              ·
                refine ⟨1434485724895972030663351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7650590532778517496871205 1434485724895972030663351)
                ·
                  refine ⟨2151728587343958045995027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434485724895972030663351 2151728587343958045995027)
                  ·
                    refine ⟨3227592881015937068992541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2151728587343958045995027 3227592881015937068992541)
                    ·
                      refine ⟨1210347330380976400872203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3227592881015937068992541 1210347330380976400872203)
                      ·
                        rfl

theorem cell23_2357143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_2357143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357143 prefixEnd_2357143 := by exact prefixLift 2357143
  have htrace : WordTrace (prefixWord ++ tailWord_2357143) baseStart_2357143 baseEnd_2357143 := by
    simpa [prefixWord, tailWord_2357143, baseEnd_2357143] using wordTrace_append hprefix tailTrace_2357143
  have hstable : (prefixWord ++ tailWord_2357143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357143).length < 2 ^ (prefixWord ++ tailWord_2357143).sum := by decide
  have hdescent : baseEnd_2357143 < baseStart_2357143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357149 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2357149 : Nat := 118140960795 + 2357149 * 2 ^ 59
def prefixEnd_2357149 : Nat := 4983230072969 + 3 ^ 40 * 2357149 * 2
def baseEnd_2357149 : Nat := 1210350411264903377397175

theorem tailTrace_2357149 : CollatzResearch.WordTrace tailWord_2357149 prefixEnd_2357149 1210350411264903377397175 := by
  unfold tailWord_2357149
  simp only [CollatzResearch.WordTrace]
  refine ⟨85972286937459216844154501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57314857958306144562769667 85972286937459216844154501)
  ·
    refine ⟨16119803800773603158278969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85972286937459216844154501 16119803800773603158278969)
    ·
      refine ⟨12089852850580202368709227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16119803800773603158278969 12089852850580202368709227)
      ·
        refine ⟨18134779275870303553063841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12089852850580202368709227 18134779275870303553063841)
        ·
          refine ⟨13601084456902727664797881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18134779275870303553063841 13601084456902727664797881)
          ·
            refine ⟨10200813342677045748598411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13601084456902727664797881 10200813342677045748598411)
            ·
              refine ⟨15301220014015568622897617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10200813342677045748598411 15301220014015568622897617)
              ·
                refine ⟨11475915010511676467173213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15301220014015568622897617 11475915010511676467173213)
                ·
                  refine ⟨4303468128941878675189955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11475915010511676467173213 4303468128941878675189955)
                  ·
                    refine ⟨6455202193412818012784933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4303468128941878675189955 6455202193412818012784933)
                    ·
                      refine ⟨1210350411264903377397175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6455202193412818012784933 1210350411264903377397175)
                      ·
                        rfl

theorem cell23_2357149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2357149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357149 prefixEnd_2357149 := by exact prefixLift 2357149
  have htrace : WordTrace (prefixWord ++ tailWord_2357149) baseStart_2357149 baseEnd_2357149 := by
    simpa [prefixWord, tailWord_2357149, baseEnd_2357149] using wordTrace_append hprefix tailTrace_2357149
  have hstable : (prefixWord ++ tailWord_2357149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357149).length < 2 ^ (prefixWord ++ tailWord_2357149).sum := by decide
  have hdescent : baseEnd_2357149 < baseStart_2357149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357152 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2357152 : Nat := 118140960795 + 2357152 * 2 ^ 59
def prefixEnd_2357152 : Nat := 4983230072969 + 3 ^ 40 * 2357152 * 2
def baseEnd_2357152 : Nat := 1210351951706866865659661

theorem tailTrace_2357152 : CollatzResearch.WordTrace tailWord_2357152 prefixEnd_2357152 1210351951706866865659661 := by
  unfold tailWord_2357152
  simp only [CollatzResearch.WordTrace]
  refine ⟨42986198178224174178256855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57314930904298898904342473 42986198178224174178256855)
  ·
    refine ⟨64479297267336261267385283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42986198178224174178256855 64479297267336261267385283)
    ·
      refine ⟨96718945901004391901077925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64479297267336261267385283 96718945901004391901077925)
      ·
        refine ⟨18134802356438323481452111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96718945901004391901077925 18134802356438323481452111)
        ·
          refine ⟨27202203534657485222178167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18134802356438323481452111 27202203534657485222178167)
          ·
            refine ⟨40803305301986227833267251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27202203534657485222178167 40803305301986227833267251)
            ·
              refine ⟨61204957952979341749900877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40803305301986227833267251 61204957952979341749900877)
              ·
                refine ⟨22951859232367253156212829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61204957952979341749900877 22951859232367253156212829)
                ·
                  refine ⟨8606947212137719933579811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22951859232367253156212829 8606947212137719933579811)
                  ·
                    refine ⟨12910420818206579900369717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8606947212137719933579811 12910420818206579900369717)
                    ·
                      refine ⟨1210351951706866865659661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12910420818206579900369717 1210351951706866865659661)
                      ·
                        rfl

theorem cell23_2357152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2357152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357152 prefixEnd_2357152 := by exact prefixLift 2357152
  have htrace : WordTrace (prefixWord ++ tailWord_2357152) baseStart_2357152 baseEnd_2357152 := by
    simpa [prefixWord, tailWord_2357152, baseEnd_2357152] using wordTrace_append hprefix tailTrace_2357152
  have hstable : (prefixWord ++ tailWord_2357152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357152).length < 2 ^ (prefixWord ++ tailWord_2357152).sum := by decide
  have hdescent : baseEnd_2357152 < baseStart_2357152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357159 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2357159 : Nat := 118140960795 + 2357159 * 2 ^ 59
def prefixEnd_2357159 : Nat := 4983230072969 + 3 ^ 40 * 2357159 * 2
def baseEnd_2357159 : Nat := 403451848690482779424043

theorem tailTrace_2357159 : CollatzResearch.WordTrace tailWord_2357159 prefixEnd_2357159 403451848690482779424043 := by
  unfold tailWord_2357159
  simp only [CollatzResearch.WordTrace]
  refine ⟨85972651667422988552018531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57315101111615325701345687 85972651667422988552018531)
  ·
    refine ⟨128958977501134482828027797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85972651667422988552018531 128958977501134482828027797)
    ·
      refine ⟨6044952070365678882563803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128958977501134482828027797 6044952070365678882563803)
      ·
        refine ⟨9067428105548518323845705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6044952070365678882563803 9067428105548518323845705)
        ·
          refine ⟨6800571079161388742884279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9067428105548518323845705 6800571079161388742884279)
          ·
            refine ⟨10200856618742083114326419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6800571079161388742884279 10200856618742083114326419)
            ·
              refine ⟨15301284928113124671489629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10200856618742083114326419 15301284928113124671489629)
              ·
                refine ⟨5737981848042421751808611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15301284928113124671489629 5737981848042421751808611)
                ·
                  refine ⟨8606972772063632627712917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5737981848042421751808611 8606972772063632627712917)
                  ·
                    refine ⟨403451848690482779424043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8606972772063632627712917 403451848690482779424043)
                    ·
                      rfl

theorem cell23_2357159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2357159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357159 prefixEnd_2357159 := by exact prefixLift 2357159
  have htrace : WordTrace (prefixWord ++ tailWord_2357159) baseStart_2357159 baseEnd_2357159 := by
    simpa [prefixWord, tailWord_2357159, baseEnd_2357159] using wordTrace_append hprefix tailTrace_2357159
  have hstable : (prefixWord ++ tailWord_2357159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357159).length < 2 ^ (prefixWord ++ tailWord_2357159).sum := by decide
  have hdescent : baseEnd_2357159 < baseStart_2357159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357160 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2357160 : Nat := 118140960795 + 2357160 * 2 ^ 59
def prefixEnd_2357160 : Nat := 4983230072969 + 3 ^ 40 * 2357160 * 2
def baseEnd_2357160 : Nat := 1210356059552102834359625

theorem tailTrace_2357160 : CollatzResearch.WordTrace tailWord_2357160 prefixEnd_2357160 1210356059552102834359625 := by
  unfold tailWord_2357160
  simp only [CollatzResearch.WordTrace]
  refine ⟨42986344070209682861402467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57315125426946243815203289 42986344070209682861402467)
  ·
    refine ⟨64479516105314524292103701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42986344070209682861402467 64479516105314524292103701)
    ·
      refine ⟨3022477317436618326192361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64479516105314524292103701 3022477317436618326192361)
      ·
        refine ⟨2266857988077463744644271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3022477317436618326192361 2266857988077463744644271)
        ·
          refine ⟨3400286982116195616966407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266857988077463744644271 3400286982116195616966407)
          ·
            refine ⟨5100430473174293425449611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400286982116195616966407 5100430473174293425449611)
            ·
              refine ⟨7650645709761440138174417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100430473174293425449611 7650645709761440138174417)
              ·
                refine ⟨5737984282321080103630813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7650645709761440138174417 5737984282321080103630813)
                ·
                  refine ⟨2151744105870405038861555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5737984282321080103630813 2151744105870405038861555)
                  ·
                    refine ⟨3227616158805607558292333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2151744105870405038861555 3227616158805607558292333)
                    ·
                      refine ⟨1210356059552102834359625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3227616158805607558292333 1210356059552102834359625)
                      ·
                        rfl

theorem cell23_2357160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2357160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357160 prefixEnd_2357160 := by exact prefixLift 2357160
  have htrace : WordTrace (prefixWord ++ tailWord_2357160) baseStart_2357160 baseEnd_2357160 := by
    simpa [prefixWord, tailWord_2357160, baseEnd_2357160] using wordTrace_append hprefix tailTrace_2357160
  have hstable : (prefixWord ++ tailWord_2357160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357160).length < 2 ^ (prefixWord ++ tailWord_2357160).sum := by decide
  have hdescent : baseEnd_2357160 < baseStart_2357160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357180 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_2357180 : Nat := 118140960795 + 2357180 * 2 ^ 59
def prefixEnd_2357180 : Nat := 4983230072969 + 3 ^ 40 * 2357180 * 2
def baseEnd_2357180 : Nat := 403455443055064252036511

theorem tailTrace_2357180 : CollatzResearch.WordTrace tailWord_2357180 prefixEnd_2357180 403455443055064252036511 := by
  unfold tailWord_2357180
  simp only [CollatzResearch.WordTrace]
  refine ⟨42986708800173454569266497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57315611733564606092355329 42986708800173454569266497)
  ·
    refine ⟨32240031600130090926949873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42986708800173454569266497 32240031600130090926949873)
    ·
      refine ⟨24180023700097568195212405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32240031600130090926949873 24180023700097568195212405)
      ·
        refine ⟨2266877221884147018301163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24180023700097568195212405 2266877221884147018301163)
        ·
          refine ⟨3400315832826220527451745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266877221884147018301163 3400315832826220527451745)
          ·
            refine ⟨2550236874619665395588809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400315832826220527451745 2550236874619665395588809)
            ·
              refine ⟨1912677655964749046691607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550236874619665395588809 1912677655964749046691607)
              ·
                refine ⟨2869016483947123570037411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912677655964749046691607 2869016483947123570037411)
                ·
                  refine ⟨4303524725920685355056117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869016483947123570037411 4303524725920685355056117)
                  ·
                    refine ⟨403455443055064252036511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4303524725920685355056117 403455443055064252036511)
                    ·
                      rfl

theorem cell23_2357180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_2357180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357180 prefixEnd_2357180 := by exact prefixLift 2357180
  have htrace : WordTrace (prefixWord ++ tailWord_2357180) baseStart_2357180 baseEnd_2357180 := by
    simpa [prefixWord, tailWord_2357180, baseEnd_2357180] using wordTrace_append hprefix tailTrace_2357180
  have hstable : (prefixWord ++ tailWord_2357180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357180).length < 2 ^ (prefixWord ++ tailWord_2357180).sum := by decide
  have hdescent : baseEnd_2357180 < baseStart_2357180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357213 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_2357213 : Nat := 118140960795 + 2357213 * 2 ^ 59
def prefixEnd_2357213 : Nat := 4983230072969 + 3 ^ 40 * 2357213 * 2
def baseEnd_2357213 : Nat := 1210383274026791126996881

theorem tailTrace_2357213 : CollatzResearch.WordTrace tailWord_2357213 prefixEnd_2357213 1210383274026791126996881 := by
  unfold tailWord_2357213
  simp only [CollatzResearch.WordTrace]
  refine ⟨85974621209227355774484293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57316414139484903849656195 85974621209227355774484293)
  ·
    refine ⟨16120241476730129207715805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85974621209227355774484293 16120241476730129207715805)
    ·
      refine ⟨6045090553773798452893427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16120241476730129207715805 6045090553773798452893427)
      ·
        refine ⟨9067635830660697679340141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6045090553773798452893427 9067635830660697679340141)
        ·
          refine ⟨3400363436497761629752553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9067635830660697679340141 3400363436497761629752553)
          ·
            refine ⟨2550272577373321222314415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400363436497761629752553 2550272577373321222314415)
            ·
              refine ⟨3825408866059981833471623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550272577373321222314415 3825408866059981833471623)
              ·
                refine ⟨5738113299089972750207435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825408866059981833471623 5738113299089972750207435)
                ·
                  refine ⟨8607169948634959125311153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5738113299089972750207435 8607169948634959125311153)
                  ·
                    refine ⟨6455377461476219343983365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8607169948634959125311153 6455377461476219343983365)
                    ·
                      refine ⟨1210383274026791126996881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6455377461476219343983365 1210383274026791126996881)
                      ·
                        rfl

theorem cell23_2357213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_2357213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357213 prefixEnd_2357213 := by exact prefixLift 2357213
  have htrace : WordTrace (prefixWord ++ tailWord_2357213) baseStart_2357213 baseEnd_2357213 := by
    simpa [prefixWord, tailWord_2357213, baseEnd_2357213] using wordTrace_append hprefix tailTrace_2357213
  have hstable : (prefixWord ++ tailWord_2357213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357213).length < 2 ^ (prefixWord ++ tailWord_2357213).sum := by decide
  have hdescent : baseEnd_2357213 < baseStart_2357213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357216 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 2, 1, 3]
def baseStart_2357216 : Nat := 118140960795 + 2357216 * 2 ^ 59
def prefixEnd_2357216 : Nat := 4983230072969 + 3 ^ 40 * 2357216 * 2
def baseEnd_2357216 : Nat := 1210384814468754615259367

theorem tailTrace_2357216 : CollatzResearch.WordTrace tailWord_2357216 prefixEnd_2357216 1210384814468754615259367 := by
  unfold tailWord_2357216
  simp only [CollatzResearch.WordTrace]
  refine ⟨42987365314108243643421751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57316487085477658191229001 42987365314108243643421751)
  ·
    refine ⟨64481047971162365465132627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42987365314108243643421751 64481047971162365465132627)
    ·
      refine ⟨96721571956743548197698941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64481047971162365465132627 96721571956743548197698941)
      ·
        refine ⟨36270589483778830574137103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96721571956743548197698941 36270589483778830574137103)
        ·
          refine ⟨54405884225668245861205655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36270589483778830574137103 54405884225668245861205655)
          ·
            refine ⟨81608826338502368791808483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54405884225668245861205655 81608826338502368791808483)
            ·
              refine ⟨122413239507753553187712725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81608826338502368791808483 122413239507753553187712725)
              ·
                refine ⟨2869060300962973902837017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122413239507753553187712725 2869060300962973902837017)
                ·
                  refine ⟨2151795225722230427127763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2869060300962973902837017 2151795225722230427127763)
                  ·
                    refine ⟨3227692838583345640691645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2151795225722230427127763 3227692838583345640691645)
                    ·
                      refine ⟨1210384814468754615259367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3227692838583345640691645 1210384814468754615259367)
                      ·
                        rfl

theorem cell23_2357216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_2357216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357216 prefixEnd_2357216 := by exact prefixLift 2357216
  have htrace : WordTrace (prefixWord ++ tailWord_2357216) baseStart_2357216 baseEnd_2357216 := by
    simpa [prefixWord, tailWord_2357216, baseEnd_2357216] using wordTrace_append hprefix tailTrace_2357216
  have hstable : (prefixWord ++ tailWord_2357216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357216).length < 2 ^ (prefixWord ++ tailWord_2357216).sum := by decide
  have hdescent : baseEnd_2357216 < baseStart_2357216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357223 : List Nat := [1, 1, 5, 2, 4, 1, 2, 7]
def baseStart_2357223 : Nat := 118140960795 + 2357223 * 2 ^ 59
def prefixEnd_2357223 : Nat := 4983230072969 + 3 ^ 40 * 2357223 * 2
def baseEnd_2357223 : Nat := 44829200327160595847105

theorem tailTrace_2357223 : CollatzResearch.WordTrace tailWord_2357223 prefixEnd_2357223 44829200327160595847105 := by
  unfold tailWord_2357223
  simp only [CollatzResearch.WordTrace]
  refine ⟨85974985939191127482348323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57316657292794084988232215 85974985939191127482348323)
  ·
    refine ⟨128962478908786691223522485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85974985939191127482348323 128962478908786691223522485)
    ·
      refine ⟨12090232397698752302205233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128962478908786691223522485 12090232397698752302205233)
      ·
        refine ⟨9067674298274064226653925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12090232397698752302205233 9067674298274064226653925)
        ·
          refine ⟨1700188930926387042497611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9067674298274064226653925 1700188930926387042497611)
          ·
            refine ⟨2550283396389580563746417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700188930926387042497611 2550283396389580563746417)
            ·
              refine ⟨1912712547292185422809813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550283396389580563746417 1912712547292185422809813)
              ·
                refine ⟨44829200327160595847105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1912712547292185422809813 44829200327160595847105)
                ·
                  rfl

theorem cell23_2357223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 7].length) (baseStart_2357223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357223 prefixEnd_2357223 := by exact prefixLift 2357223
  have htrace : WordTrace (prefixWord ++ tailWord_2357223) baseStart_2357223 baseEnd_2357223 := by
    simpa [prefixWord, tailWord_2357223, baseEnd_2357223] using wordTrace_append hprefix tailTrace_2357223
  have hstable : (prefixWord ++ tailWord_2357223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357223).length < 2 ^ (prefixWord ++ tailWord_2357223).sum := by decide
  have hdescent : baseEnd_2357223 < baseStart_2357223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357232 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 1, 8]
def baseStart_2357232 : Nat := 118140960795 + 2357232 * 2 ^ 59
def prefixEnd_2357232 : Nat := 4983230072969 + 3 ^ 40 * 2357232 * 2
def baseEnd_2357232 : Nat := 403464343386408850886431

theorem tailTrace_2357232 : CollatzResearch.WordTrace tailWord_2357232 prefixEnd_2357232 403464343386408850886431 := by
  unfold tailWord_2357232
  simp only [CollatzResearch.WordTrace]
  refine ⟨42987657098079261009712975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57316876130772348012950633 42987657098079261009712975)
  ·
    refine ⟨64481485647118891514569463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42987657098079261009712975 64481485647118891514569463)
    ·
      refine ⟨96722228470678337271854195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64481485647118891514569463 96722228470678337271854195)
      ·
        refine ⟨145083342706017505907781293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96722228470678337271854195 145083342706017505907781293)
        ·
          refine ⟨54406253514756564715417985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145083342706017505907781293 54406253514756564715417985)
          ·
            refine ⟨40804690136067423536563489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54406253514756564715417985 40804690136067423536563489)
            ·
              refine ⟨30603517602050567652422617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40804690136067423536563489 30603517602050567652422617)
              ·
                refine ⟨22952638201537925739316963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30603517602050567652422617 22952638201537925739316963)
                ·
                  refine ⟨34428957302306888608975445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22952638201537925739316963 34428957302306888608975445)
                  ·
                    refine ⟨403464343386408850886431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34428957302306888608975445 403464343386408850886431)
                    ·
                      rfl

theorem cell23_2357232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_2357232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357232 prefixEnd_2357232 := by exact prefixLift 2357232
  have htrace : WordTrace (prefixWord ++ tailWord_2357232) baseStart_2357232 baseEnd_2357232 := by
    simpa [prefixWord, tailWord_2357232, baseEnd_2357232] using wordTrace_append hprefix tailTrace_2357232
  have hstable : (prefixWord ++ tailWord_2357232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357232).length < 2 ^ (prefixWord ++ tailWord_2357232).sum := by decide
  have hdescent : baseEnd_2357232 < baseStart_2357232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357259 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 3]
def baseStart_2357259 : Nat := 118140960795 + 2357259 * 2 ^ 59
def prefixEnd_2357259 : Nat := 4983230072969 + 3 ^ 40 * 2357259 * 2
def baseEnd_2357259 : Nat := 1210406894136897947021669

theorem tailTrace_2357259 : CollatzResearch.WordTrace tailWord_2357259 prefixEnd_2357259 1210406894136897947021669 := by
  unfold tailWord_2357259
  simp only [CollatzResearch.WordTrace]
  refine ⟨85976298967060705630658831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57317532644707137087105887 85976298967060705630658831)
  ·
    refine ⟨128964448450591058445988247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85976298967060705630658831 128964448450591058445988247)
    ·
      refine ⟨193446672675886587668982371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128964448450591058445988247 193446672675886587668982371)
      ·
        refine ⟨290170009013829881503473557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193446672675886587668982371 290170009013829881503473557)
        ·
          refine ⟨13601719172523275695475323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 290170009013829881503473557 13601719172523275695475323)
          ·
            refine ⟨20402578758784913543212985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13601719172523275695475323 20402578758784913543212985)
            ·
              refine ⟨15301934069088685157409739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20402578758784913543212985 15301934069088685157409739)
              ·
                refine ⟨22952901103633027736114609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15301934069088685157409739 22952901103633027736114609)
                ·
                  refine ⟨17214675827724770802085957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22952901103633027736114609 17214675827724770802085957)
                  ·
                    refine ⟨3227751717698394525391117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17214675827724770802085957 3227751717698394525391117)
                    ·
                      refine ⟨1210406894136897947021669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3227751717698394525391117 1210406894136897947021669)
                      ·
                        rfl

theorem cell23_2357259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 3].length) (baseStart_2357259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357259 prefixEnd_2357259 := by exact prefixLift 2357259
  have htrace : WordTrace (prefixWord ++ tailWord_2357259) baseStart_2357259 baseEnd_2357259 := by
    simpa [prefixWord, tailWord_2357259, baseEnd_2357259] using wordTrace_append hprefix tailTrace_2357259
  have hstable : (prefixWord ++ tailWord_2357259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357259).length < 2 ^ (prefixWord ++ tailWord_2357259).sum := by decide
  have hdescent : baseEnd_2357259 < baseStart_2357259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357261 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2357261 : Nat := 118140960795 + 2357261 * 2 ^ 59
def prefixEnd_2357261 : Nat := 4983230072969 + 3 ^ 40 * 2357261 * 2
def baseEnd_2357261 : Nat := 403469307032735646398887

theorem tailTrace_2357261 : CollatzResearch.WordTrace tailWord_2357261 prefixEnd_2357261 403469307032735646398887 := by
  unfold tailWord_2357261
  simp only [CollatzResearch.WordTrace]
  refine ⟨85976371913053459972231637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57317581275368973314821091 85976371913053459972231637)
  ·
    refine ⟨2015071216712190468099179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 85976371913053459972231637 2015071216712190468099179)
    ·
      refine ⟨3022606825068285702148769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015071216712190468099179 3022606825068285702148769)
      ·
        refine ⟨2266955118801214276611577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3022606825068285702148769 2266955118801214276611577)
        ·
          refine ⟨1700216339100910707458683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2266955118801214276611577 1700216339100910707458683)
          ·
            refine ⟨2550324508651366061188025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700216339100910707458683 2550324508651366061188025)
            ·
              refine ⟨1912743381488524545891019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550324508651366061188025 1912743381488524545891019)
              ·
                refine ⟨2869115072232786818836529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912743381488524545891019 2869115072232786818836529)
                ·
                  refine ⟨2151836304174590114127397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2869115072232786818836529 2151836304174590114127397)
                  ·
                    refine ⟨403469307032735646398887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151836304174590114127397 403469307032735646398887)
                    ·
                      rfl

theorem cell23_2357261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2357261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357261 prefixEnd_2357261 := by exact prefixLift 2357261
  have htrace : WordTrace (prefixWord ++ tailWord_2357261) baseStart_2357261 baseEnd_2357261 := by
    simpa [prefixWord, tailWord_2357261, baseEnd_2357261] using wordTrace_append hprefix tailTrace_2357261
  have hstable : (prefixWord ++ tailWord_2357261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357261).length < 2 ^ (prefixWord ++ tailWord_2357261).sum := by decide
  have hdescent : baseEnd_2357261 < baseStart_2357261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357313 : List Nat := [1, 2, 5, 1, 2, 2, 1, 4, 5]
def baseStart_2357313 : Nat := 118140960795 + 2357313 * 2 ^ 59
def prefixEnd_2357313 : Nat := 4983230072969 + 3 ^ 40 * 2357313 * 2
def baseEnd_2357313 : Nat := 134492735788026748416269

theorem tailTrace_2357313 : CollatzResearch.WordTrace tailWord_2357313 prefixEnd_2357313 134492735788026748416269 := by
  unfold tailWord_2357313
  simp only [CollatzResearch.WordTrace]
  refine ⟨85978268508865072853124593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57318845672576715235416395 85978268508865072853124593)
  ·
    refine ⟨64483701381648804639843445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85978268508865072853124593 64483701381648804639843445)
    ·
      refine ⟨6045347004529575434985323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64483701381648804639843445 6045347004529575434985323)
      ·
        refine ⟨9068020506794363152477985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6045347004529575434985323 9068020506794363152477985)
        ·
          refine ⟨6801015380095772364358489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9068020506794363152477985 6801015380095772364358489)
          ·
            refine ⟨5100761535071829273268867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6801015380095772364358489 5100761535071829273268867)
            ·
              refine ⟨7651142302607743909903301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100761535071829273268867 7651142302607743909903301)
              ·
                refine ⟨1434589181738951983106869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7651142302607743909903301 1434589181738951983106869)
                ·
                  refine ⟨134492735788026748416269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1434589181738951983106869 134492735788026748416269)
                  ·
                    rfl

theorem cell23_2357313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 5].length) (baseStart_2357313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357313 prefixEnd_2357313 := by exact prefixLift 2357313
  have htrace : WordTrace (prefixWord ++ tailWord_2357313) baseStart_2357313 baseEnd_2357313 := by
    simpa [prefixWord, tailWord_2357313, baseEnd_2357313] using wordTrace_append hprefix tailTrace_2357313
  have hstable : (prefixWord ++ tailWord_2357313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357313).length < 2 ^ (prefixWord ++ tailWord_2357313).sum := by decide
  have hdescent : baseEnd_2357313 < baseStart_2357313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357319 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_2357319 : Nat := 118140960795 + 2357319 * 2 ^ 59
def prefixEnd_2357319 : Nat := 4983230072969 + 3 ^ 40 * 2357319 * 2
def baseEnd_2357319 : Nat := 1210437702976167712271393

theorem tailTrace_2357319 : CollatzResearch.WordTrace tailWord_2357319 prefixEnd_2357319 1210437702976167712271393 := by
  unfold tailWord_2357319
  simp only [CollatzResearch.WordTrace]
  refine ⟨85978487346843335877843011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57318991564562223918562007 85978487346843335877843011)
  ·
    refine ⟨128967731020265003816764517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85978487346843335877843011 128967731020265003816764517)
    ·
      refine ⟨24181449566299688215643347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128967731020265003816764517 24181449566299688215643347)
      ·
        refine ⟨36272174349449532323465021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24181449566299688215643347 36272174349449532323465021)
        ·
          refine ⟨13602065381043574621299383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36272174349449532323465021 13602065381043574621299383)
          ·
            refine ⟨20403098071565361931949075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13602065381043574621299383 20403098071565361931949075)
            ·
              refine ⟨30604647107348042897923613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20403098071565361931949075 30604647107348042897923613)
              ·
                refine ⟨11476742665255516086721355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30604647107348042897923613 11476742665255516086721355)
                ·
                  refine ⟨17215113997883274130082033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11476742665255516086721355 17215113997883274130082033)
                  ·
                    refine ⟨12911335498412455597561525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17215113997883274130082033 12911335498412455597561525)
                    ·
                      refine ⟨1210437702976167712271393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12911335498412455597561525 1210437702976167712271393)
                      ·
                        rfl

theorem cell23_2357319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_2357319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357319 prefixEnd_2357319 := by exact prefixLift 2357319
  have htrace : WordTrace (prefixWord ++ tailWord_2357319) baseStart_2357319 baseEnd_2357319 := by
    simpa [prefixWord, tailWord_2357319, baseEnd_2357319] using wordTrace_append hprefix tailTrace_2357319
  have hstable : (prefixWord ++ tailWord_2357319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357319).length < 2 ^ (prefixWord ++ tailWord_2357319).sum := by decide
  have hdescent : baseEnd_2357319 < baseStart_2357319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357329 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_2357329 : Nat := 118140960795 + 2357329 * 2 ^ 59
def prefixEnd_2357329 : Nat := 4983230072969 + 3 ^ 40 * 2357329 * 2
def baseEnd_2357329 : Nat := 1210442837782712673146347

theorem tailTrace_2357329 : CollatzResearch.WordTrace tailWord_2357329 prefixEnd_2357329 1210442837782712673146347 := by
  unfold tailWord_2357329
  simp only [CollatzResearch.WordTrace]
  refine ⟨85978852076807107585707041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57319234717871405057138027 85978852076807107585707041)
  ·
    refine ⟨64484139057605330689280281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85978852076807107585707041 64484139057605330689280281)
    ·
      refine ⟨48363104293203998016960211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64484139057605330689280281 48363104293203998016960211)
      ·
        refine ⟨72544656439805997025440317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48363104293203998016960211 72544656439805997025440317)
        ·
          refine ⟨27204246164927248884540119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72544656439805997025440317 27204246164927248884540119)
          ·
            refine ⟨40806369247390873326810179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27204246164927248884540119 40806369247390873326810179)
            ·
              refine ⟨61209553871086309990215269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40806369247390873326810179 61209553871086309990215269)
              ·
                refine ⟨11476791350828683123165363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61209553871086309990215269 11476791350828683123165363)
                ·
                  refine ⟨17215187026243024684748045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11476791350828683123165363 17215187026243024684748045)
                  ·
                    refine ⟨6455695134841134256780517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17215187026243024684748045 6455695134841134256780517)
                    ·
                      refine ⟨1210442837782712673146347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6455695134841134256780517 1210442837782712673146347)
                      ·
                        rfl

theorem cell23_2357329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_2357329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357329 prefixEnd_2357329 := by exact prefixLift 2357329
  have htrace : WordTrace (prefixWord ++ tailWord_2357329) baseStart_2357329 baseEnd_2357329 := by
    simpa [prefixWord, tailWord_2357329, baseEnd_2357329] using wordTrace_append hprefix tailTrace_2357329
  have hstable : (prefixWord ++ tailWord_2357329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357329).length < 2 ^ (prefixWord ++ tailWord_2357329).sum := by decide
  have hdescent : baseEnd_2357329 < baseStart_2357329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357359 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_2357359 : Nat := 118140960795 + 2357359 * 2 ^ 59
def prefixEnd_2357359 : Nat := 4983230072969 + 3 ^ 40 * 2357359 * 2
def baseEnd_2357359 : Nat := 1210458242202347555771209

theorem tailTrace_2357359 : CollatzResearch.WordTrace tailWord_2357359 prefixEnd_2357359 1210458242202347555771209 := by
  unfold tailWord_2357359
  simp only [CollatzResearch.WordTrace]
  refine ⟨85979946266698422709299131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57319964177798948472866087 85979946266698422709299131)
  ·
    refine ⟨128969919400047634063948697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85979946266698422709299131 128969919400047634063948697)
    ·
      refine ⟨96727439550035725547961523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128969919400047634063948697 96727439550035725547961523)
      ·
        refine ⟨145091159325053588321942285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96727439550035725547961523 145091159325053588321942285)
        ·
          refine ⟨54409184746895095620728357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145091159325053588321942285 54409184746895095620728357)
          ·
            refine ⟨10201722140042830428886567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54409184746895095620728357 10201722140042830428886567)
            ·
              refine ⟨15302583210064245643329851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10201722140042830428886567 15302583210064245643329851)
              ·
                refine ⟨22953874815096368464994777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15302583210064245643329851 22953874815096368464994777)
                ·
                  refine ⟨17215406111322276348746083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22953874815096368464994777 17215406111322276348746083)
                  ·
                    refine ⟨25823109166983414523119125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17215406111322276348746083 25823109166983414523119125)
                    ·
                      refine ⟨1210458242202347555771209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25823109166983414523119125 1210458242202347555771209)
                      ·
                        rfl

theorem cell23_2357359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_2357359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357359 prefixEnd_2357359 := by exact prefixLift 2357359
  have htrace : WordTrace (prefixWord ++ tailWord_2357359) baseStart_2357359 baseEnd_2357359 := by
    simpa [prefixWord, tailWord_2357359, baseEnd_2357359] using wordTrace_append hprefix tailTrace_2357359
  have hstable : (prefixWord ++ tailWord_2357359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357359).length < 2 ^ (prefixWord ++ tailWord_2357359).sum := by decide
  have hdescent : baseEnd_2357359 < baseStart_2357359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357373 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_2357373 : Nat := 118140960795 + 2357373 * 2 ^ 59
def prefixEnd_2357373 : Nat := 4983230072969 + 3 ^ 40 * 2357373 * 2
def baseEnd_2357373 : Nat := 403488476977170166998715

theorem tailTrace_2357373 : CollatzResearch.WordTrace tailWord_2357373 prefixEnd_2357373 403488476977170166998715 := by
  unfold tailWord_2357373
  simp only [CollatzResearch.WordTrace]
  refine ⟨85980456888647703100308773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57320304592431802066872515 85980456888647703100308773)
  ·
    refine ⟨16121335666621444331307895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85980456888647703100308773 16121335666621444331307895)
    ·
      refine ⟨24182003499932166496961843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16121335666621444331307895 24182003499932166496961843)
      ·
        refine ⟨36273005249898249745442765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24182003499932166496961843 36273005249898249745442765)
        ·
          refine ⟨13602376968711843654541037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36273005249898249745442765 13602376968711843654541037)
          ·
            refine ⟨5100891363266941370452889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13602376968711843654541037 5100891363266941370452889)
            ·
              refine ⟨3825668522450206027839667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5100891363266941370452889 3825668522450206027839667)
              ·
                refine ⟨5738502783675309041759501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825668522450206027839667 5738502783675309041759501)
                ·
                  refine ⟨2151938543878240890659813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5738502783675309041759501 2151938543878240890659813)
                  ·
                    refine ⟨403488476977170166998715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151938543878240890659813 403488476977170166998715)
                    ·
                      rfl

theorem cell23_2357373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_2357373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357373 prefixEnd_2357373 := by exact prefixLift 2357373
  have htrace : WordTrace (prefixWord ++ tailWord_2357373) baseStart_2357373 baseEnd_2357373 := by
    simpa [prefixWord, tailWord_2357373, baseEnd_2357373] using wordTrace_append hprefix tailTrace_2357373
  have hstable : (prefixWord ++ tailWord_2357373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357373).length < 2 ^ (prefixWord ++ tailWord_2357373).sum := by decide
  have hdescent : baseEnd_2357373 < baseStart_2357373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357398 : List Nat := [5, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2357398 : Nat := 118140960795 + 2357398 * 2 ^ 59
def prefixEnd_2357398 : Nat := 4983230072969 + 3 ^ 40 * 2357398 * 2
def baseEnd_2357398 : Nat := 134497585327541433687059

theorem tailTrace_2357398 : CollatzResearch.WordTrace tailWord_2357398 prefixEnd_2357398 134497585327541433687059 := by
  unfold tailWord_2357398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5373835544597320773123053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57320912475704754913312565 5373835544597320773123053)
  ·
    refine ⟨2015188329223995289921145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5373835544597320773123053 2015188329223995289921145)
    ·
      refine ⟨1511391246917996467440859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2015188329223995289921145 1511391246917996467440859)
      ·
        refine ⟨2267086870376994701161289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511391246917996467440859 2267086870376994701161289)
        ·
          refine ⟨1700315152782746025870967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2267086870376994701161289 1700315152782746025870967)
          ·
            refine ⟨2550472729174119038806451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700315152782746025870967 2550472729174119038806451)
            ·
              refine ⟨3825709093761178558209677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550472729174119038806451 3825709093761178558209677)
              ·
                refine ⟨1434640910160441959328629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3825709093761178558209677 1434640910160441959328629)
                ·
                  refine ⟨134497585327541433687059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1434640910160441959328629 134497585327541433687059)
                  ·
                    rfl

theorem cell23_2357398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2357398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357398 prefixEnd_2357398 := by exact prefixLift 2357398
  have htrace : WordTrace (prefixWord ++ tailWord_2357398) baseStart_2357398 baseEnd_2357398 := by
    simpa [prefixWord, tailWord_2357398, baseEnd_2357398] using wordTrace_append hprefix tailTrace_2357398
  have hstable : (prefixWord ++ tailWord_2357398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357398).length < 2 ^ (prefixWord ++ tailWord_2357398).sum := by decide
  have hdescent : baseEnd_2357398 < baseStart_2357398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357407 : List Nat := [1, 1, 2, 6, 1, 3, 1, 3, 1, 4]
def baseStart_2357407 : Nat := 118140960795 + 2357407 * 2 ^ 59
def prefixEnd_2357407 : Nat := 4983230072969 + 3 ^ 40 * 2357407 * 2
def baseEnd_2357407 : Nat := 403494296424587789323663

theorem tailTrace_2357407 : CollatzResearch.WordTrace tailWord_2357407 prefixEnd_2357407 403494296424587789323663 := by
  unfold tailWord_2357407
  simp only [CollatzResearch.WordTrace]
  refine ⟨85981696970524526907046475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57321131313683017938030983 85981696970524526907046475)
  ·
    refine ⟨128972545455786790360569713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85981696970524526907046475 128972545455786790360569713)
    ·
      refine ⟨96729409091840092770427285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128972545455786790360569713 96729409091840092770427285)
      ·
        refine ⟨4534191051180004348613779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96729409091840092770427285 4534191051180004348613779)
        ·
          refine ⟨6801286576770006522920669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534191051180004348613779 6801286576770006522920669)
          ·
            refine ⟨2550482466288752446095251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6801286576770006522920669 2550482466288752446095251)
            ·
              refine ⟨3825723699433128669142877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550482466288752446095251 3825723699433128669142877)
              ·
                refine ⟨1434646387287423250928579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3825723699433128669142877 1434646387287423250928579)
                ·
                  refine ⟨2151969580931134876392869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434646387287423250928579 2151969580931134876392869)
                  ·
                    refine ⟨403494296424587789323663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151969580931134876392869 403494296424587789323663)
                    ·
                      rfl

theorem cell23_2357407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 4].length) (baseStart_2357407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357407 prefixEnd_2357407 := by exact prefixLift 2357407
  have htrace : WordTrace (prefixWord ++ tailWord_2357407) baseStart_2357407 baseEnd_2357407 := by
    simpa [prefixWord, tailWord_2357407, baseEnd_2357407] using wordTrace_append hprefix tailTrace_2357407
  have hstable : (prefixWord ++ tailWord_2357407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357407).length < 2 ^ (prefixWord ++ tailWord_2357407).sum := by decide
  have hdescent : baseEnd_2357407 < baseStart_2357407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357419 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4]
def baseStart_2357419 : Nat := 118140960795 + 2357419 * 2 ^ 59
def prefixEnd_2357419 : Nat := 4983230072969 + 3 ^ 40 * 2357419 * 2
def baseEnd_2357419 : Nat := 1210489051041617321020933

theorem tailTrace_2357419 : CollatzResearch.WordTrace tailWord_2357419 prefixEnd_2357419 1210489051041617321020933 := by
  unfold tailWord_2357419
  simp only [CollatzResearch.WordTrace]
  refine ⟨85982134646481052956483311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57321423097654035304322207 85982134646481052956483311)
  ·
    refine ⟨128973201969721579434724967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85982134646481052956483311 128973201969721579434724967)
    ·
      refine ⟨193459802954582369152087451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128973201969721579434724967 193459802954582369152087451)
      ·
        refine ⟨290189704431873553728131177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193459802954582369152087451 290189704431873553728131177)
        ·
          refine ⟨217642278323905165296098383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290189704431873553728131177 217642278323905165296098383)
          ·
            refine ⟨326463417485857747944147575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217642278323905165296098383 326463417485857747944147575)
            ·
              refine ⟨489695126228786621916221363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326463417485857747944147575 489695126228786621916221363)
              ·
                refine ⟨734542689343179932874332045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489695126228786621916221363 734542689343179932874332045)
                ·
                  refine ⟨275453508503692474827874517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 734542689343179932874332045 275453508503692474827874517)
                  ·
                    refine ⟨6455941605555292378778309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 275453508503692474827874517 6455941605555292378778309)
                    ·
                      refine ⟨1210489051041617321020933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6455941605555292378778309 1210489051041617321020933)
                      ·
                        rfl

theorem cell23_2357419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_2357419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357419 prefixEnd_2357419 := by exact prefixLift 2357419
  have htrace : WordTrace (prefixWord ++ tailWord_2357419) baseStart_2357419 baseEnd_2357419 := by
    simpa [prefixWord, tailWord_2357419, baseEnd_2357419] using wordTrace_append hprefix tailTrace_2357419
  have hstable : (prefixWord ++ tailWord_2357419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357419).length < 2 ^ (prefixWord ++ tailWord_2357419).sum := by decide
  have hdescent : baseEnd_2357419 < baseStart_2357419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357466 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_2357466 : Nat := 118140960795 + 2357466 * 2 ^ 59
def prefixEnd_2357466 : Nat := 4983230072969 + 3 ^ 40 * 2357466 * 2
def baseEnd_2357466 : Nat := 1210513184632378637133217

theorem tailTrace_2357466 : CollatzResearch.WordTrace tailWord_2357466 prefixEnd_2357466 1210513184632378637133217 := by
  unfold tailWord_2357466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21495962219327694995861063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57322565918207186655629501 21495962219327694995861063)
  ·
    refine ⟨32243943328991542493791595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21495962219327694995861063 32243943328991542493791595)
    ·
      refine ⟨48365914993487313740687393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32243943328991542493791595 48365914993487313740687393)
      ·
        refine ⟨36274436245115485305515545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48365914993487313740687393 36274436245115485305515545)
        ·
          refine ⟨27205827183836613979136659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36274436245115485305515545 27205827183836613979136659)
          ·
            refine ⟨40808740775754920968704989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27205827183836613979136659 40808740775754920968704989)
            ·
              refine ⟨15303277790908095363264371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40808740775754920968704989 15303277790908095363264371)
              ·
                refine ⟨22954916686362143044896557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15303277790908095363264371 22954916686362143044896557)
                ·
                  refine ⟨8608093757385803641836209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22954916686362143044896557 8608093757385803641836209)
                  ·
                    refine ⟨6456070318039352731377157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8608093757385803641836209 6456070318039352731377157)
                    ·
                      refine ⟨1210513184632378637133217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6456070318039352731377157 1210513184632378637133217)
                      ·
                        rfl

theorem cell23_2357466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_2357466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357466 prefixEnd_2357466 := by exact prefixLift 2357466
  have htrace : WordTrace (prefixWord ++ tailWord_2357466) baseStart_2357466 baseEnd_2357466 := by
    simpa [prefixWord, tailWord_2357466, baseEnd_2357466] using wordTrace_append hprefix tailTrace_2357466
  have hstable : (prefixWord ++ tailWord_2357466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357466).length < 2 ^ (prefixWord ++ tailWord_2357466).sum := by decide
  have hdescent : baseEnd_2357466 < baseStart_2357466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357480 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 2, 4]
def baseStart_2357480 : Nat := 118140960795 + 2357480 * 2 ^ 59
def prefixEnd_2357480 : Nat := 4983230072969 + 3 ^ 40 * 2357480 * 2
def baseEnd_2357480 : Nat := 403506791120513860786051

theorem tailTrace_2357480 : CollatzResearch.WordTrace tailWord_2357480 prefixEnd_2357480 403506791120513860786051 := by
  unfold tailWord_2357480
  simp only [CollatzResearch.WordTrace]
  refine ⟨42992179749630030187226947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57322906332840040249635929 42992179749630030187226947)
  ·
    refine ⟨64488269624445045280840421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42992179749630030187226947 64488269624445045280840421)
    ·
      refine ⟨12091550554583445990157579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64488269624445045280840421 12091550554583445990157579)
      ·
        refine ⟨18137325831875168985236369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12091550554583445990157579 18137325831875168985236369)
        ·
          refine ⟨13602994373906376738927277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18137325831875168985236369 13602994373906376738927277)
          ·
            refine ⟨5101122890214891277097729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13602994373906376738927277 5101122890214891277097729)
            ·
              refine ⟨3825842167661168457823297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5101122890214891277097729 3825842167661168457823297)
              ·
                refine ⟨2869381625745876343367473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825842167661168457823297 2869381625745876343367473)
                ·
                  refine ⟨2152036219309407257525605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2869381625745876343367473 2152036219309407257525605)
                  ·
                    refine ⟨403506791120513860786051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2152036219309407257525605 403506791120513860786051)
                    ·
                      rfl

theorem cell23_2357480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_2357480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357480 prefixEnd_2357480 := by exact prefixLift 2357480
  have htrace : WordTrace (prefixWord ++ tailWord_2357480) baseStart_2357480 baseEnd_2357480 := by
    simpa [prefixWord, tailWord_2357480, baseEnd_2357480] using wordTrace_append hprefix tailTrace_2357480
  have hstable : (prefixWord ++ tailWord_2357480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357480).length < 2 ^ (prefixWord ++ tailWord_2357480).sum := by decide
  have hdescent : baseEnd_2357480 < baseStart_2357480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357503 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 3]
def baseStart_2357503 : Nat := 118140960795 + 2357503 * 2 ^ 59
def prefixEnd_2357503 : Nat := 4983230072969 + 3 ^ 40 * 2357503 * 2
def baseEnd_2357503 : Nat := 1210532183416594992370547

theorem tailTrace_2357503 : CollatzResearch.WordTrace tailWord_2357503 prefixEnd_2357503 1210532183416594992370547 := by
  unfold tailWord_2357503
  simp only [CollatzResearch.WordTrace]
  refine ⟨85985198378176735302541163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57323465585451156868360775 85985198378176735302541163)
  ·
    refine ⟨128977797567265102953811745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85985198378176735302541163 128977797567265102953811745)
    ·
      refine ⟨96733348175448827215358809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128977797567265102953811745 96733348175448827215358809)
      ·
        refine ⟨72550011131586620411519107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96733348175448827215358809 72550011131586620411519107)
        ·
          refine ⟨108825016697379930617278661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72550011131586620411519107 108825016697379930617278661)
          ·
            refine ⟨20404690630758736990739749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108825016697379930617278661 20404690630758736990739749)
            ·
              refine ⟨3825879493267263185763703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20404690630758736990739749 3825879493267263185763703)
              ·
                refine ⟨5738819239900894778645555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825879493267263185763703 5738819239900894778645555)
                ·
                  refine ⟨8608228859851342167968333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5738819239900894778645555 8608228859851342167968333)
                  ·
                    refine ⟨3228085822444253312988125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8608228859851342167968333 3228085822444253312988125)
                    ·
                      refine ⟨1210532183416594992370547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228085822444253312988125 1210532183416594992370547)
                      ·
                        rfl

theorem cell23_2357503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_2357503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357503 prefixEnd_2357503 := by exact prefixLift 2357503
  have htrace : WordTrace (prefixWord ++ tailWord_2357503) baseStart_2357503 baseEnd_2357503 := by
    simpa [prefixWord, tailWord_2357503, baseEnd_2357503] using wordTrace_append hprefix tailTrace_2357503
  have hstable : (prefixWord ++ tailWord_2357503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357503).length < 2 ^ (prefixWord ++ tailWord_2357503).sum := by decide
  have hdescent : baseEnd_2357503 < baseStart_2357503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357516 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2357516 : Nat := 118140960795 + 2357516 * 2 ^ 59
def prefixEnd_2357516 : Nat := 4983230072969 + 3 ^ 40 * 2357516 * 2
def baseEnd_2357516 : Nat := 1210538858665103441507987

theorem tailTrace_2357516 : CollatzResearch.WordTrace tailWord_2357516 prefixEnd_2357516 1210538858665103441507987 := by
  unfold tailWord_2357516
  simp only [CollatzResearch.WordTrace]
  refine ⟨42992836263564819261382201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57323781684753092348509601 42992836263564819261382201)
  ·
    refine ⟨32244627197673614446036651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42992836263564819261382201 32244627197673614446036651)
    ·
      refine ⟨48366940796510421669054977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32244627197673614446036651 48366940796510421669054977)
      ·
        refine ⟨36275205597382816251791233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48366940796510421669054977 36275205597382816251791233)
        ·
          refine ⟨27206404198037112188843425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36275205597382816251791233 27206404198037112188843425)
          ·
            refine ⟨20404803148527834141632569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27206404198037112188843425 20404803148527834141632569)
            ·
              refine ⟨15303602361395875606224427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20404803148527834141632569 15303602361395875606224427)
              ·
                refine ⟨22955403542093813409336641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15303602361395875606224427 22955403542093813409336641)
                ·
                  refine ⟨17216552656570360057002481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22955403542093813409336641 17216552656570360057002481)
                  ·
                    refine ⟨12912414492427770042751861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17216552656570360057002481 12912414492427770042751861)
                    ·
                      refine ⟨1210538858665103441507987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12912414492427770042751861 1210538858665103441507987)
                      ·
                        rfl

theorem cell23_2357516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2357516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357516 prefixEnd_2357516 := by exact prefixLift 2357516
  have htrace : WordTrace (prefixWord ++ tailWord_2357516) baseStart_2357516 baseEnd_2357516 := by
    simpa [prefixWord, tailWord_2357516, baseEnd_2357516] using wordTrace_append hprefix tailTrace_2357516
  have hstable : (prefixWord ++ tailWord_2357516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357516).length < 2 ^ (prefixWord ++ tailWord_2357516).sum := by decide
  have hdescent : baseEnd_2357516 < baseStart_2357516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357554 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_2357554 : Nat := 118140960795 + 2357554 * 2 ^ 59
def prefixEnd_2357554 : Nat := 4983230072969 + 3 ^ 40 * 2357554 * 2
def baseEnd_2357554 : Nat := 1210558370929974292832813

theorem tailTrace_2357554 : CollatzResearch.WordTrace tailWord_2357554 prefixEnd_2357554 1210558370929974292832813 := by
  unfold tailWord_2357554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496764625247992753161929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57324705667327980675098477 21496764625247992753161929)
  ·
    refine ⟨16122573468935994564871447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21496764625247992753161929 16122573468935994564871447)
    ·
      refine ⟨24183860203403991847307171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16122573468935994564871447 24183860203403991847307171)
      ·
        refine ⟨36275790305105987770960757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24183860203403991847307171 36275790305105987770960757)
        ·
          refine ⟨3400855341103686353527571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36275790305105987770960757 3400855341103686353527571)
          ·
            refine ⟨5101283011655529530291357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400855341103686353527571 5101283011655529530291357)
            ·
              refine ⟨1912981129370823573859259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5101283011655529530291357 1912981129370823573859259)
              ·
                refine ⟨2869471694056235360788889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912981129370823573859259 2869471694056235360788889)
                ·
                  refine ⟨2152103770542176520591667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2869471694056235360788889 2152103770542176520591667)
                  ·
                    refine ⟨3228155655813264780887501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152103770542176520591667 3228155655813264780887501)
                    ·
                      refine ⟨1210558370929974292832813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228155655813264780887501 1210558370929974292832813)
                      ·
                        rfl

theorem cell23_2357554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_2357554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357554 prefixEnd_2357554 := by exact prefixLift 2357554
  have htrace : WordTrace (prefixWord ++ tailWord_2357554) baseStart_2357554 baseEnd_2357554 := by
    simpa [prefixWord, tailWord_2357554, baseEnd_2357554] using wordTrace_append hprefix tailTrace_2357554
  have hstable : (prefixWord ++ tailWord_2357554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357554).length < 2 ^ (prefixWord ++ tailWord_2357554).sum := by decide
  have hdescent : baseEnd_2357554 < baseStart_2357554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357560 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 1, 4, 2]
def baseStart_2357560 : Nat := 118140960795 + 2357560 * 2 ^ 59
def prefixEnd_2357560 : Nat := 4983230072969 + 3 ^ 40 * 2357560 * 2
def baseEnd_2357560 : Nat := 1210561451813901269357785

theorem tailTrace_2357560 : CollatzResearch.WordTrace tailWord_2357560 prefixEnd_2357560 1210561451813901269357785 := by
  unfold tailWord_2357560
  simp only [CollatzResearch.WordTrace]
  refine ⟨42993638669485117018683067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57324851559313489358244089 42993638669485117018683067)
  ·
    refine ⟨64490458004227675528024601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42993638669485117018683067 64490458004227675528024601)
    ·
      refine ⟨48367843503170756646018451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64490458004227675528024601 48367843503170756646018451)
      ·
        refine ⟨72551765254756134969027677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48367843503170756646018451 72551765254756134969027677)
        ·
          refine ⟨27206911970533550613385379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72551765254756134969027677 27206911970533550613385379)
          ·
            refine ⟨40810367955800325920078069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27206911970533550613385379 40810367955800325920078069)
            ·
              refine ⟨3825971995856280555007319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40810367955800325920078069 3825971995856280555007319)
              ·
                refine ⟨5738957993784420832510979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825971995856280555007319 5738957993784420832510979)
                ·
                  refine ⟨8608436990676631248766469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5738957993784420832510979 8608436990676631248766469)
                  ·
                    refine ⟨1614081935751868359143713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8608436990676631248766469 1614081935751868359143713)
                    ·
                      refine ⟨1210561451813901269357785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614081935751868359143713 1210561451813901269357785)
                      ·
                        rfl

theorem cell23_2357560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_2357560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357560 prefixEnd_2357560 := by exact prefixLift 2357560
  have htrace : WordTrace (prefixWord ++ tailWord_2357560) baseStart_2357560 baseEnd_2357560 := by
    simpa [prefixWord, tailWord_2357560, baseEnd_2357560] using wordTrace_append hprefix tailTrace_2357560
  have hstable : (prefixWord ++ tailWord_2357560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357560).length < 2 ^ (prefixWord ++ tailWord_2357560).sum := by decide
  have hdescent : baseEnd_2357560 < baseStart_2357560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357583 : List Nat := [1, 1, 2, 1, 1, 2, 1, 9, 5]
def baseStart_2357583 : Nat := 118140960795 + 2357583 * 2 ^ 59
def prefixEnd_2357583 : Nat := 4983230072969 + 3 ^ 40 * 2357583 * 2
def baseEnd_2357583 : Nat := 134508140207661631041131

theorem tailTrace_2357583 : CollatzResearch.WordTrace tailWord_2357583 prefixEnd_2357583 134508140207661631041131 := by
  unfold tailWord_2357583
  simp only [CollatzResearch.WordTrace]
  refine ⟨85988116217886908965453403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57325410811924605976968935 85988116217886908965453403)
  ·
    refine ⟨128982174326830363448180105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85988116217886908965453403 128982174326830363448180105)
    ·
      refine ⟨96736630745122772586135079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128982174326830363448180105 96736630745122772586135079)
      ·
        refine ⟨145104946117684158879202619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96736630745122772586135079 145104946117684158879202619)
        ·
          refine ⟨217657419176526238318803929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145104946117684158879202619 217657419176526238318803929)
          ·
            refine ⟨163243064382394678739102947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217657419176526238318803929 163243064382394678739102947)
            ·
              refine ⟨244864596573592018108654421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163243064382394678739102947 244864596573592018108654421)
              ·
                refine ⟨1434753495548390731105397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 244864596573592018108654421 1434753495548390731105397)
                ·
                  refine ⟨134508140207661631041131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1434753495548390731105397 134508140207661631041131)
                  ·
                    rfl

theorem cell23_2357583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 5].length) (baseStart_2357583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357583 prefixEnd_2357583 := by exact prefixLift 2357583
  have htrace : WordTrace (prefixWord ++ tailWord_2357583) baseStart_2357583 baseEnd_2357583 := by
    simpa [prefixWord, tailWord_2357583, baseEnd_2357583] using wordTrace_append hprefix tailTrace_2357583
  have hstable : (prefixWord ++ tailWord_2357583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357583).length < 2 ^ (prefixWord ++ tailWord_2357583).sum := by decide
  have hdescent : baseEnd_2357583 < baseStart_2357583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357600 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 7]
def baseStart_2357600 : Nat := 118140960795 + 2357600 * 2 ^ 59
def prefixEnd_2357600 : Nat := 4983230072969 + 3 ^ 40 * 2357600 * 2
def baseEnd_2357600 : Nat := 134509110115564568095289

theorem tailTrace_2357600 : CollatzResearch.WordTrace tailWord_2357600 prefixEnd_2357600 134509110115564568095289 := by
  unfold tailWord_2357600
  simp only [CollatzResearch.WordTrace]
  refine ⟨42994368129412660434411127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57325824172550213912548169 42994368129412660434411127)
  ·
    refine ⟨64491552194118990651616691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42994368129412660434411127 64491552194118990651616691)
    ·
      refine ⟨96737328291178485977425037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64491552194118990651616691 96737328291178485977425037)
      ·
        refine ⟨36276498109191932241534389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96737328291178485977425037 36276498109191932241534389)
        ·
          refine ⟨3400921697736743647643849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36276498109191932241534389 3400921697736743647643849)
          ·
            refine ⟨2550691273302557735732887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400921697736743647643849 2550691273302557735732887)
            ·
              refine ⟨3826036909953836603599331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550691273302557735732887 3826036909953836603599331)
              ·
                refine ⟨5739055364930754905398997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3826036909953836603599331 5739055364930754905398997)
                ·
                  refine ⟨134509110115564568095289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5739055364930754905398997 134509110115564568095289)
                  ·
                    rfl

theorem cell23_2357600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 7].length) (baseStart_2357600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357600 prefixEnd_2357600 := by exact prefixLift 2357600
  have htrace : WordTrace (prefixWord ++ tailWord_2357600) baseStart_2357600 baseEnd_2357600 := by
    simpa [prefixWord, tailWord_2357600, baseEnd_2357600] using wordTrace_append hprefix tailTrace_2357600
  have hstable : (prefixWord ++ tailWord_2357600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357600).length < 2 ^ (prefixWord ++ tailWord_2357600).sum := by decide
  have hdescent : baseEnd_2357600 < baseStart_2357600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357613 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2357613 : Nat := 118140960795 + 2357613 * 2 ^ 59
def prefixEnd_2357613 : Nat := 4983230072969 + 3 ^ 40 * 2357613 * 2
def baseEnd_2357613 : Nat := 403529555429529853998347

theorem tailTrace_2357613 : CollatzResearch.WordTrace tailWord_2357613 prefixEnd_2357613 403529555429529853998347 := by
  unfold tailWord_2357613
  simp only [CollatzResearch.WordTrace]
  refine ⟨85989210407778224089045493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57326140271852149392696995 85989210407778224089045493)
  ·
    refine ⟨8061488475729208508348015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85989210407778224089045493 8061488475729208508348015)
    ·
      refine ⟨12092232713593812762522023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8061488475729208508348015 12092232713593812762522023)
      ·
        refine ⟨18138349070390719143783035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12092232713593812762522023 18138349070390719143783035)
        ·
          refine ⟨27207523605586078715674553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18138349070390719143783035 27207523605586078715674553)
          ·
            refine ⟨20405642704189559036755915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27207523605586078715674553 20405642704189559036755915)
            ·
              refine ⟨30608464056284338555133873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20405642704189559036755915 30608464056284338555133873)
              ·
                refine ⟨22956348042213253916350405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30608464056284338555133873 22956348042213253916350405)
                ·
                  refine ⟨4304315257914985109315701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22956348042213253916350405 4304315257914985109315701)
                  ·
                    refine ⟨403529555429529853998347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4304315257914985109315701 403529555429529853998347)
                    ·
                      rfl

theorem cell23_2357613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2357613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357613 prefixEnd_2357613 := by exact prefixLift 2357613
  have htrace : WordTrace (prefixWord ++ tailWord_2357613) baseStart_2357613 baseEnd_2357613 := by
    simpa [prefixWord, tailWord_2357613, baseEnd_2357613] using wordTrace_append hprefix tailTrace_2357613
  have hstable : (prefixWord ++ tailWord_2357613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357613).length < 2 ^ (prefixWord ++ tailWord_2357613).sum := by decide
  have hdescent : baseEnd_2357613 < baseStart_2357613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357653 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_2357653 : Nat := 118140960795 + 2357653 * 2 ^ 59
def prefixEnd_2357653 : Nat := 4983230072969 + 3 ^ 40 * 2357653 * 2
def baseEnd_2357653 : Nat := 1210609205514769405494857

theorem tailTrace_2357653 : CollatzResearch.WordTrace tailWord_2357653 prefixEnd_2357653 1210609205514769405494857 := by
  unfold tailWord_2357653
  simp only [CollatzResearch.WordTrace]
  refine ⟨85990669327633310920501613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57327112885088873947001075 85990669327633310920501613)
  ·
    refine ⟨32246500997862491595188105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85990669327633310920501613 32246500997862491595188105)
    ·
      refine ⟨24184875748396868696391079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32246500997862491595188105 24184875748396868696391079)
      ·
        refine ⟨36277313622595303044586619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24184875748396868696391079 36277313622595303044586619)
        ·
          refine ⟨54415970433892954566879929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36277313622595303044586619 54415970433892954566879929)
          ·
            refine ⟨40811977825419715925159947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54415970433892954566879929 40811977825419715925159947)
            ·
              refine ⟨61217966738129573887739921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40811977825419715925159947 61217966738129573887739921)
              ·
                refine ⟨45913475053597180415804941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61217966738129573887739921 45913475053597180415804941)
                ·
                  refine ⟨17217553145098942655926853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45913475053597180415804941 17217553145098942655926853)
                  ·
                    refine ⟨3228291214706051747986285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17217553145098942655926853 3228291214706051747986285)
                    ·
                      refine ⟨1210609205514769405494857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228291214706051747986285 1210609205514769405494857)
                      ·
                        rfl

theorem cell23_2357653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_2357653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357653 prefixEnd_2357653 := by exact prefixLift 2357653
  have htrace : WordTrace (prefixWord ++ tailWord_2357653) baseStart_2357653 baseEnd_2357653 := by
    simpa [prefixWord, tailWord_2357653, baseEnd_2357653] using wordTrace_append hprefix tailTrace_2357653
  have hstable : (prefixWord ++ tailWord_2357653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357653).length < 2 ^ (prefixWord ++ tailWord_2357653).sum := by decide
  have hdescent : baseEnd_2357653 < baseStart_2357653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357684 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2357684 : Nat := 118140960795 + 2357684 * 2 ^ 59
def prefixEnd_2357684 : Nat := 4983230072969 + 3 ^ 40 * 2357684 * 2
def baseEnd_2357684 : Nat := 1210625123415058784207215

theorem tailTrace_2357684 : CollatzResearch.WordTrace tailWord_2357684 prefixEnd_2357684 1210625123415058784207215 := by
  unfold tailWord_2357684
  simp only [CollatzResearch.WordTrace]
  refine ⟨42995899995260501607440053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57327866660347335476586737 42995899995260501607440053)
  ·
    refine ⟨4030865624555672025697505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42995899995260501607440053 4030865624555672025697505)
    ·
      refine ⟨3023149218416754019273129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4030865624555672025697505 3023149218416754019273129)
      ·
        refine ⟨2267361913812565514454847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3023149218416754019273129 2267361913812565514454847)
        ·
          refine ⟨3401042870718848271682271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267361913812565514454847 3401042870718848271682271)
          ·
            refine ⟨5101564306078272407523407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401042870718848271682271 5101564306078272407523407)
            ·
              refine ⟨7652346459117408611285111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101564306078272407523407 7652346459117408611285111)
              ·
                refine ⟨11478519688676112916927667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7652346459117408611285111 11478519688676112916927667)
                ·
                  refine ⟨17217779533014169375391501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11478519688676112916927667 17217779533014169375391501)
                  ·
                    refine ⟨6456667324880313515771813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17217779533014169375391501 6456667324880313515771813)
                    ·
                      refine ⟨1210625123415058784207215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6456667324880313515771813 1210625123415058784207215)
                      ·
                        rfl

theorem cell23_2357684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2357684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357684 prefixEnd_2357684 := by exact prefixLift 2357684
  have htrace : WordTrace (prefixWord ++ tailWord_2357684) baseStart_2357684 baseEnd_2357684 := by
    simpa [prefixWord, tailWord_2357684, baseEnd_2357684] using wordTrace_append hprefix tailTrace_2357684
  have hstable : (prefixWord ++ tailWord_2357684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357684).length < 2 ^ (prefixWord ++ tailWord_2357684).sum := by decide
  have hdescent : baseEnd_2357684 < baseStart_2357684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357687 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_2357687 : Nat := 118140960795 + 2357687 * 2 ^ 59
def prefixEnd_2357687 : Nat := 4983230072969 + 3 ^ 40 * 2357687 * 2
def baseEnd_2357687 : Nat := 1210626663857022272469701

theorem tailTrace_2357687 : CollatzResearch.WordTrace tailWord_2357687 prefixEnd_2357687 1210626663857022272469701 := by
  unfold tailWord_2357687
  simp only [CollatzResearch.WordTrace]
  refine ⟨85991909409510134727239315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57327939606340089818159543 85991909409510134727239315)
  ·
    refine ⟨128987864114265202090858973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85991909409510134727239315 128987864114265202090858973)
    ·
      refine ⟨48370449042849450784072115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128987864114265202090858973 48370449042849450784072115)
      ·
        refine ⟨72555673564274176176108173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48370449042849450784072115 72555673564274176176108173)
        ·
          refine ⟨27208377586602816066040565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72555673564274176176108173 27208377586602816066040565)
          ·
            refine ⟨2550785398744014006191303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27208377586602816066040565 2550785398744014006191303)
            ·
              refine ⟨3826178098116021009286955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550785398744014006191303 3826178098116021009286955)
              ·
                refine ⟨5739267147174031513930433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3826178098116021009286955 5739267147174031513930433)
                ·
                  refine ⟨4304450360380523635447825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5739267147174031513930433 4304450360380523635447825)
                  ·
                    refine ⟨3228337770285392726585869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4304450360380523635447825 3228337770285392726585869)
                    ·
                      refine ⟨1210626663857022272469701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228337770285392726585869 1210626663857022272469701)
                      ·
                        rfl

theorem cell23_2357687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_2357687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357687 prefixEnd_2357687 := by exact prefixLift 2357687
  have htrace : WordTrace (prefixWord ++ tailWord_2357687) baseStart_2357687 baseEnd_2357687 := by
    simpa [prefixWord, tailWord_2357687, baseEnd_2357687] using wordTrace_append hprefix tailTrace_2357687
  have hstable : (prefixWord ++ tailWord_2357687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357687).length < 2 ^ (prefixWord ++ tailWord_2357687).sum := by decide
  have hdescent : baseEnd_2357687 < baseStart_2357687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357717 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2357717 : Nat := 118140960795 + 2357717 * 2 ^ 59
def prefixEnd_2357717 : Nat := 4983230072969 + 3 ^ 40 * 2357717 * 2
def baseEnd_2357717 : Nat := 1210642068276657155094563

theorem tailTrace_2357717 : CollatzResearch.WordTrace tailWord_2357717 prefixEnd_2357717 1210642068276657155094563 := by
  unfold tailWord_2357717
  simp only [CollatzResearch.WordTrace]
  refine ⟨85993003599401449850831405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57328669066267633233887603 85993003599401449850831405)
  ·
    refine ⟨32247376349775543694061777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85993003599401449850831405 32247376349775543694061777)
    ·
      refine ⟨24185532262331657770546333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32247376349775543694061777 24185532262331657770546333)
      ·
        refine ⟨9069574598374371663954875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24185532262331657770546333 9069574598374371663954875)
        ·
          refine ⟨13604361897561557495932313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069574598374371663954875 13604361897561557495932313)
          ·
            refine ⟨10203271423171168121949235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13604361897561557495932313 10203271423171168121949235)
            ·
              refine ⟨15304907134756752182923853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10203271423171168121949235 15304907134756752182923853)
              ·
                refine ⟨5739340175533782068596445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15304907134756752182923853 5739340175533782068596445)
                ·
                  refine ⟨2152252565825168275723667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5739340175533782068596445 2152252565825168275723667)
                  ·
                    refine ⟨3228378848737752413585501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152252565825168275723667 3228378848737752413585501)
                    ·
                      refine ⟨1210642068276657155094563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228378848737752413585501 1210642068276657155094563)
                      ·
                        rfl

theorem cell23_2357717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2357717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357717 prefixEnd_2357717 := by exact prefixLift 2357717
  have htrace : WordTrace (prefixWord ++ tailWord_2357717) baseStart_2357717 baseEnd_2357717 := by
    simpa [prefixWord, tailWord_2357717, baseEnd_2357717] using wordTrace_append hprefix tailTrace_2357717
  have hstable : (prefixWord ++ tailWord_2357717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357717).length < 2 ^ (prefixWord ++ tailWord_2357717).sum := by decide
  have hdescent : baseEnd_2357717 < baseStart_2357717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357740 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 2, 6, 2]
def baseStart_2357740 : Nat := 118140960795 + 2357740 * 2 ^ 59
def prefixEnd_2357740 : Nat := 4983230072969 + 3 ^ 40 * 2357740 * 2
def baseEnd_2357740 : Nat := 1210653878331710565106957

theorem tailTrace_2357740 : CollatzResearch.WordTrace tailWord_2357740 prefixEnd_2357740 1210653878331710565106957 := by
  unfold tailWord_2357740
  simp only [CollatzResearch.WordTrace]
  refine ⟨42996921239159062389459337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57329228318878749852612449 42996921239159062389459337)
  ·
    refine ⟨32247690929369296792094503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42996921239159062389459337 32247690929369296792094503)
    ·
      refine ⟨48371536394053945188141755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32247690929369296792094503 48371536394053945188141755)
      ·
        refine ⟨72557304591080917782212633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48371536394053945188141755 72557304591080917782212633)
        ·
          refine ⟨54417978443310688336659475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72557304591080917782212633 54417978443310688336659475)
          ·
            refine ⟨81626967664966032504989213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54417978443310688336659475 81626967664966032504989213)
            ·
              refine ⟨30610112874362262189370955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81626967664966032504989213 30610112874362262189370955)
              ·
                refine ⟨45915169311543393284056433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30610112874362262189370955 45915169311543393284056433)
                ·
                  refine ⟨34436376983657544963042325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45915169311543393284056433 34436376983657544963042325)
                  ·
                    refine ⟨1614205171108947420142609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34436376983657544963042325 1614205171108947420142609)
                    ·
                      refine ⟨1210653878331710565106957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614205171108947420142609 1210653878331710565106957)
                      ·
                        rfl

theorem cell23_2357740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_2357740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357740 prefixEnd_2357740 := by exact prefixLift 2357740
  have htrace : WordTrace (prefixWord ++ tailWord_2357740) baseStart_2357740 baseEnd_2357740 := by
    simpa [prefixWord, tailWord_2357740, baseEnd_2357740] using wordTrace_append hprefix tailTrace_2357740
  have hstable : (prefixWord ++ tailWord_2357740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357740).length < 2 ^ (prefixWord ++ tailWord_2357740).sum := by decide
  have hdescent : baseEnd_2357740 < baseStart_2357740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357743 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_2357743 : Nat := 118140960795 + 2357743 * 2 ^ 59
def prefixEnd_2357743 : Nat := 4983230072969 + 3 ^ 40 * 2357743 * 2
def baseEnd_2357743 : Nat := 1210655418773674053369443

theorem tailTrace_2357743 : CollatzResearch.WordTrace tailWord_2357743 prefixEnd_2357743 1210655418773674053369443 := by
  unfold tailWord_2357743
  simp only [CollatzResearch.WordTrace]
  refine ⟨85993951897307256291277883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57329301264871504194185255 85993951897307256291277883)
  ·
    refine ⟨128990927845960884436916825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85993951897307256291277883 128990927845960884436916825)
    ·
      refine ⟨96743195884470663327687619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128990927845960884436916825 96743195884470663327687619)
      ·
        refine ⟨145114793826705994991531429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96743195884470663327687619 145114793826705994991531429)
        ·
          refine ⟨27209023842507374060912143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145114793826705994991531429 27209023842507374060912143)
          ·
            refine ⟨40813535763761061091368215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27209023842507374060912143 40813535763761061091368215)
            ·
              refine ⟨61220303645641591637052323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40813535763761061091368215 61220303645641591637052323)
              ·
                refine ⟨91830455468462387455578485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61220303645641591637052323 91830455468462387455578485)
                ·
                  refine ⟨8609105200168348823960483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91830455468462387455578485 8609105200168348823960483)
                  ·
                    refine ⟨12913657800252523235940725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8609105200168348823960483 12913657800252523235940725)
                    ·
                      refine ⟨1210655418773674053369443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12913657800252523235940725 1210655418773674053369443)
                      ·
                        rfl

theorem cell23_2357743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_2357743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357743 prefixEnd_2357743 := by exact prefixLift 2357743
  have htrace : WordTrace (prefixWord ++ tailWord_2357743) baseStart_2357743 baseEnd_2357743 := by
    simpa [prefixWord, tailWord_2357743, baseEnd_2357743] using wordTrace_append hprefix tailTrace_2357743
  have hstable : (prefixWord ++ tailWord_2357743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357743).length < 2 ^ (prefixWord ++ tailWord_2357743).sum := by decide
  have hdescent : baseEnd_2357743 < baseStart_2357743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357750 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2357750 : Nat := 118140960795 + 2357750 * 2 ^ 59
def prefixEnd_2357750 : Nat := 4983230072969 + 3 ^ 40 * 2357750 * 2
def baseEnd_2357750 : Nat := 403553004379418508660637

theorem tailTrace_2357750 : CollatzResearch.WordTrace tailWord_2357750 prefixEnd_2357750 403553004379418508660637 := by
  unfold tailWord_2357750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374637950517618530423919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57329471472187930991188469 5374637950517618530423919)
  ·
    refine ⟨8061956925776427795635879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5374637950517618530423919 8061956925776427795635879)
    ·
      refine ⟨12092935388664641693453819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8061956925776427795635879 12092935388664641693453819)
      ·
        refine ⟨18139403082996962540180729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12092935388664641693453819 18139403082996962540180729)
        ·
          refine ⟨13604552312247721905135547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18139403082996962540180729 13604552312247721905135547)
          ·
            refine ⟨20406828468371582857703321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13604552312247721905135547 20406828468371582857703321)
            ·
              refine ⟨15305121351278687143277491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20406828468371582857703321 15305121351278687143277491)
              ·
                refine ⟨22957682026918030714916237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15305121351278687143277491 22957682026918030714916237)
                ·
                  refine ⟨8609130760094261518093589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22957682026918030714916237 8609130760094261518093589)
                  ·
                    refine ⟨403553004379418508660637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8609130760094261518093589 403553004379418508660637)
                    ·
                      rfl

theorem cell23_2357750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2357750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357750 prefixEnd_2357750 := by exact prefixLift 2357750
  have htrace : WordTrace (prefixWord ++ tailWord_2357750) baseStart_2357750 baseEnd_2357750 := by
    simpa [prefixWord, tailWord_2357750, baseEnd_2357750] using wordTrace_append hprefix tailTrace_2357750
  have hstable : (prefixWord ++ tailWord_2357750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357750).length < 2 ^ (prefixWord ++ tailWord_2357750).sum := by decide
  have hdescent : baseEnd_2357750 < baseStart_2357750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357784 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 2, 4]
def baseStart_2357784 : Nat := 118140960795 + 2357784 * 2 ^ 59
def prefixEnd_2357784 : Nat := 4983230072969 + 3 ^ 40 * 2357784 * 2
def baseEnd_2357784 : Nat := 403558823826836130985585

theorem tailTrace_2357784 : CollatzResearch.WordTrace tailWord_2357784 prefixEnd_2357784 403558823826836130985585 := by
  unfold tailWord_2357784
  simp only [CollatzResearch.WordTrace]
  refine ⟨42997723645079360146760203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57330298193439146862346937 42997723645079360146760203)
  ·
    refine ⟨64496585467619040220140305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42997723645079360146760203 64496585467619040220140305)
    ·
      refine ⟨48372439100714280165105229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64496585467619040220140305 48372439100714280165105229)
      ·
        refine ⟨18139664662767855061914461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48372439100714280165105229 18139664662767855061914461)
        ·
          refine ⟨6802374248537945648217923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18139664662767855061914461 6802374248537945648217923)
          ·
            refine ⟨10203561372806918472326885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6802374248537945648217923 10203561372806918472326885)
            ·
              refine ⟨1913167757401297213561291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10203561372806918472326885 1913167757401297213561291)
              ·
                refine ⟨2869751636101945820341937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913167757401297213561291 2869751636101945820341937)
                ·
                  refine ⟨2152313727076459365256453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2869751636101945820341937 2152313727076459365256453)
                  ·
                    refine ⟨403558823826836130985585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2152313727076459365256453 403558823826836130985585)
                    ·
                      rfl

theorem cell23_2357784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_2357784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357784 prefixEnd_2357784 := by exact prefixLift 2357784
  have htrace : WordTrace (prefixWord ++ tailWord_2357784) baseStart_2357784 baseEnd_2357784 := by
    simpa [prefixWord, tailWord_2357784, baseEnd_2357784] using wordTrace_append hprefix tailTrace_2357784
  have hstable : (prefixWord ++ tailWord_2357784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357784).length < 2 ^ (prefixWord ++ tailWord_2357784).sum := by decide
  have hdescent : baseEnd_2357784 < baseStart_2357784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357803 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5]
def baseStart_2357803 : Nat := 118140960795 + 2357803 * 2 ^ 59
def prefixEnd_2357803 : Nat := 4983230072969 + 3 ^ 40 * 2357803 * 2
def baseEnd_2357803 : Nat := 1210686227612943818619167

theorem tailTrace_2357803 : CollatzResearch.WordTrace tailWord_2357803 prefixEnd_2357803 1210686227612943818619167 := by
  unfold tailWord_2357803
  simp only [CollatzResearch.WordTrace]
  refine ⟨85996140277089886538462063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57330760184726591025641375 85996140277089886538462063)
  ·
    refine ⟨128994210415634829807693095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85996140277089886538462063 128994210415634829807693095)
    ·
      refine ⟨193491315623452244711539643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128994210415634829807693095 193491315623452244711539643)
      ·
        refine ⟨290236973435178367067309465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193491315623452244711539643 290236973435178367067309465)
        ·
          refine ⟨217677730076383775300482099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290236973435178367067309465 217677730076383775300482099)
          ·
            refine ⟨326516595114575662950723149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217677730076383775300482099 326516595114575662950723149)
            ·
              refine ⟨122443723167965873606521181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326516595114575662950723149 122443723167965873606521181)
              ·
                refine ⟨45916396187987202602445443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122443723167965873606521181 45916396187987202602445443)
                ·
                  refine ⟨68874594281980803903668165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45916396187987202602445443 68874594281980803903668165)
                  ·
                    refine ⟨12913986427871400731937781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68874594281980803903668165 12913986427871400731937781)
                    ·
                      refine ⟨1210686227612943818619167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12913986427871400731937781 1210686227612943818619167)
                      ·
                        rfl

theorem cell23_2357803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_2357803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357803 prefixEnd_2357803 := by exact prefixLift 2357803
  have htrace : WordTrace (prefixWord ++ tailWord_2357803) baseStart_2357803 baseEnd_2357803 := by
    simpa [prefixWord, tailWord_2357803, baseEnd_2357803] using wordTrace_append hprefix tailTrace_2357803
  have hstable : (prefixWord ++ tailWord_2357803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357803).length < 2 ^ (prefixWord ++ tailWord_2357803).sum := by decide
  have hdescent : baseEnd_2357803 < baseStart_2357803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357825 : List Nat := [1, 2, 5, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2357825 : Nat := 118140960795 + 2357825 * 2 ^ 59
def prefixEnd_2357825 : Nat := 4983230072969 + 3 ^ 40 * 2357825 * 2
def baseEnd_2357825 : Nat := 1210697524187342732544067

theorem tailTrace_2357825 : CollatzResearch.WordTrace tailWord_2357825 prefixEnd_2357825 1210697524187342732544067 := by
  unfold tailWord_2357825
  simp only [CollatzResearch.WordTrace]
  refine ⟨85996942683010184295762929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57331295122006789530508619 85996942683010184295762929)
  ·
    refine ⟨64497707012257638221822197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85996942683010184295762929 64497707012257638221822197)
    ·
      refine ⟨6046660032399153583295831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64497707012257638221822197 6046660032399153583295831)
      ·
        refine ⟨9069990048598730374943747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046660032399153583295831 9069990048598730374943747)
        ·
          refine ⟨13604985072898095562415621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069990048598730374943747 13604985072898095562415621)
          ·
            refine ⟨2550934701168392917952929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13604985072898095562415621 2550934701168392917952929)
            ·
              refine ⟨1913201025876294688464697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550934701168392917952929 1913201025876294688464697)
              ·
                refine ⟨1434900769407221016348523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913201025876294688464697 1434900769407221016348523)
                ·
                  refine ⟨2152351154110831524522785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434900769407221016348523 2152351154110831524522785)
                  ·
                    refine ⟨1614263365583123643392089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2152351154110831524522785 1614263365583123643392089)
                    ·
                      refine ⟨1210697524187342732544067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614263365583123643392089 1210697524187342732544067)
                      ·
                        rfl

theorem cell23_2357825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2357825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357825 prefixEnd_2357825 := by exact prefixLift 2357825
  have htrace : WordTrace (prefixWord ++ tailWord_2357825) baseStart_2357825 baseEnd_2357825 := by
    simpa [prefixWord, tailWord_2357825, baseEnd_2357825] using wordTrace_append hprefix tailTrace_2357825
  have hstable : (prefixWord ++ tailWord_2357825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357825).length < 2 ^ (prefixWord ++ tailWord_2357825).sum := by decide
  have hdescent : baseEnd_2357825 < baseStart_2357825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357843 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10]
def baseStart_2357843 : Nat := 118140960795 + 2357843 * 2 ^ 59
def prefixEnd_2357843 : Nat := 4983230072969 + 3 ^ 40 * 2357843 * 2
def baseEnd_2357843 : Nat := 1210706766839123662118983

theorem tailTrace_2357843 : CollatzResearch.WordTrace tailWord_2357843 prefixEnd_2357843 1210706766839123662118983 := by
  unfold tailWord_2357843
  simp only [CollatzResearch.WordTrace]
  refine ⟨85997599196944973369918183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57331732797963315579945455 85997599196944973369918183)
  ·
    refine ⟨128996398795417460054877275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85997599196944973369918183 128996398795417460054877275)
    ·
      refine ⟨193494598193126190082315913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128996398795417460054877275 193494598193126190082315913)
      ·
        refine ⟨145120948644844642561736935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193494598193126190082315913 145120948644844642561736935)
        ·
          refine ⟨217681422967266963842605403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145120948644844642561736935 217681422967266963842605403)
          ·
            refine ⟨326522134450900445763908105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217681422967266963842605403 326522134450900445763908105)
            ·
              refine ⟨244891600838175334322931079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326522134450900445763908105 244891600838175334322931079)
              ·
                refine ⟨367337401257263001484396619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244891600838175334322931079 367337401257263001484396619)
                ·
                  refine ⟨551006101885894502226594929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367337401257263001484396619 551006101885894502226594929)
                  ·
                    refine ⟨413254576414420876669946197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 551006101885894502226594929 413254576414420876669946197)
                    ·
                      refine ⟨1210706766839123662118983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 413254576414420876669946197 1210706766839123662118983)
                      ·
                        rfl

theorem cell23_2357843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_2357843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357843 prefixEnd_2357843 := by exact prefixLift 2357843
  have htrace : WordTrace (prefixWord ++ tailWord_2357843) baseStart_2357843 baseEnd_2357843 := by
    simpa [prefixWord, tailWord_2357843, baseEnd_2357843] using wordTrace_append hprefix tailTrace_2357843
  have hstable : (prefixWord ++ tailWord_2357843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357843).length < 2 ^ (prefixWord ++ tailWord_2357843).sum := by decide
  have hdescent : baseEnd_2357843 < baseStart_2357843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357860 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_2357860 : Nat := 118140960795 + 2357860 * 2 ^ 59
def prefixEnd_2357860 : Nat := 4983230072969 + 3 ^ 40 * 2357860 * 2
def baseEnd_2357860 : Nat := 1210715496010250095606405

theorem tailTrace_2357860 : CollatzResearch.WordTrace tailWord_2357860 prefixEnd_2357860 1210715496010250095606405 := by
  unfold tailWord_2357860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42999109618941692636643517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57332146158588923515524689 42999109618941692636643517)
  ·
    refine ⟨16124666107103134738741319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42999109618941692636643517 16124666107103134738741319)
    ·
      refine ⟨24186999160654702108111979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16124666107103134738741319 24186999160654702108111979)
      ·
        refine ⟨36280498740982053162167969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24186999160654702108111979 36280498740982053162167969)
        ·
          refine ⟨27210374055736539871625977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36280498740982053162167969 27210374055736539871625977)
          ·
            refine ⟨20407780541802404903719483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27210374055736539871625977 20407780541802404903719483)
            ·
              refine ⟨30611670812703607355579225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20407780541802404903719483 30611670812703607355579225)
              ·
                refine ⟨22958753109527705516684419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30611670812703607355579225 22958753109527705516684419)
                ·
                  refine ⟨34438129664291558275026629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22958753109527705516684419 34438129664291558275026629)
                  ·
                    refine ⟨6457149312054667176567493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34438129664291558275026629 6457149312054667176567493)
                    ·
                      refine ⟨1210715496010250095606405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6457149312054667176567493 1210715496010250095606405)
                      ·
                        rfl

theorem cell23_2357860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_2357860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357860 prefixEnd_2357860 := by exact prefixLift 2357860
  have htrace : WordTrace (prefixWord ++ tailWord_2357860) baseStart_2357860 baseEnd_2357860 := by
    simpa [prefixWord, tailWord_2357860, baseEnd_2357860] using wordTrace_append hprefix tailTrace_2357860
  have hstable : (prefixWord ++ tailWord_2357860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357860).length < 2 ^ (prefixWord ++ tailWord_2357860).sum := by decide
  have hdescent : baseEnd_2357860 < baseStart_2357860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357880 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_2357880 : Nat := 118140960795 + 2357880 * 2 ^ 59
def prefixEnd_2357880 : Nat := 4983230072969 + 3 ^ 40 * 2357880 * 2
def baseEnd_2357880 : Nat := 1210725765623340017356313

theorem tailTrace_2357880 : CollatzResearch.WordTrace tailWord_2357880 prefixEnd_2357880 1210725765623340017356313 := by
  unfold tailWord_2357880
  simp only [CollatzResearch.WordTrace]
  refine ⟨42999474348905464344507547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57332632465207285792676729 42999474348905464344507547)
  ·
    refine ⟨64499211523358196516761321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42999474348905464344507547 64499211523358196516761321)
    ·
      refine ⟨48374408642518647387570991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64499211523358196516761321 48374408642518647387570991)
      ·
        refine ⟨72561612963777971081356487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48374408642518647387570991 72561612963777971081356487)
        ·
          refine ⟨108842419445666956622034731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72561612963777971081356487 108842419445666956622034731)
          ·
            refine ⟨163263629168500434933052097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108842419445666956622034731 163263629168500434933052097)
            ·
              refine ⟨122447721876375326199789073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163263629168500434933052097 122447721876375326199789073)
              ·
                refine ⟨91835791407281494649841805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122447721876375326199789073 91835791407281494649841805)
                ·
                  refine ⟨34438421777730560493690677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91835791407281494649841805 34438421777730560493690677)
                  ·
                    refine ⟨3228602041662240046283501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34438421777730560493690677 3228602041662240046283501)
                    ·
                      refine ⟨1210725765623340017356313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228602041662240046283501 1210725765623340017356313)
                      ·
                        rfl

theorem cell23_2357880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_2357880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357880 prefixEnd_2357880 := by exact prefixLift 2357880
  have htrace : WordTrace (prefixWord ++ tailWord_2357880) baseStart_2357880 baseEnd_2357880 := by
    simpa [prefixWord, tailWord_2357880, baseEnd_2357880] using wordTrace_append hprefix tailTrace_2357880
  have hstable : (prefixWord ++ tailWord_2357880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357880).length < 2 ^ (prefixWord ++ tailWord_2357880).sum := by decide
  have hdescent : baseEnd_2357880 < baseStart_2357880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357881 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 2, 2, 2]
def baseStart_2357881 : Nat := 118140960795 + 2357881 * 2 ^ 59
def prefixEnd_2357881 : Nat := 4983230072969 + 3 ^ 40 * 2357881 * 2
def baseEnd_2357881 : Nat := 1210726279103994513443809

theorem tailTrace_2357881 : CollatzResearch.WordTrace tailWord_2357881 prefixEnd_2357881 1210726279103994513443809 := by
  unfold tailWord_2357881
  simp only [CollatzResearch.WordTrace]
  refine ⟨85998985170807305859801497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57332656780538203906534331 85998985170807305859801497)
  ·
    refine ⟨64499238878105479394851123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85998985170807305859801497 64499238878105479394851123)
    ·
      refine ⟨96748858317158219092276685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64499238878105479394851123 96748858317158219092276685)
      ·
        refine ⟨36280821868934332159603757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96748858317158219092276685 36280821868934332159603757)
        ·
          refine ⟨13605308200850374559851409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36280821868934332159603757 13605308200850374559851409)
          ·
            refine ⟨10203981150637780919888557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13605308200850374559851409 10203981150637780919888557)
            ·
              refine ⟨3826492931489167844958209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10203981150637780919888557 3826492931489167844958209)
              ·
                refine ⟨2869869698616875883718657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826492931489167844958209 2869869698616875883718657)
                ·
                  refine ⟨2152402273962656912788993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2869869698616875883718657 2152402273962656912788993)
                  ·
                    refine ⟨1614301705471992684591745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2152402273962656912788993 1614301705471992684591745)
                    ·
                      refine ⟨1210726279103994513443809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614301705471992684591745 1210726279103994513443809)
                      ·
                        rfl

theorem cell23_2357881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_2357881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357881 prefixEnd_2357881 := by exact prefixLift 2357881
  have htrace : WordTrace (prefixWord ++ tailWord_2357881) baseStart_2357881 baseEnd_2357881 := by
    simpa [prefixWord, tailWord_2357881, baseEnd_2357881] using wordTrace_append hprefix tailTrace_2357881
  have hstable : (prefixWord ++ tailWord_2357881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357881).length < 2 ^ (prefixWord ++ tailWord_2357881).sum := by decide
  have hdescent : baseEnd_2357881 < baseStart_2357881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357898 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_2357898 : Nat := 118140960795 + 2357898 * 2 ^ 59
def prefixEnd_2357898 : Nat := 4983230072969 + 3 ^ 40 * 2357898 * 2
def baseEnd_2357898 : Nat := 1210735008275120946931231

theorem tailTrace_2357898 : CollatzResearch.WordTrace tailWord_2357898 prefixEnd_2357898 1210735008275120946931231 := by
  unfold tailWord_2357898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21499901302936429440792587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57333070141163811842113565 21499901302936429440792587)
  ·
    refine ⟨32249851954404644161188881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21499901302936429440792587 32249851954404644161188881)
    ·
      refine ⟨24187388965803483120891661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32249851954404644161188881 24187388965803483120891661)
      ·
        refine ⟨9070270862176306170334373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24187388965803483120891661 9070270862176306170334373)
        ·
          refine ⟨1700675786658057406937695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9070270862176306170334373 1700675786658057406937695)
          ·
            refine ⟨2551013679987086110406543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700675786658057406937695 2551013679987086110406543)
            ·
              refine ⟨3826520519980629165609815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551013679987086110406543 3826520519980629165609815)
              ·
                refine ⟨5739780779970943748414723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3826520519980629165609815 5739780779970943748414723)
                ·
                  refine ⟨8609671169956415622622085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5739780779970943748414723 8609671169956415622622085)
                  ·
                    refine ⟨1614313344366827929241641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8609671169956415622622085 1614313344366827929241641)
                    ·
                      refine ⟨1210735008275120946931231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614313344366827929241641 1210735008275120946931231)
                      ·
                        rfl

theorem cell23_2357898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_2357898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357898 prefixEnd_2357898 := by exact prefixLift 2357898
  have htrace : WordTrace (prefixWord ++ tailWord_2357898) baseStart_2357898 baseEnd_2357898 := by
    simpa [prefixWord, tailWord_2357898, baseEnd_2357898] using wordTrace_append hprefix tailTrace_2357898
  have hstable : (prefixWord ++ tailWord_2357898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357898).length < 2 ^ (prefixWord ++ tailWord_2357898).sum := by decide
  have hdescent : baseEnd_2357898 < baseStart_2357898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357900 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_2357900 : Nat := 118140960795 + 2357900 * 2 ^ 59
def prefixEnd_2357900 : Nat := 4983230072969 + 3 ^ 40 * 2357900 * 2
def baseEnd_2357900 : Nat := 403578678412143313035407

theorem tailTrace_2357900 : CollatzResearch.WordTrace tailWord_2357900 prefixEnd_2357900 403578678412143313035407 := by
  unfold tailWord_2357900
  simp only [CollatzResearch.WordTrace]
  refine ⟨42999839078869236052371577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57333118771825648069828769 42999839078869236052371577)
  ·
    refine ⟨32249879309151927039278683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42999839078869236052371577 32249879309151927039278683)
    ·
      refine ⟨48374818963727890558918025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32249879309151927039278683 48374818963727890558918025)
      ·
        refine ⟨36281114222795917919188519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48374818963727890558918025 36281114222795917919188519)
        ·
          refine ⟨54421671334193876878782779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36281114222795917919188519 54421671334193876878782779)
          ·
            refine ⟨81632507001290815318174169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54421671334193876878782779 81632507001290815318174169)
            ·
              refine ⟨61224380250968111488630627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81632507001290815318174169 61224380250968111488630627)
              ·
                refine ⟨91836570376452167232945941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61224380250968111488630627 91836570376452167232945941)
                ·
                  refine ⟨4304839236396195339044341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91836570376452167232945941 4304839236396195339044341)
                  ·
                    refine ⟨403578678412143313035407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4304839236396195339044341 403578678412143313035407)
                    ·
                      rfl

theorem cell23_2357900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_2357900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357900 prefixEnd_2357900 := by exact prefixLift 2357900
  have htrace : WordTrace (prefixWord ++ tailWord_2357900) baseStart_2357900 baseEnd_2357900 := by
    simpa [prefixWord, tailWord_2357900, baseEnd_2357900] using wordTrace_append hprefix tailTrace_2357900
  have hstable : (prefixWord ++ tailWord_2357900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357900).length < 2 ^ (prefixWord ++ tailWord_2357900).sum := by decide
  have hdescent : baseEnd_2357900 < baseStart_2357900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357921 : List Nat := [1, 2, 3, 3, 3, 2, 1, 3, 5]
def baseStart_2357921 : Nat := 118140960795 + 2357921 * 2 ^ 59
def prefixEnd_2357921 : Nat := 4983230072969 + 3 ^ 40 * 2357921 * 2
def baseEnd_2357921 : Nat := 134527424258908261882625

theorem tailTrace_2357921 : CollatzResearch.WordTrace tailWord_2357921 prefixEnd_2357921 134527424258908261882625 := by
  unfold tailWord_2357921
  simp only [CollatzResearch.WordTrace]
  refine ⟨86000444090662392691257617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57333629393774928460838411 86000444090662392691257617)
  ·
    refine ⟨64500333067996794518443213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86000444090662392691257617 64500333067996794518443213)
    ·
      refine ⟨24187624900498797944416205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64500333067996794518443213 24187624900498797944416205)
      ·
        refine ⟨9070359337687049229156077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24187624900498797944416205 9070359337687049229156077)
        ·
          refine ⟨3401384751632643460933529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9070359337687049229156077 3401384751632643460933529)
          ·
            refine ⟨2551038563724482595700147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3401384751632643460933529 2551038563724482595700147)
            ·
              refine ⟨3826557845586723893550221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551038563724482595700147 3826557845586723893550221)
              ·
                refine ⟨1434959192095021460081333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3826557845586723893550221 1434959192095021460081333)
                ·
                  refine ⟨134527424258908261882625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1434959192095021460081333 134527424258908261882625)
                  ·
                    rfl

theorem cell23_2357921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 5].length) (baseStart_2357921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357921 prefixEnd_2357921 := by exact prefixLift 2357921
  have htrace : WordTrace (prefixWord ++ tailWord_2357921) baseStart_2357921 baseEnd_2357921 := by
    simpa [prefixWord, tailWord_2357921, baseEnd_2357921] using wordTrace_append hprefix tailTrace_2357921
  have hstable : (prefixWord ++ tailWord_2357921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357921).length < 2 ^ (prefixWord ++ tailWord_2357921).sum := by decide
  have hdescent : baseEnd_2357921 < baseStart_2357921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357934 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2357934 : Nat := 118140960795 + 2357934 * 2 ^ 59
def prefixEnd_2357934 : Nat := 4983230072969 + 3 ^ 40 * 2357934 * 2
def baseEnd_2357934 : Nat := 403584497859560935360355

theorem tailTrace_2357934 : CollatzResearch.WordTrace tailWord_2357934 prefixEnd_2357934 403584497859560935360355 := by
  unfold tailWord_2357934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10750114779951911988935107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57333945493076863940987237 10750114779951911988935107)
  ·
    refine ⟨16125172169927867983402661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10750114779951911988935107 16125172169927867983402661)
    ·
      refine ⟨3023469781861475246887999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16125172169927867983402661 3023469781861475246887999)
      ·
        refine ⟨4535204672792212870331999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023469781861475246887999 4535204672792212870331999)
        ·
          refine ⟨6802807009188319305497999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4535204672792212870331999 6802807009188319305497999)
          ·
            refine ⟨10204210513782478958246999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6802807009188319305497999 10204210513782478958246999)
            ·
              refine ⟨15306315770673718437370499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10204210513782478958246999 15306315770673718437370499)
              ·
                refine ⟨22959473656010577656055749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15306315770673718437370499 22959473656010577656055749)
                ·
                  refine ⟨4304901310501983310510453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22959473656010577656055749 4304901310501983310510453)
                  ·
                    refine ⟨403584497859560935360355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4304901310501983310510453 403584497859560935360355)
                    ·
                      rfl

theorem cell23_2357934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2357934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357934 prefixEnd_2357934 := by exact prefixLift 2357934
  have htrace : WordTrace (prefixWord ++ tailWord_2357934) baseStart_2357934 baseEnd_2357934 := by
    simpa [prefixWord, tailWord_2357934, baseEnd_2357934] using wordTrace_append hprefix tailTrace_2357934
  have hstable : (prefixWord ++ tailWord_2357934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357934).length < 2 ^ (prefixWord ++ tailWord_2357934).sum := by decide
  have hdescent : baseEnd_2357934 < baseStart_2357934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357997 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2357997 : Nat := 118140960795 + 2357997 * 2 ^ 59
def prefixEnd_2357997 : Nat := 4983230072969 + 3 ^ 40 * 2357997 * 2
def baseEnd_2357997 : Nat := 1210785842859916059593275

theorem tailTrace_2357997 : CollatzResearch.WordTrace tailWord_2357997 prefixEnd_2357997 1210785842859916059593275 := by
  unfold tailWord_2357997
  simp only [CollatzResearch.WordTrace]
  refine ⟨86003216038387057671024245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57335477358924705114016163 86003216038387057671024245)
  ·
    refine ⟨8062801503598786656658523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86003216038387057671024245 8062801503598786656658523)
    ·
      refine ⟨12094202255398179984987785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8062801503598786656658523 12094202255398179984987785)
      ·
        refine ⟨9070651691548634988740839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12094202255398179984987785 9070651691548634988740839)
        ·
          refine ⟨13605977537322952483111259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9070651691548634988740839 13605977537322952483111259)
          ·
            refine ⟨20408966305984428724666889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13605977537322952483111259 20408966305984428724666889)
            ·
              refine ⟨15306724729488321543500167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20408966305984428724666889 15306724729488321543500167)
              ·
                refine ⟨22960087094232482315250251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15306724729488321543500167 22960087094232482315250251)
                ·
                  refine ⟨34440130641348723472875377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22960087094232482315250251 34440130641348723472875377)
                  ·
                    refine ⟨25830097981011542604656533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34440130641348723472875377 25830097981011542604656533)
                    ·
                      refine ⟨1210785842859916059593275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25830097981011542604656533 1210785842859916059593275)
                      ·
                        rfl

theorem cell23_2357997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2357997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357997 prefixEnd_2357997 := by exact prefixLift 2357997
  have htrace : WordTrace (prefixWord ++ tailWord_2357997) baseStart_2357997 baseEnd_2357997 := by
    simpa [prefixWord, tailWord_2357997, baseEnd_2357997] using wordTrace_append hprefix tailTrace_2357997
  have hstable : (prefixWord ++ tailWord_2357997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357997).length < 2 ^ (prefixWord ++ tailWord_2357997).sum := by decide
  have hdescent : baseEnd_2357997 < baseStart_2357997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357998 : List Nat := [4, 1, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_2357998 : Nat := 118140960795 + 2357998 * 2 ^ 59
def prefixEnd_2357998 : Nat := 4983230072969 + 3 ^ 40 * 2357998 * 2
def baseEnd_2357998 : Nat := 403595452113523518560257

theorem tailTrace_2357998 : CollatzResearch.WordTrace tailWord_2357998 prefixEnd_2357998 403595452113523518560257 := by
  unfold tailWord_2357998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10750406563922929355226331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57335501674255623227873765 10750406563922929355226331)
  ·
    refine ⟨16125609845884394032839497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10750406563922929355226331 16125609845884394032839497)
    ·
      refine ⟨12094207384413295524629623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16125609845884394032839497 12094207384413295524629623)
      ·
        refine ⟨18141311076619943286944435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12094207384413295524629623 18141311076619943286944435)
        ·
          refine ⟨27211966614929914930416653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18141311076619943286944435 27211966614929914930416653)
          ·
            refine ⟨10204487480598718098906245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27211966614929914930416653 10204487480598718098906245)
            ·
              refine ⟨1913341402612259643544921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10204487480598718098906245 1913341402612259643544921)
              ·
                refine ⟨1435006051959194732658691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913341402612259643544921 1435006051959194732658691)
                ·
                  refine ⟨2152509077938792098988037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435006051959194732658691 2152509077938792098988037)
                  ·
                    refine ⟨403595452113523518560257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2152509077938792098988037 403595452113523518560257)
                    ·
                      rfl

theorem cell23_2357998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_2357998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2357998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2357998 prefixEnd_2357998 := by exact prefixLift 2357998
  have htrace : WordTrace (prefixWord ++ tailWord_2357998) baseStart_2357998 baseEnd_2357998 := by
    simpa [prefixWord, tailWord_2357998, baseEnd_2357998] using wordTrace_append hprefix tailTrace_2357998
  have hstable : (prefixWord ++ tailWord_2357998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357998).length < 2 ^ (prefixWord ++ tailWord_2357998).sum := by decide
  have hdescent : baseEnd_2357998 < baseStart_2357998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358005 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2358005 : Nat := 118140960795 + 2358005 * 2 ^ 59
def prefixEnd_2358005 : Nat := 4983230072969 + 3 ^ 40 * 2358005 * 2
def baseEnd_2358005 : Nat := 1210789950705152028293239

theorem tailTrace_2358005 : CollatzResearch.WordTrace tailWord_2358005 prefixEnd_2358005 1210789950705152028293239 := by
  unfold tailWord_2358005
  simp only [CollatzResearch.WordTrace]
  refine ⟨86003507822358075037315469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57335671881572050024876979 86003507822358075037315469)
  ·
    refine ⟨32251315433384278138993301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86003507822358075037315469 32251315433384278138993301)
    ·
      refine ⟨1511780410939888037765311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32251315433384278138993301 1511780410939888037765311)
      ·
        refine ⟨2267670616409832056647967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511780410939888037765311 2267670616409832056647967)
        ·
          refine ⟨3401505924614748084971951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267670616409832056647967 3401505924614748084971951)
          ·
            refine ⟨5102258886922122127457927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401505924614748084971951 5102258886922122127457927)
            ·
              refine ⟨7653388330383183191186891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102258886922122127457927 7653388330383183191186891)
              ·
                refine ⟨11480082495574774786780337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7653388330383183191186891 11480082495574774786780337)
                ·
                  refine ⟨8610061871681081090085253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11480082495574774786780337 8610061871681081090085253)
                  ·
                    refine ⟨1614386600940202704390985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8610061871681081090085253 1614386600940202704390985)
                    ·
                      refine ⟨1210789950705152028293239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614386600940202704390985 1210789950705152028293239)
                      ·
                        rfl

theorem cell23_2358005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2358005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358005 prefixEnd_2358005 := by exact prefixLift 2358005
  have htrace : WordTrace (prefixWord ++ tailWord_2358005) baseStart_2358005 baseEnd_2358005 := by
    simpa [prefixWord, tailWord_2358005, baseEnd_2358005] using wordTrace_append hprefix tailTrace_2358005
  have hstable : (prefixWord ++ tailWord_2358005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358005).length < 2 ^ (prefixWord ++ tailWord_2358005).sum := by decide
  have hdescent : baseEnd_2358005 < baseStart_2358005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358037 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_2358037 : Nat := 118140960795 + 2358037 * 2 ^ 59
def prefixEnd_2358037 : Nat := 4983230072969 + 3 ^ 40 * 2358037 * 2
def baseEnd_2358037 : Nat := 403602127362031967697697

theorem tailTrace_2358037 : CollatzResearch.WordTrace tailWord_2358037 prefixEnd_2358037 403602127362031967697697 := by
  unfold tailWord_2358037
  simp only [CollatzResearch.WordTrace]
  refine ⟨86004674958242144502480365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57336449972161429668320243 86004674958242144502480365)
  ·
    refine ⟨32251753109340804188430137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86004674958242144502480365 32251753109340804188430137)
    ·
      refine ⟨24188814832005603141322603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32251753109340804188430137 24188814832005603141322603)
      ·
        refine ⟨36283222248008404711983905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24188814832005603141322603 36283222248008404711983905)
        ·
          refine ⟨27212416686006303533987929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36283222248008404711983905 27212416686006303533987929)
          ·
            refine ⟨20409312514504727650490947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27212416686006303533987929 20409312514504727650490947)
            ·
              refine ⟨30613968771757091475736421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20409312514504727650490947 30613968771757091475736421)
              ·
                refine ⟨5740119144704454651700579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30613968771757091475736421 5740119144704454651700579)
                ·
                  refine ⟨8610178717056681977550869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5740119144704454651700579 8610178717056681977550869)
                  ·
                    refine ⟨403602127362031967697697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8610178717056681977550869 403602127362031967697697)
                    ·
                      rfl

theorem cell23_2358037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_2358037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358037 prefixEnd_2358037 := by exact prefixLift 2358037
  have htrace : WordTrace (prefixWord ++ tailWord_2358037) baseStart_2358037 baseEnd_2358037 := by
    simpa [prefixWord, tailWord_2358037, baseEnd_2358037] using wordTrace_append hprefix tailTrace_2358037
  have hstable : (prefixWord ++ tailWord_2358037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358037).length < 2 ^ (prefixWord ++ tailWord_2358037).sum := by decide
  have hdescent : baseEnd_2358037 < baseStart_2358037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358071 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 2, 4]
def baseStart_2358071 : Nat := 118140960795 + 2358071 * 2 ^ 59
def prefixEnd_2358071 : Nat := 4983230072969 + 3 ^ 40 * 2358071 * 2
def baseEnd_2358071 : Nat := 403607946809449590022645

theorem tailTrace_2358071 : CollatzResearch.WordTrace tailWord_2358071 prefixEnd_2358071 403607946809449590022645 := by
  unfold tailWord_2358071
  simp only [CollatzResearch.WordTrace]
  refine ⟨86005915040118968309218067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57337276693412645539478711 86005915040118968309218067)
  ·
    refine ⟨129008872560178452463827101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86005915040118968309218067 129008872560178452463827101)
    ·
      refine ⟨48378327210066919673935163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129008872560178452463827101 48378327210066919673935163)
      ·
        refine ⟨72567490815100379510902745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48378327210066919673935163 72567490815100379510902745)
        ·
          refine ⟨54425618111325284633177059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72567490815100379510902745 54425618111325284633177059)
          ·
            refine ⟨81638427166987926949765589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54425618111325284633177059 81638427166987926949765589)
            ·
              refine ⟨1913400636726279537885131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 81638427166987926949765589 1913400636726279537885131)
              ·
                refine ⟨2870100955089419306827697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913400636726279537885131 2870100955089419306827697)
                ·
                  refine ⟨2152575716317064480120773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870100955089419306827697 2152575716317064480120773)
                  ·
                    refine ⟨403607946809449590022645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2152575716317064480120773 403607946809449590022645)
                    ·
                      rfl

theorem cell23_2358071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_2358071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358071 prefixEnd_2358071 := by exact prefixLift 2358071
  have htrace : WordTrace (prefixWord ++ tailWord_2358071) baseStart_2358071 baseEnd_2358071 := by
    simpa [prefixWord, tailWord_2358071, baseEnd_2358071] using wordTrace_append hprefix tailTrace_2358071
  have hstable : (prefixWord ++ tailWord_2358071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358071).length < 2 ^ (prefixWord ++ tailWord_2358071).sum := by decide
  have hdescent : baseEnd_2358071 < baseStart_2358071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358074 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_2358074 : Nat := 118140960795 + 2358074 * 2 ^ 59
def prefixEnd_2358074 : Nat := 4983230072969 + 3 ^ 40 * 2358074 * 2
def baseEnd_2358074 : Nat := 1210825380870312258330421

theorem tailTrace_2358074 : CollatzResearch.WordTrace tailWord_2358074 prefixEnd_2358074 1210825380870312258330421 := by
  unfold tailWord_2358074
  simp only [CollatzResearch.WordTrace]
  refine ⟨21501506114777024955394319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57337349639405399881051517 21501506114777024955394319)
  ·
    refine ⟨32252259172165537433091479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21501506114777024955394319 32252259172165537433091479)
    ·
      refine ⟨48378388758248306149637219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32252259172165537433091479 48378388758248306149637219)
      ·
        refine ⟨72567583137372459224455829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48378388758248306149637219 72567583137372459224455829)
        ·
          refine ⟨3401605459564334026146367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72567583137372459224455829 3401605459564334026146367)
          ·
            refine ⟨5102408189346501039219551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401605459564334026146367 5102408189346501039219551)
            ·
              refine ⟨7653612284019751558829327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102408189346501039219551 7653612284019751558829327)
              ·
                refine ⟨11480418426029627338243991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7653612284019751558829327 11480418426029627338243991)
                ·
                  refine ⟨17220627639044441007365987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11480418426029627338243991 17220627639044441007365987)
                  ·
                    refine ⟨25830941458566661511048981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17220627639044441007365987 25830941458566661511048981)
                    ·
                      refine ⟨1210825380870312258330421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25830941458566661511048981 1210825380870312258330421)
                      ·
                        rfl

theorem cell23_2358074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_2358074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358074 prefixEnd_2358074 := by exact prefixLift 2358074
  have htrace : WordTrace (prefixWord ++ tailWord_2358074) baseStart_2358074 baseEnd_2358074 := by
    simpa [prefixWord, tailWord_2358074, baseEnd_2358074] using wordTrace_append hprefix tailTrace_2358074
  have hstable : (prefixWord ++ tailWord_2358074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358074).length < 2 ^ (prefixWord ++ tailWord_2358074).sum := by decide
  have hdescent : baseEnd_2358074 < baseStart_2358074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358078 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2358078 : Nat := 118140960795 + 2358078 * 2 ^ 59
def prefixEnd_2358078 : Nat := 4983230072969 + 3 ^ 40 * 2358078 * 2
def baseEnd_2358078 : Nat := 1210827434792930242680403

theorem tailTrace_2358078 : CollatzResearch.WordTrace tailWord_2358078 prefixEnd_2358078 1210827434792930242680403 := by
  unfold tailWord_2358078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10750771293886701063090361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57337446900729072336481925 10750771293886701063090361)
  ·
    refine ⟨8063078470415025797317771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10750771293886701063090361 8063078470415025797317771)
    ·
      refine ⟨12094617705622538695976657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8063078470415025797317771 12094617705622538695976657)
      ·
        refine ⟨9070963279216904021982493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12094617705622538695976657 9070963279216904021982493)
        ·
          refine ⟨3401611229706339008243435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9070963279216904021982493 3401611229706339008243435)
          ·
            refine ⟨5102416844559508512365153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401611229706339008243435 5102416844559508512365153)
            ·
              refine ⟨3826812633419631384273865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5102416844559508512365153 3826812633419631384273865)
              ·
                refine ⟨2870109475064723538205399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826812633419631384273865 2870109475064723538205399)
                ·
                  refine ⟨4305164212597085307308099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870109475064723538205399 4305164212597085307308099)
                  ·
                    refine ⟨6457746318895627960962149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4305164212597085307308099 6457746318895627960962149)
                    ·
                      refine ⟨1210827434792930242680403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6457746318895627960962149 1210827434792930242680403)
                      ·
                        rfl

theorem cell23_2358078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2358078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358078 prefixEnd_2358078 := by exact prefixLift 2358078
  have htrace : WordTrace (prefixWord ++ tailWord_2358078) baseStart_2358078 baseEnd_2358078 := by
    simpa [prefixWord, tailWord_2358078, baseEnd_2358078] using wordTrace_append hprefix tailTrace_2358078
  have hstable : (prefixWord ++ tailWord_2358078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358078).length < 2 ^ (prefixWord ++ tailWord_2358078).sum := by decide
  have hdescent : baseEnd_2358078 < baseStart_2358078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358094 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_2358094 : Nat := 118140960795 + 2358094 * 2 ^ 59
def prefixEnd_2358094 : Nat := 4983230072969 + 3 ^ 40 * 2358094 * 2
def baseEnd_2358094 : Nat := 1210835650483402180080329

theorem tailTrace_2358094 : CollatzResearch.WordTrace tailWord_2358094 prefixEnd_2358094 1210835650483402180080329 := by
  unfold tailWord_2358094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10750844239879455404663167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57337835946023762158203557 10750844239879455404663167)
  ·
    refine ⟨16126266359819183106994751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10750844239879455404663167 16126266359819183106994751)
    ·
      refine ⟨24189399539728774660492127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16126266359819183106994751 24189399539728774660492127)
      ·
        refine ⟨36284099309593161990738191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24189399539728774660492127 36284099309593161990738191)
        ·
          refine ⟨54426148964389742986107287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36284099309593161990738191 54426148964389742986107287)
          ·
            refine ⟨81639223446584614479160931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54426148964389742986107287 81639223446584614479160931)
            ·
              refine ⟨122458835169876921718741397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81639223446584614479160931 122458835169876921718741397)
              ·
                refine ⟨5740257898587980705566003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122458835169876921718741397 5740257898587980705566003)
                ·
                  refine ⟨8610386847881971058349005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5740257898587980705566003 8610386847881971058349005)
                  ·
                    refine ⟨3228895067955739146880877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8610386847881971058349005 3228895067955739146880877)
                    ·
                      refine ⟨1210835650483402180080329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228895067955739146880877 1210835650483402180080329)
                      ·
                        rfl

theorem cell23_2358094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_2358094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358094 prefixEnd_2358094 := by exact prefixLift 2358094
  have htrace : WordTrace (prefixWord ++ tailWord_2358094) baseStart_2358094 baseEnd_2358094 := by
    simpa [prefixWord, tailWord_2358094, baseEnd_2358094] using wordTrace_append hprefix tailTrace_2358094
  have hstable : (prefixWord ++ tailWord_2358094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358094).length < 2 ^ (prefixWord ++ tailWord_2358094).sum := by decide
  have hdescent : baseEnd_2358094 < baseStart_2358094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358111 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 3]
def baseStart_2358111 : Nat := 118140960795 + 2358111 * 2 ^ 59
def prefixEnd_2358111 : Nat := 4983230072969 + 3 ^ 40 * 2358111 * 2
def baseEnd_2358111 : Nat := 1210844379654528613567751

theorem tailTrace_2358111 : CollatzResearch.WordTrace tailWord_2358111 prefixEnd_2358111 1210844379654528613567751 := by
  unfold tailWord_2358111
  simp only [CollatzResearch.WordTrace]
  refine ⟨86007373959974055140674187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57338249306649370093782791 86007373959974055140674187)
  ·
    refine ⟨129011060939961082711011281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86007373959974055140674187 129011060939961082711011281)
    ·
      refine ⟨96758295704970812033258461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129011060939961082711011281 96758295704970812033258461)
      ·
        refine ⟨36284360889364054512471923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96758295704970812033258461 36284360889364054512471923)
        ·
          refine ⟨54426541334046081768707885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36284360889364054512471923 54426541334046081768707885)
          ·
            refine ⟨20409953000267280663265457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54426541334046081768707885 20409953000267280663265457)
            ·
              refine ⟨15307464750200460497449093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20409953000267280663265457 15307464750200460497449093)
              ·
                refine ⟨2870149640662586343271705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15307464750200460497449093 2870149640662586343271705)
                ·
                  refine ⟨2152612230496939757453779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870149640662586343271705 2152612230496939757453779)
                  ·
                    refine ⟨3228918345745409636180669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152612230496939757453779 3228918345745409636180669)
                    ·
                      refine ⟨1210844379654528613567751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228918345745409636180669 1210844379654528613567751)
                      ·
                        rfl

theorem cell23_2358111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_2358111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358111 prefixEnd_2358111 := by exact prefixLift 2358111
  have htrace : WordTrace (prefixWord ++ tailWord_2358111) baseStart_2358111 baseEnd_2358111 := by
    simpa [prefixWord, tailWord_2358111, baseEnd_2358111] using wordTrace_append hprefix tailTrace_2358111
  have hstable : (prefixWord ++ tailWord_2358111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358111).length < 2 ^ (prefixWord ++ tailWord_2358111).sum := by decide
  have hdescent : baseEnd_2358111 < baseStart_2358111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358127 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 2, 6]
def baseStart_2358127 : Nat := 118140960795 + 2358127 * 2 ^ 59
def prefixEnd_2358127 : Nat := 4983230072969 + 3 ^ 40 * 2358127 * 2
def baseEnd_2358127 : Nat := 403617531781666850322559

theorem tailTrace_2358127 : CollatzResearch.WordTrace tailWord_2358127 prefixEnd_2358127 403617531781666850322559 := by
  unfold tailWord_2358127
  simp only [CollatzResearch.WordTrace]
  refine ⟨86007957527916089873256635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57338638351944059915504423 86007957527916089873256635)
  ·
    refine ⟨129011936291874134809884953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86007957527916089873256635 129011936291874134809884953)
    ·
      refine ⟨96758952218905601107413715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129011936291874134809884953 96758952218905601107413715)
      ·
        refine ⟨145138428328358401661120573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96758952218905601107413715 145138428328358401661120573)
        ·
          refine ⟨54426910623134400622920215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145138428328358401661120573 54426910623134400622920215)
          ·
            refine ⟨81640365934701600934380323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54426910623134400622920215 81640365934701600934380323)
            ·
              refine ⟨122460548902052401401570485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81640365934701600934380323 122460548902052401401570485)
              ·
                refine ⟨11480676459567412631397233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122460548902052401401570485 11480676459567412631397233)
                ·
                  refine ⟨8610507344675559473547925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11480676459567412631397233 8610507344675559473547925)
                  ·
                    refine ⟨403617531781666850322559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8610507344675559473547925 403617531781666850322559)
                    ·
                      rfl

theorem cell23_2358127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_2358127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358127 prefixEnd_2358127 := by exact prefixLift 2358127
  have htrace : WordTrace (prefixWord ++ tailWord_2358127) baseStart_2358127 baseEnd_2358127 := by
    simpa [prefixWord, tailWord_2358127, baseEnd_2358127] using wordTrace_append hprefix tailTrace_2358127
  have hstable : (prefixWord ++ tailWord_2358127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358127).length < 2 ^ (prefixWord ++ tailWord_2358127).sum := by decide
  have hdescent : baseEnd_2358127 < baseStart_2358127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358128 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 2, 1, 3]
def baseStart_2358128 : Nat := 118140960795 + 2358128 * 2 ^ 59
def prefixEnd_2358128 : Nat := 4983230072969 + 3 ^ 40 * 2358128 * 2
def baseEnd_2358128 : Nat := 1210853108825655047055173

theorem tailTrace_2358128 : CollatzResearch.WordTrace tailWord_2358128 prefixEnd_2358128 1210853108825655047055173 := by
  unfold tailWord_2358128
  simp only [CollatzResearch.WordTrace]
  refine ⟨43003997000456233522021519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57338662667274978029362025 43003997000456233522021519)
  ·
    refine ⟨64505995500684350283032279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43003997000456233522021519 64505995500684350283032279)
    ·
      refine ⟨96758993251026525424548419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64505995500684350283032279 96758993251026525424548419)
      ·
        refine ⟨145138489876539788136822629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96758993251026525424548419 145138489876539788136822629)
        ·
          refine ⟨27213466851851210275654243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145138489876539788136822629 27213466851851210275654243)
          ·
            refine ⟨40820200277776815413481365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27213466851851210275654243 40820200277776815413481365)
            ·
              refine ⟨1913446888020788222506939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40820200277776815413481365 1913446888020788222506939)
              ·
                refine ⟨2870170332031182333760409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913446888020788222506939 2870170332031182333760409)
                ·
                  refine ⟨2152627749023386750320307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870170332031182333760409 2152627749023386750320307)
                  ·
                    refine ⟨3228941623535080125480461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152627749023386750320307 3228941623535080125480461)
                    ·
                      refine ⟨1210853108825655047055173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3228941623535080125480461 1210853108825655047055173)
                      ·
                        rfl

theorem cell23_2358128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 1, 3].length) (baseStart_2358128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358128 prefixEnd_2358128 := by exact prefixLift 2358128
  have htrace : WordTrace (prefixWord ++ tailWord_2358128) baseStart_2358128 baseEnd_2358128 := by
    simpa [prefixWord, tailWord_2358128, baseEnd_2358128] using wordTrace_append hprefix tailTrace_2358128
  have hstable : (prefixWord ++ tailWord_2358128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358128).length < 2 ^ (prefixWord ++ tailWord_2358128).sum := by decide
  have hdescent : baseEnd_2358128 < baseStart_2358128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358151 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_2358151 : Nat := 118140960795 + 2358151 * 2 ^ 59
def prefixEnd_2358151 : Nat := 4983230072969 + 3 ^ 40 * 2358151 * 2
def baseEnd_2358151 : Nat := 1210864918880708457067567

theorem tailTrace_2358151 : CollatzResearch.WordTrace tailWord_2358151 prefixEnd_2358151 1210864918880708457067567 := by
  unfold tailWord_2358151
  simp only [CollatzResearch.WordTrace]
  refine ⟨86008832879829141972130307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57339221919886094648086871 86008832879829141972130307)
  ·
    refine ⟨129013249319743712958195461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86008832879829141972130307 129013249319743712958195461)
    ·
      refine ⟨24189984247451946179661649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129013249319743712958195461 24189984247451946179661649)
      ·
        refine ⟨18142488185588959634746237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24189984247451946179661649 18142488185588959634746237)
        ·
          refine ⟨6803433069595859863029839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18142488185588959634746237 6803433069595859863029839)
          ·
            refine ⟨10205149604393789794544759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6803433069595859863029839 10205149604393789794544759)
            ·
              refine ⟨15307724406590684691817139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10205149604393789794544759 15307724406590684691817139)
              ·
                refine ⟨22961586609886027037725709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15307724406590684691817139 22961586609886027037725709)
                ·
                  refine ⟨8610594978707260139147141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22961586609886027037725709 8610594978707260139147141)
                  ·
                    refine ⟨1614486558507611276090089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8610594978707260139147141 1614486558507611276090089)
                    ·
                      refine ⟨1210864918880708457067567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614486558507611276090089 1210864918880708457067567)
                      ·
                        rfl

theorem cell23_2358151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_2358151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358151 prefixEnd_2358151 := by exact prefixLift 2358151
  have htrace : WordTrace (prefixWord ++ tailWord_2358151) baseStart_2358151 baseEnd_2358151 := by
    simpa [prefixWord, tailWord_2358151, baseEnd_2358151] using wordTrace_append hprefix tailTrace_2358151
  have hstable : (prefixWord ++ tailWord_2358151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358151).length < 2 ^ (prefixWord ++ tailWord_2358151).sum := by decide
  have hdescent : baseEnd_2358151 < baseStart_2358151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358187 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 3, 7]
def baseStart_2358187 : Nat := 118140960795 + 2358187 * 2 ^ 59
def prefixEnd_2358187 : Nat := 4983230072969 + 3 ^ 40 * 2358187 * 2
def baseEnd_2358187 : Nat := 403627801394756772072467

theorem tailTrace_2358187 : CollatzResearch.WordTrace tailWord_2358187 prefixEnd_2358187 403627801394756772072467 := by
  unfold tailWord_2358187
  simp only [CollatzResearch.WordTrace]
  refine ⟨86010145907698720120440815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57340097271799146746960543 86010145907698720120440815)
  ·
    refine ⟨129015218861548080180661223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86010145907698720120440815 129015218861548080180661223)
    ·
      refine ⟨193522828292322120270991835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129015218861548080180661223 193522828292322120270991835)
      ·
        refine ⟨290284242438483180406487753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193522828292322120270991835 290284242438483180406487753)
        ·
          refine ⟨217713181828862385304865815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290284242438483180406487753 217713181828862385304865815)
          ·
            refine ⟨326569772743293577957298723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217713181828862385304865815 326569772743293577957298723)
            ·
              refine ⟨489854659114940366935948085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326569772743293577957298723 489854659114940366935948085)
              ·
                refine ⟨45923874292025659400245133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 489854659114940366935948085 45923874292025659400245133)
                ·
                  refine ⟨17221452859509622275091925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45923874292025659400245133 17221452859509622275091925)
                  ·
                    refine ⟨403627801394756772072467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17221452859509622275091925 403627801394756772072467)
                    ·
                      rfl

theorem cell23_2358187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_2358187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358187 prefixEnd_2358187 := by exact prefixLift 2358187
  have htrace : WordTrace (prefixWord ++ tailWord_2358187) baseStart_2358187 baseEnd_2358187 := by
    simpa [prefixWord, tailWord_2358187, baseEnd_2358187] using wordTrace_append hprefix tailTrace_2358187
  have hstable : (prefixWord ++ tailWord_2358187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358187).length < 2 ^ (prefixWord ++ tailWord_2358187).sum := by decide
  have hdescent : baseEnd_2358187 < baseStart_2358187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358224 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_2358224 : Nat := 118140960795 + 2358224 * 2 ^ 59
def prefixEnd_2358224 : Nat := 4983230072969 + 3 ^ 40 * 2358224 * 2
def baseEnd_2358224 : Nat := 1210902402968486671454731

theorem tailTrace_2358224 : CollatzResearch.WordTrace tailWord_2358224 prefixEnd_2358224 1210902402968486671454731 := by
  unfold tailWord_2358224
  simp only [CollatzResearch.WordTrace]
  refine ⟨43005747704282337719768863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57340996939043116959691817 43005747704282337719768863)
  ·
    refine ⟨64508621556423506579653295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43005747704282337719768863 64508621556423506579653295)
    ·
      refine ⟨96762932334635259869479943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64508621556423506579653295 96762932334635259869479943)
      ·
        refine ⟨145144398501952889804219915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96762932334635259869479943 145144398501952889804219915)
        ·
          refine ⟨217716597752929334706329873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145144398501952889804219915 217716597752929334706329873)
          ·
            refine ⟨163287448314697001029747405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217716597752929334706329873 163287448314697001029747405)
            ·
              refine ⟨61232793118011375386155277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163287448314697001029747405 61232793118011375386155277)
              ·
                refine ⟨22962297419254265769808229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61232793118011375386155277 22962297419254265769808229)
                ·
                  refine ⟨4305430766110174831839043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22962297419254265769808229 4305430766110174831839043)
                  ·
                    refine ⟨6458146149165262247758565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4305430766110174831839043 6458146149165262247758565)
                    ·
                      refine ⟨1210902402968486671454731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6458146149165262247758565 1210902402968486671454731)
                      ·
                        rfl

theorem cell23_2358224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_2358224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358224 prefixEnd_2358224 := by exact prefixLift 2358224
  have htrace : WordTrace (prefixWord ++ tailWord_2358224) baseStart_2358224 baseEnd_2358224 := by
    simpa [prefixWord, tailWord_2358224, baseEnd_2358224] using wordTrace_append hprefix tailTrace_2358224
  have hstable : (prefixWord ++ tailWord_2358224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358224).length < 2 ^ (prefixWord ++ tailWord_2358224).sum := by decide
  have hdescent : baseEnd_2358224 < baseStart_2358224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358325 : List Nat := [1, 3, 3, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_2358325 : Nat := 118140960795 + 2358325 * 2 ^ 59
def prefixEnd_2358325 : Nat := 4983230072969 + 3 ^ 40 * 2358325 * 2
def baseEnd_2358325 : Nat := 1210954264514590776291767

theorem tailTrace_2358325 : CollatzResearch.WordTrace tailWord_2358325 prefixEnd_2358325 1210954264514590776291767 := by
  unfold tailWord_2358325
  simp only [CollatzResearch.WordTrace]
  refine ⟨86015179181198769688964429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57343452787465846459309619 86015179181198769688964429)
  ·
    refine ⟨32255692192949538633361661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86015179181198769688964429 32255692192949538633361661)
    ·
      refine ⟨12095884572356076987510623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32255692192949538633361661 12095884572356076987510623)
      ·
        refine ⟨18143826858534115481265935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12095884572356076987510623 18143826858534115481265935)
        ·
          refine ⟨27215740287801173221898903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18143826858534115481265935 27215740287801173221898903)
          ·
            refine ⟨40823610431701759832848355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27215740287801173221898903 40823610431701759832848355)
            ·
              refine ⟨61235415647552639749272533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40823610431701759832848355 61235415647552639749272533)
              ·
                refine ⟨1435205054239514994123575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61235415647552639749272533 1435205054239514994123575)
                ·
                  refine ⟨2152807581359272491185363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435205054239514994123575 2152807581359272491185363)
                  ·
                    refine ⟨3229211372038908736778045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152807581359272491185363 3229211372038908736778045)
                    ·
                      refine ⟨1210954264514590776291767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3229211372038908736778045 1210954264514590776291767)
                      ·
                        rfl

theorem cell23_2358325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_2358325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358325 prefixEnd_2358325 := by exact prefixLift 2358325
  have htrace : WordTrace (prefixWord ++ tailWord_2358325) baseStart_2358325 baseEnd_2358325 := by
    simpa [prefixWord, tailWord_2358325, baseEnd_2358325] using wordTrace_append hprefix tailTrace_2358325
  have hstable : (prefixWord ++ tailWord_2358325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358325).length < 2 ^ (prefixWord ++ tailWord_2358325).sum := by decide
  have hdescent : baseEnd_2358325 < baseStart_2358325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358341 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_2358341 : Nat := 118140960795 + 2358341 * 2 ^ 59
def prefixEnd_2358341 : Nat := 4983230072969 + 3 ^ 40 * 2358341 * 2
def baseEnd_2358341 : Nat := 403654160068354237897231

theorem tailTrace_2358341 : CollatzResearch.WordTrace tailWord_2358341 prefixEnd_2358341 403654160068354237897231 := by
  unfold tailWord_2358341
  simp only [CollatzResearch.WordTrace]
  refine ⟨86015762749140804421546877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57343841832760536281031251 86015762749140804421546877)
  ·
    refine ⟨32255911030927801658080079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86015762749140804421546877 32255911030927801658080079)
    ·
      refine ⟨48383866546391702487120119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32255911030927801658080079 48383866546391702487120119)
      ·
        refine ⟨72575799819587553730680179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48383866546391702487120119 72575799819587553730680179)
        ·
          refine ⟨108863699729381330596020269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72575799819587553730680179 108863699729381330596020269)
          ·
            refine ⟨40823887398517998973507601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108863699729381330596020269 40823887398517998973507601)
            ·
              refine ⟨30617915548888499230130701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40823887398517998973507601 30617915548888499230130701)
              ·
                refine ⟨11481718330833187211299013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30617915548888499230130701 11481718330833187211299013)
                ·
                  refine ⟨2152822187031222602118565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11481718330833187211299013 2152822187031222602118565)
                  ·
                    refine ⟨403654160068354237897231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2152822187031222602118565 403654160068354237897231)
                    ·
                      rfl

theorem cell23_2358341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_2358341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358341 prefixEnd_2358341 := by exact prefixLift 2358341
  have htrace : WordTrace (prefixWord ++ tailWord_2358341) baseStart_2358341 baseEnd_2358341 := by
    simpa [prefixWord, tailWord_2358341, baseEnd_2358341] using wordTrace_append hprefix tailTrace_2358341
  have hstable : (prefixWord ++ tailWord_2358341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358341).length < 2 ^ (prefixWord ++ tailWord_2358341).sum := by decide
  have hdescent : baseEnd_2358341 < baseStart_2358341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358368 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3]
def baseStart_2358368 : Nat := 118140960795 + 2358368 * 2 ^ 59
def prefixEnd_2358368 : Nat := 4983230072969 + 3 ^ 40 * 2358368 * 2
def baseEnd_2358368 : Nat := 1210976344182734108054069

theorem tailTrace_2358368 : CollatzResearch.WordTrace tailWord_2358368 prefixEnd_2358368 1210976344182734108054069 := by
  unfold tailWord_2358368
  simp only [CollatzResearch.WordTrace]
  refine ⟨43008373760021494016389879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57344498346695325355186505 43008373760021494016389879)
  ·
    refine ⟨64512560640032241024584819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43008373760021494016389879 64512560640032241024584819)
    ·
      refine ⟨96768840960048361536877229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64512560640032241024584819 96768840960048361536877229)
      ·
        refine ⟨36288315360018135576328961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96768840960048361536877229 36288315360018135576328961)
        ·
          refine ⟨27216236520013601682246721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36288315360018135576328961 27216236520013601682246721)
          ·
            refine ⟨20412177390010201261685041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27216236520013601682246721 20412177390010201261685041)
            ·
              refine ⟨15309133042507650946263781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20412177390010201261685041 15309133042507650946263781)
              ·
                refine ⟨2870462445470184552424459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15309133042507650946263781 2870462445470184552424459)
                ·
                  refine ⟨4305693668205276828636689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870462445470184552424459 4305693668205276828636689)
                  ·
                    refine ⟨3229270251153957621477517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4305693668205276828636689 3229270251153957621477517)
                    ·
                      refine ⟨1210976344182734108054069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3229270251153957621477517 1210976344182734108054069)
                      ·
                        rfl

theorem cell23_2358368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_2358368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358368 prefixEnd_2358368 := by exact prefixLift 2358368
  have htrace : WordTrace (prefixWord ++ tailWord_2358368) baseStart_2358368 baseEnd_2358368 := by
    simpa [prefixWord, tailWord_2358368, baseEnd_2358368] using wordTrace_append hprefix tailTrace_2358368
  have hstable : (prefixWord ++ tailWord_2358368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358368).length < 2 ^ (prefixWord ++ tailWord_2358368).sum := by decide
  have hdescent : baseEnd_2358368 < baseStart_2358368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358378 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2358378 : Nat := 118140960795 + 2358378 * 2 ^ 59
def prefixEnd_2358378 : Nat := 4983230072969 + 3 ^ 40 * 2358378 * 2
def baseEnd_2358378 : Nat := 1210981478989279068929023

theorem tailTrace_2358378 : CollatzResearch.WordTrace tailWord_2358378 prefixEnd_2358378 1210981478989279068929023 := by
  unfold tailWord_2358378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21504278062501689935160947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57344741500004506493762525 21504278062501689935160947)
  ·
    refine ⟨32256417093752534902741421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21504278062501689935160947 32256417093752534902741421)
    ·
      refine ⟨12096156410157200588528033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32256417093752534902741421 12096156410157200588528033)
      ·
        refine ⟨9072117307617900441396025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12096156410157200588528033 9072117307617900441396025)
        ·
          refine ⟨6804087980713425331047019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9072117307617900441396025 6804087980713425331047019)
          ·
            refine ⟨10206131971070137996570529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804087980713425331047019 10206131971070137996570529)
            ·
              refine ⟨7654598978302603497427897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10206131971070137996570529 7654598978302603497427897)
              ·
                refine ⟨5740949233726952623070923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7654598978302603497427897 5740949233726952623070923)
                ·
                  refine ⟨8611423850590428934606385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5740949233726952623070923 8611423850590428934606385)
                  ·
                    refine ⟨6458567887942821700954789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8611423850590428934606385 6458567887942821700954789)
                    ·
                      refine ⟨1210981478989279068929023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6458567887942821700954789 1210981478989279068929023)
                      ·
                        rfl

theorem cell23_2358378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2358378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358378 prefixEnd_2358378 := by exact prefixLift 2358378
  have htrace : WordTrace (prefixWord ++ tailWord_2358378) baseStart_2358378 baseEnd_2358378 := by
    simpa [prefixWord, tailWord_2358378, baseEnd_2358378] using wordTrace_append hprefix tailTrace_2358378
  have hstable : (prefixWord ++ tailWord_2358378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358378).length < 2 ^ (prefixWord ++ tailWord_2358378).sum := by decide
  have hdescent : baseEnd_2358378 < baseStart_2358378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358382 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_2358382 : Nat := 118140960795 + 2358382 * 2 ^ 59
def prefixEnd_2358382 : Nat := 4983230072969 + 3 ^ 40 * 2358382 * 2
def baseEnd_2358382 : Nat := 1210983532911897053279005

theorem tailTrace_2358382 : CollatzResearch.WordTrace tailWord_2358382 prefixEnd_2358382 1210983532911897053279005 := by
  unfold tailWord_2358382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752157267749033552973675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57344838761328178949192933 10752157267749033552973675)
  ·
    refine ⟨16128235901623550329460513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10752157267749033552973675 16128235901623550329460513)
    ·
      refine ⟨12096176926217662747095385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16128235901623550329460513 12096176926217662747095385)
      ·
        refine ⟨9072132694663247060321539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12096176926217662747095385 9072132694663247060321539)
        ·
          refine ⟨13608199041994870590482309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072132694663247060321539 13608199041994870590482309)
          ·
            refine ⟨2551537320374038235715433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13608199041994870590482309 2551537320374038235715433)
            ·
              refine ⟨1913652990280528676786575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2551537320374038235715433 1913652990280528676786575)
              ·
                refine ⟨2870479485420793015179863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913652990280528676786575 2870479485420793015179863)
                ·
                  refine ⟨4305719228131189522769795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870479485420793015179863 4305719228131189522769795)
                  ·
                    refine ⟨6458578842196784284154693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4305719228131189522769795 6458578842196784284154693)
                    ·
                      refine ⟨1210983532911897053279005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6458578842196784284154693 1210983532911897053279005)
                      ·
                        rfl

theorem cell23_2358382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_2358382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358382 prefixEnd_2358382 := by exact prefixLift 2358382
  have htrace : WordTrace (prefixWord ++ tailWord_2358382) baseStart_2358382 baseEnd_2358382 := by
    simpa [prefixWord, tailWord_2358382, baseEnd_2358382] using wordTrace_append hprefix tailTrace_2358382
  have hstable : (prefixWord ++ tailWord_2358382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358382).length < 2 ^ (prefixWord ++ tailWord_2358382).sum := by decide
  have hdescent : baseEnd_2358382 < baseStart_2358382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358441 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 3]
def baseStart_2358441 : Nat := 118140960795 + 2358441 * 2 ^ 59
def prefixEnd_2358441 : Nat := 4983230072969 + 3 ^ 40 * 2358441 * 2
def baseEnd_2358441 : Nat := 1211013828270512322441233

theorem tailTrace_2358441 : CollatzResearch.WordTrace tailWord_2358441 prefixEnd_2358441 1211013828270512322441233 := by
  unfold tailWord_2358441
  simp only [CollatzResearch.WordTrace]
  refine ⟨86019410048778521500187177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57346273365852347666791451 86019410048778521500187177)
  ·
    refine ⟨64514557536583891125140383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86019410048778521500187177 64514557536583891125140383)
    ·
      refine ⟨96771836304875836687710575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64514557536583891125140383 96771836304875836687710575)
      ·
        refine ⟨145157754457313755031565863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96771836304875836687710575 145157754457313755031565863)
        ·
          refine ⟨217736631685970632547348795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145157754457313755031565863 217736631685970632547348795)
          ·
            refine ⟨326604947528955948821023193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217736631685970632547348795 326604947528955948821023193)
            ·
              refine ⟨244953710646716961615767395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326604947528955948821023193 244953710646716961615767395)
              ·
                refine ⟨367430565970075442423651093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244953710646716961615767395 367430565970075442423651093)
                ·
                  refine ⟨17223307779847286363608645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 367430565970075442423651093 17223307779847286363608645)
                  ·
                    refine ⟨3229370208721366193176621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17223307779847286363608645 3229370208721366193176621)
                    ·
                      refine ⟨1211013828270512322441233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3229370208721366193176621 1211013828270512322441233)
                      ·
                        rfl

theorem cell23_2358441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_2358441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358441 prefixEnd_2358441 := by exact prefixLift 2358441
  have htrace : WordTrace (prefixWord ++ tailWord_2358441) baseStart_2358441 baseEnd_2358441 := by
    simpa [prefixWord, tailWord_2358441, baseEnd_2358441] using wordTrace_append hprefix tailTrace_2358441
  have hstable : (prefixWord ++ tailWord_2358441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358441).length < 2 ^ (prefixWord ++ tailWord_2358441).sum := by decide
  have hdescent : baseEnd_2358441 < baseStart_2358441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358451 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4]
def baseStart_2358451 : Nat := 118140960795 + 2358451 * 2 ^ 59
def prefixEnd_2358451 : Nat := 4983230072969 + 3 ^ 40 * 2358451 * 2
def baseEnd_2358451 : Nat := 1211018963077057283316187

theorem tailTrace_2358451 : CollatzResearch.WordTrace tailWord_2358451 prefixEnd_2358451 1211018963077057283316187 := by
  unfold tailWord_2358451
  simp only [CollatzResearch.WordTrace]
  refine ⟨86019774778742293208051207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57346516519161528805367471 86019774778742293208051207)
  ·
    refine ⟨129029662168113439812076811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86019774778742293208051207 129029662168113439812076811)
    ·
      refine ⟨193544493252170159718115217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129029662168113439812076811 193544493252170159718115217)
      ·
        refine ⟨145158369939127619788586413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193544493252170159718115217 145158369939127619788586413)
        ·
          refine ⟨54434388727172857420719905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145158369939127619788586413 54434388727172857420719905)
          ·
            refine ⟨40825791545379643065539929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54434388727172857420719905 40825791545379643065539929)
            ·
              refine ⟨30619343659034732299154947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40825791545379643065539929 30619343659034732299154947)
              ·
                refine ⟨45929015488552098448732421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30619343659034732299154947 45929015488552098448732421)
                ·
                  refine ⟨8611690404103518459137329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45929015488552098448732421 8611690404103518459137329)
                  ·
                    refine ⟨6458767803077638844352997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8611690404103518459137329 6458767803077638844352997)
                    ·
                      refine ⟨1211018963077057283316187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6458767803077638844352997 1211018963077057283316187)
                      ·
                        rfl

theorem cell23_2358451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_2358451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358451 prefixEnd_2358451 := by exact prefixLift 2358451
  have htrace : WordTrace (prefixWord ++ tailWord_2358451) baseStart_2358451 baseEnd_2358451 := by
    simpa [prefixWord, tailWord_2358451, baseEnd_2358451] using wordTrace_append hprefix tailTrace_2358451
  have hstable : (prefixWord ++ tailWord_2358451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358451).length < 2 ^ (prefixWord ++ tailWord_2358451).sum := by decide
  have hdescent : baseEnd_2358451 < baseStart_2358451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358455 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 4, 2, 2]
def baseStart_2358455 : Nat := 118140960795 + 2358455 * 2 ^ 59
def prefixEnd_2358455 : Nat := 4983230072969 + 3 ^ 40 * 2358455 * 2
def baseEnd_2358455 : Nat := 1211021016999675267666169

theorem tailTrace_2358455 : CollatzResearch.WordTrace tailWord_2358455 prefixEnd_2358455 1211021016999675267666169 := by
  unfold tailWord_2358455
  simp only [CollatzResearch.WordTrace]
  refine ⟨86019920670727801891196819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57346613780485201260797879 86019920670727801891196819)
  ·
    refine ⟨129029881006091702836795229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86019920670727801891196819 129029881006091702836795229)
    ·
      refine ⟨48386205377284388563798211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129029881006091702836795229 48386205377284388563798211)
      ·
        refine ⟨72579308065926582845697317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48386205377284388563798211 72579308065926582845697317)
        ·
          refine ⟨13608620262361234283568247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72579308065926582845697317 13608620262361234283568247)
          ·
            refine ⟨20412930393541851425352371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608620262361234283568247 20412930393541851425352371)
            ·
              refine ⟨30619395590312777138028557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20412930393541851425352371 30619395590312777138028557)
              ·
                refine ⟨11482273346367291426760709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30619395590312777138028557 11482273346367291426760709)
                ·
                  refine ⟨2152926252443867142517633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11482273346367291426760709 2152926252443867142517633)
                  ·
                    refine ⟨1614694689332900356888225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2152926252443867142517633 1614694689332900356888225)
                    ·
                      refine ⟨1211021016999675267666169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614694689332900356888225 1211021016999675267666169)
                      ·
                        rfl

theorem cell23_2358455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_2358455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358455 prefixEnd_2358455 := by exact prefixLift 2358455
  have htrace : WordTrace (prefixWord ++ tailWord_2358455) baseStart_2358455 baseEnd_2358455 := by
    simpa [prefixWord, tailWord_2358455, baseEnd_2358455] using wordTrace_append hprefix tailTrace_2358455
  have hstable : (prefixWord ++ tailWord_2358455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358455).length < 2 ^ (prefixWord ++ tailWord_2358455).sum := by decide
  have hdescent : baseEnd_2358455 < baseStart_2358455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358466 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2358466 : Nat := 118140960795 + 2358466 * 2 ^ 59
def prefixEnd_2358466 : Nat := 4983230072969 + 3 ^ 40 * 2358466 * 2
def baseEnd_2358466 : Nat := 1211026665286874724628619

theorem tailTrace_2358466 : CollatzResearch.WordTrace tailWord_2358466 prefixEnd_2358466 1211026665286874724628619 := by
  unfold tailWord_2358466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21505080468421987692461813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57346881249125300513231501 21505080468421987692461813)
  ·
    refine ⟨2016101293914561346168295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21505080468421987692461813 2016101293914561346168295)
    ·
      refine ⟨3024151940871842019252443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016101293914561346168295 3024151940871842019252443)
      ·
        refine ⟨4536227911307763028878665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024151940871842019252443 4536227911307763028878665)
        ·
          refine ⟨3402170933480822271658999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4536227911307763028878665 3402170933480822271658999)
          ·
            refine ⟨5103256400221233407488499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3402170933480822271658999 5103256400221233407488499)
            ·
              refine ⟨7654884600331850111232749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103256400221233407488499 7654884600331850111232749)
              ·
                refine ⟨2870581725124443791712281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7654884600331850111232749 2870581725124443791712281)
                ·
                  refine ⟨2152936293843332843784211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870581725124443791712281 2152936293843332843784211)
                  ·
                    refine ⟨3229404440764999265676317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152936293843332843784211 3229404440764999265676317)
                    ·
                      refine ⟨1211026665286874724628619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3229404440764999265676317 1211026665286874724628619)
                      ·
                        rfl

theorem cell23_2358466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2358466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358466 prefixEnd_2358466 := by exact prefixLift 2358466
  have htrace : WordTrace (prefixWord ++ tailWord_2358466) baseStart_2358466 baseEnd_2358466 := by
    simpa [prefixWord, tailWord_2358466, baseEnd_2358466] using wordTrace_append hprefix tailTrace_2358466
  have hstable : (prefixWord ++ tailWord_2358466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358466).length < 2 ^ (prefixWord ++ tailWord_2358466).sum := by decide
  have hdescent : baseEnd_2358466 < baseStart_2358466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358508 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_2358508 : Nat := 118140960795 + 2358508 * 2 ^ 59
def prefixEnd_2358508 : Nat := 4983230072969 + 3 ^ 40 * 2358508 * 2
def baseEnd_2358508 : Nat := 403682743824787853434475

theorem tailTrace_2358508 : CollatzResearch.WordTrace tailWord_2358508 prefixEnd_2358508 403682743824787853434475 := by
  unfold tailWord_2358508
  simp only [CollatzResearch.WordTrace]
  refine ⟨43010926869767895971438089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57347902493023861295250785 43010926869767895971438089)
  ·
    refine ⟨32258195152325921978578567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43010926869767895971438089 32258195152325921978578567)
    ·
      refine ⟨48387292728488882967867851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32258195152325921978578567 48387292728488882967867851)
      ·
        refine ⟨72580939092733324451801777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48387292728488882967867851 72580939092733324451801777)
        ·
          refine ⟨54435704319549993338851333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72580939092733324451801777 54435704319549993338851333)
          ·
            refine ⟨10206694559915623751034625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54435704319549993338851333 10206694559915623751034625)
            ·
              refine ⟨7655020919936717813275969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10206694559915623751034625 7655020919936717813275969)
              ·
                refine ⟨5741265689952538359956977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7655020919936717813275969 5741265689952538359956977)
                ·
                  refine ⟨4305949267464403769967733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5741265689952538359956977 4305949267464403769967733)
                  ·
                    refine ⟨403682743824787853434475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4305949267464403769967733 403682743824787853434475)
                    ·
                      rfl

theorem cell23_2358508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_2358508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358508 prefixEnd_2358508 := by exact prefixLift 2358508
  have htrace : WordTrace (prefixWord ++ tailWord_2358508) baseStart_2358508 baseEnd_2358508 := by
    simpa [prefixWord, tailWord_2358508, baseEnd_2358508] using wordTrace_append hprefix tailTrace_2358508
  have hstable : (prefixWord ++ tailWord_2358508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358508).length < 2 ^ (prefixWord ++ tailWord_2358508).sum := by decide
  have hdescent : baseEnd_2358508 < baseStart_2358508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358615 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 1, 5]
def baseStart_2358615 : Nat := 118140960795 + 2358615 * 2 ^ 59
def prefixEnd_2358615 : Nat := 4983230072969 + 3 ^ 40 * 2358615 * 2
def baseEnd_2358615 : Nat := 403701057968131547221811

theorem tailTrace_2358615 : CollatzResearch.WordTrace tailWord_2358615 prefixEnd_2358615 403701057968131547221811 := by
  unfold tailWord_2358615
  simp only [CollatzResearch.WordTrace]
  refine ⟨86025756350148149217021299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57350504233432099478014199 86025756350148149217021299)
  ·
    refine ⟨129038634525222223825531949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86025756350148149217021299 129038634525222223825531949)
    ·
      refine ⟨48389487946958333934574481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129038634525222223825531949 48389487946958333934574481)
      ·
        refine ⟨36292115960218750450930861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48389487946958333934574481 36292115960218750450930861)
        ·
          refine ⟨13609543485082031419099073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36292115960218750450930861 13609543485082031419099073)
          ·
            refine ⟨10207157613811523564324305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13609543485082031419099073 10207157613811523564324305)
            ·
              refine ⟨7655368210358642673243229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10207157613811523564324305 7655368210358642673243229)
              ·
                refine ⟨2870763078884491002466211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7655368210358642673243229 2870763078884491002466211)
                ·
                  refine ⟨4306144618326736503699317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870763078884491002466211 4306144618326736503699317)
                  ·
                    refine ⟨403701057968131547221811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4306144618326736503699317 403701057968131547221811)
                    ·
                      rfl

theorem cell23_2358615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_2358615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358615 prefixEnd_2358615 := by exact prefixLift 2358615
  have htrace : WordTrace (prefixWord ++ tailWord_2358615) baseStart_2358615 baseEnd_2358615 := by
    simpa [prefixWord, tailWord_2358615, baseEnd_2358615] using wordTrace_append hprefix tailTrace_2358615
  have hstable : (prefixWord ++ tailWord_2358615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358615).length < 2 ^ (prefixWord ++ tailWord_2358615).sum := by decide
  have hdescent : baseEnd_2358615 < baseStart_2358615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358648 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2358648 : Nat := 118140960795 + 2358648 * 2 ^ 59
def prefixEnd_2358648 : Nat := 4983230072969 + 3 ^ 40 * 2358648 * 2
def baseEnd_2358648 : Nat := 1211120118765993012552781

theorem tailTrace_2358648 : CollatzResearch.WordTrace tailWord_2358648 prefixEnd_2358648 1211120118765993012552781 := by
  unfold tailWord_2358648
  simp only [CollatzResearch.WordTrace]
  refine ⟨43013479979514297926486299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57351306639352397235315065 43013479979514297926486299)
  ·
    refine ⟨64520219969271446889729449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43013479979514297926486299 64520219969271446889729449)
    ·
      refine ⟨48390164976953585167297087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64520219969271446889729449 48390164976953585167297087)
      ·
        refine ⟨72585247465430377750945631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48390164976953585167297087 72585247465430377750945631)
        ·
          refine ⟨108877871198145566626418447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72585247465430377750945631 108877871198145566626418447)
          ·
            refine ⟨163316806797218349939627671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108877871198145566626418447 163316806797218349939627671)
            ·
              refine ⟨244975210195827524909441507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163316806797218349939627671 244975210195827524909441507)
              ·
                refine ⟨367462815293741287364162261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244975210195827524909441507 367462815293741287364162261)
                ·
                  refine ⟨8612409733447061422597553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 367462815293741287364162261 8612409733447061422597553)
                  ·
                    refine ⟨6459307300085296066948165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8612409733447061422597553 6459307300085296066948165)
                    ·
                      refine ⟨1211120118765993012552781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6459307300085296066948165 1211120118765993012552781)
                      ·
                        rfl

theorem cell23_2358648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2358648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358648 prefixEnd_2358648 := by exact prefixLift 2358648
  have htrace : WordTrace (prefixWord ++ tailWord_2358648) baseStart_2358648 baseEnd_2358648 := by
    simpa [prefixWord, tailWord_2358648, baseEnd_2358648] using wordTrace_append hprefix tailTrace_2358648
  have hstable : (prefixWord ++ tailWord_2358648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358648).length < 2 ^ (prefixWord ++ tailWord_2358648).sum := by decide
  have hdescent : baseEnd_2358648 < baseStart_2358648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358652 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_2358652 : Nat := 118140960795 + 2358652 * 2 ^ 59
def prefixEnd_2358652 : Nat := 4983230072969 + 3 ^ 40 * 2358652 * 2
def baseEnd_2358652 : Nat := 1211122172688610996902763

theorem tailTrace_2358652 : CollatzResearch.WordTrace tailWord_2358652 prefixEnd_2358652 1211122172688610996902763 := by
  unfold tailWord_2358652
  simp only [CollatzResearch.WordTrace]
  refine ⟨43013552925507052268059105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57351403900676069690745473 43013552925507052268059105)
  ·
    refine ⟨32260164694130289201044329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43013552925507052268059105 32260164694130289201044329)
    ·
      refine ⟨24195123520597716900783247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32260164694130289201044329 24195123520597716900783247)
      ·
        refine ⟨36292685280896575351174871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24195123520597716900783247 36292685280896575351174871)
        ·
          refine ⟨54439027921344863026762307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36292685280896575351174871 54439027921344863026762307)
          ·
            refine ⟨81658541882017294540143461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54439027921344863026762307 81658541882017294540143461)
            ·
              refine ⟨15310976602878242726276899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81658541882017294540143461 15310976602878242726276899)
              ·
                refine ⟨22966464904317364089415349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15310976602878242726276899 22966464904317364089415349)
                ·
                  refine ⟨2153106084779752883382689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22966464904317364089415349 2153106084779752883382689)
                  ·
                    refine ⟨1614829563584814662537017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2153106084779752883382689 1614829563584814662537017)
                    ·
                      refine ⟨1211122172688610996902763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614829563584814662537017 1211122172688610996902763)
                      ·
                        rfl

theorem cell23_2358652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_2358652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358652 prefixEnd_2358652 := by exact prefixLift 2358652
  have htrace : WordTrace (prefixWord ++ tailWord_2358652) baseStart_2358652 baseEnd_2358652 := by
    simpa [prefixWord, tailWord_2358652, baseEnd_2358652] using wordTrace_append hprefix tailTrace_2358652
  have hstable : (prefixWord ++ tailWord_2358652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358652).length < 2 ^ (prefixWord ++ tailWord_2358652).sum := by decide
  have hdescent : baseEnd_2358652 < baseStart_2358652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358680 : List Nat := [2, 1, 2, 5, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2358680 : Nat := 118140960795 + 2358680 * 2 ^ 59
def prefixEnd_2358680 : Nat := 4983230072969 + 3 ^ 40 * 2358680 * 2
def baseEnd_2358680 : Nat := 1211136550146936887352635

theorem tailTrace_2358680 : CollatzResearch.WordTrace tailWord_2358680 prefixEnd_2358680 1211136550146936887352635 := by
  unfold tailWord_2358680
  simp only [CollatzResearch.WordTrace]
  refine ⟨43014063547456332659068747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57352084729941776878758329 43014063547456332659068747)
  ·
    refine ⟨64521095321184498988603121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43014063547456332659068747 64521095321184498988603121)
    ·
      refine ⟨48390821490888374241452341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64521095321184498988603121 48390821490888374241452341)
      ·
        refine ⟨4536639514770785085136157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48390821490888374241452341 4536639514770785085136157)
        ·
          refine ⟨1701239818039044406926059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4536639514770785085136157 1701239818039044406926059)
          ·
            refine ⟨2551859727058566610389089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701239818039044406926059 2551859727058566610389089)
            ·
              refine ⟨1913894795293924957791817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2551859727058566610389089 1913894795293924957791817)
              ·
                refine ⟨1435421096470443718343863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913894795293924957791817 1435421096470443718343863)
                ·
                  refine ⟨2153131644705665577515795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435421096470443718343863 2153131644705665577515795)
                  ·
                    refine ⟨3229697467058498366273693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2153131644705665577515795 3229697467058498366273693)
                    ·
                      refine ⟨1211136550146936887352635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3229697467058498366273693 1211136550146936887352635)
                      ·
                        rfl

theorem cell23_2358680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2358680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358680 prefixEnd_2358680 := by exact prefixLift 2358680
  have htrace : WordTrace (prefixWord ++ tailWord_2358680) baseStart_2358680 baseEnd_2358680 := by
    simpa [prefixWord, tailWord_2358680, baseEnd_2358680] using wordTrace_append hprefix tailTrace_2358680
  have hstable : (prefixWord ++ tailWord_2358680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358680).length < 2 ^ (prefixWord ++ tailWord_2358680).sum := by decide
  have hdescent : baseEnd_2358680 < baseStart_2358680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358688 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 9]
def baseStart_2358688 : Nat := 118140960795 + 2358688 * 2 ^ 59
def prefixEnd_2358688 : Nat := 4983230072969 + 3 ^ 40 * 2358688 * 2
def baseEnd_2358688 : Nat := 403713552664057618684199

theorem tailTrace_2358688 : CollatzResearch.WordTrace tailWord_2358688 prefixEnd_2358688 403713552664057618684199 := by
  unfold tailWord_2358688
  simp only [CollatzResearch.WordTrace]
  refine ⟨43014209439441841342214359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57352279252589121789619145 43014209439441841342214359)
  ·
    refine ⟨64521314159162762013321539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43014209439441841342214359 64521314159162762013321539)
    ·
      refine ⟨96781971238744143019982309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64521314159162762013321539 96781971238744143019982309)
      ·
        refine ⟨18146619607264526816246683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96781971238744143019982309 18146619607264526816246683)
        ·
          refine ⟨27219929410896790224370025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18146619607264526816246683 27219929410896790224370025)
          ·
            refine ⟨20414947058172592668277519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27219929410896790224370025 20414947058172592668277519)
            ·
              refine ⟨30622420587258889002416279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20414947058172592668277519 30622420587258889002416279)
              ·
                refine ⟨45933630880888333503624419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30622420587258889002416279 45933630880888333503624419)
                ·
                  refine ⟨68900446321332500255436629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45933630880888333503624419 68900446321332500255436629)
                  ·
                    refine ⟨403713552664057618684199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 68900446321332500255436629 403713552664057618684199)
                    ·
                      rfl

theorem cell23_2358688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_2358688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358688 prefixEnd_2358688 := by exact prefixLift 2358688
  have htrace : WordTrace (prefixWord ++ tailWord_2358688) baseStart_2358688 baseEnd_2358688 := by
    simpa [prefixWord, tailWord_2358688, baseEnd_2358688] using wordTrace_append hprefix tailTrace_2358688
  have hstable : (prefixWord ++ tailWord_2358688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358688).length < 2 ^ (prefixWord ++ tailWord_2358688).sum := by decide
  have hdescent : baseEnd_2358688 < baseStart_2358688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358712 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 3, 3, 2]
def baseStart_2358712 : Nat := 118140960795 + 2358712 * 2 ^ 59
def prefixEnd_2358712 : Nat := 4983230072969 + 3 ^ 40 * 2358712 * 2
def baseEnd_2358712 : Nat := 1211152981527880762152487

theorem tailTrace_2358712 : CollatzResearch.WordTrace tailWord_2358712 prefixEnd_2358712 1211152981527880762152487 := by
  unfold tailWord_2358712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43014647115398367391651195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57352862820531156522201593 43014647115398367391651195)
  ·
    refine ⟨64521970673097551087476793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43014647115398367391651195 64521970673097551087476793)
    ·
      refine ⟨48391478004823163315607595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64521970673097551087476793 48391478004823163315607595)
      ·
        refine ⟨72587217007234744973411393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48391478004823163315607595 72587217007234744973411393)
        ·
          refine ⟨54440412755426058730058545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72587217007234744973411393 54440412755426058730058545)
          ·
            refine ⟨40830309566569544047543909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54440412755426058730058545 40830309566569544047543909)
            ·
              refine ⟨7655683043731789508914483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40830309566569544047543909 7655683043731789508914483)
              ·
                refine ⟨11483524565597684263371725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7655683043731789508914483 11483524565597684263371725)
                ·
                  refine ⟨4306321712099131598764397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11483524565597684263371725 4306321712099131598764397)
                  ·
                    refine ⟨1614870642037174349536649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4306321712099131598764397 1614870642037174349536649)
                    ·
                      refine ⟨1211152981527880762152487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614870642037174349536649 1211152981527880762152487)
                      ·
                        rfl

theorem cell23_2358712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_2358712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358712 prefixEnd_2358712 := by exact prefixLift 2358712
  have htrace : WordTrace (prefixWord ++ tailWord_2358712) baseStart_2358712 baseEnd_2358712 := by
    simpa [prefixWord, tailWord_2358712, baseEnd_2358712] using wordTrace_append hprefix tailTrace_2358712
  have hstable : (prefixWord ++ tailWord_2358712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358712).length < 2 ^ (prefixWord ++ tailWord_2358712).sum := by decide
  have hdescent : baseEnd_2358712 < baseStart_2358712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358759 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2358759 : Nat := 118140960795 + 2358759 * 2 ^ 59
def prefixEnd_2358759 : Nat := 4983230072969 + 3 ^ 40 * 2358759 * 2
def baseEnd_2358759 : Nat := 1211177115118642078264771

theorem tailTrace_2358759 : CollatzResearch.WordTrace tailWord_2358759 prefixEnd_2358759 1211177115118642078264771 := by
  unfold tailWord_2358759
  simp only [CollatzResearch.WordTrace]
  refine ⟨86031008461626461810263331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57354005641084307873508887 86031008461626461810263331)
  ·
    refine ⟨129046512692439692715394997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86031008461626461810263331 129046512692439692715394997)
    ·
      refine ⟨12098110564916221192068281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129046512692439692715394997 12098110564916221192068281)
      ·
        refine ⟨9073582923687165894051211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12098110564916221192068281 9073582923687165894051211)
        ·
          refine ⟨13610374385530748841076817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073582923687165894051211 13610374385530748841076817)
          ·
            refine ⟨10207780789148061630807613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13610374385530748841076817 10207780789148061630807613)
            ·
              refine ⟨3827917795930523111552855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10207780789148061630807613 3827917795930523111552855)
              ·
                refine ⟨5741876693895784667329283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3827917795930523111552855 5741876693895784667329283)
                ·
                  refine ⟨8612815040843677000993925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5741876693895784667329283 8612815040843677000993925)
                  ·
                    refine ⟨1614902820158189437686361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8612815040843677000993925 1614902820158189437686361)
                    ·
                      refine ⟨1211177115118642078264771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614902820158189437686361 1211177115118642078264771)
                      ·
                        rfl

theorem cell23_2358759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2358759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358759 prefixEnd_2358759 := by exact prefixLift 2358759
  have htrace : WordTrace (prefixWord ++ tailWord_2358759) baseStart_2358759 baseEnd_2358759 := by
    simpa [prefixWord, tailWord_2358759, baseEnd_2358759] using wordTrace_append hprefix tailTrace_2358759
  have hstable : (prefixWord ++ tailWord_2358759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358759).length < 2 ^ (prefixWord ++ tailWord_2358759).sum := by decide
  have hdescent : baseEnd_2358759 < baseStart_2358759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358775 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_2358775 : Nat := 118140960795 + 2358775 * 2 ^ 59
def prefixEnd_2358775 : Nat := 4983230072969 + 3 ^ 40 * 2358775 * 2
def baseEnd_2358775 : Nat := 1211185330809114015664697

theorem tailTrace_2358775 : CollatzResearch.WordTrace tailWord_2358775 prefixEnd_2358775 1211185330809114015664697 := by
  unfold tailWord_2358775
  simp only [CollatzResearch.WordTrace]
  refine ⟨86031592029568496542845779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57354394686378997695230519 86031592029568496542845779)
  ·
    refine ⟨129047388044352744814268669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86031592029568496542845779 129047388044352744814268669)
    ·
      refine ⟨48392770516632279305350751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129047388044352744814268669 48392770516632279305350751)
      ·
        refine ⟨72589155774948418958026127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48392770516632279305350751 72589155774948418958026127)
        ·
          refine ⟨108883733662422628437039191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72589155774948418958026127 108883733662422628437039191)
          ·
            refine ⟨163325600493633942655558787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108883733662422628437039191 163325600493633942655558787)
            ·
              refine ⟨244988400740450913983338181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163325600493633942655558787 244988400740450913983338181)
              ·
                refine ⟨45935325138834546371875909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244988400740450913983338181 45935325138834546371875909)
                ·
                  refine ⟨8612873463531477444726733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45935325138834546371875909 8612873463531477444726733)
                  ·
                    refine ⟨3229827548824304041772525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8612873463531477444726733 3229827548824304041772525)
                    ·
                      refine ⟨1211185330809114015664697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3229827548824304041772525 1211185330809114015664697)
                      ·
                        rfl

theorem cell23_2358775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_2358775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358775 prefixEnd_2358775 := by exact prefixLift 2358775
  have htrace : WordTrace (prefixWord ++ tailWord_2358775) baseStart_2358775 baseEnd_2358775 := by
    simpa [prefixWord, tailWord_2358775, baseEnd_2358775] using wordTrace_append hprefix tailTrace_2358775
  have hstable : (prefixWord ++ tailWord_2358775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358775).length < 2 ^ (prefixWord ++ tailWord_2358775).sum := by decide
  have hdescent : baseEnd_2358775 < baseStart_2358775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358805 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_2358805 : Nat := 118140960795 + 2358805 * 2 ^ 59
def prefixEnd_2358805 : Nat := 4983230072969 + 3 ^ 40 * 2358805 * 2
def baseEnd_2358805 : Nat := 1211200735228748898289559

theorem tailTrace_2358805 : CollatzResearch.WordTrace tailWord_2358805 prefixEnd_2358805 1211200735228748898289559 := by
  unfold tailWord_2358805
  simp only [CollatzResearch.WordTrace]
  refine ⟨86032686219459811666437869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57355124146306541110958579 86032686219459811666437869)
  ·
    refine ⟨32262257332297429374914201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86032686219459811666437869 32262257332297429374914201)
    ·
      refine ⟨24196692999223072031185651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32262257332297429374914201 24196692999223072031185651)
      ·
        refine ⟨36295039498834608046778477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24196692999223072031185651 36295039498834608046778477)
        ·
          refine ⟨13610639812062978017541929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36295039498834608046778477 13610639812062978017541929)
          ·
            refine ⟨10207979859047233513156447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13610639812062978017541929 10207979859047233513156447)
            ·
              refine ⟨15311969788570850269734671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10207979859047233513156447 15311969788570850269734671)
              ·
                refine ⟨22967954682856275404602007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15311969788570850269734671 22967954682856275404602007)
                ·
                  refine ⟨34451932024284413106903011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22967954682856275404602007 34451932024284413106903011)
                  ·
                    refine ⟨51677898036426619660354517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34451932024284413106903011 51677898036426619660354517)
                    ·
                      refine ⟨1211200735228748898289559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51677898036426619660354517 1211200735228748898289559)
                      ·
                        rfl

theorem cell23_2358805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_2358805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358805 prefixEnd_2358805 := by exact prefixLift 2358805
  have htrace : WordTrace (prefixWord ++ tailWord_2358805) baseStart_2358805 baseEnd_2358805 := by
    simpa [prefixWord, tailWord_2358805, baseEnd_2358805] using wordTrace_append hprefix tailTrace_2358805
  have hstable : (prefixWord ++ tailWord_2358805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358805).length < 2 ^ (prefixWord ++ tailWord_2358805).sum := by decide
  have hdescent : baseEnd_2358805 < baseStart_2358805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358814 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2358814 : Nat := 118140960795 + 2358814 * 2 ^ 59
def prefixEnd_2358814 : Nat := 4983230072969 + 3 ^ 40 * 2358814 * 2
def baseEnd_2358814 : Nat := 1211205356554639363077019

theorem tailTrace_2358814 : CollatzResearch.WordTrace tailWord_2358814 prefixEnd_2358814 1211205356554639363077019 := by
  unfold tailWord_2358814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10754126809553400775439437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57355342984284804135676997 10754126809553400775439437)
  ·
    refine ⟨4032797553582525290789789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10754126809553400775439437 4032797553582525290789789)
    ·
      refine ⟨1512299082593446984046171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4032797553582525290789789 1512299082593446984046171)
      ·
        refine ⟨2268448623890170476069257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512299082593446984046171 2268448623890170476069257)
        ·
          refine ⟨1701336467917627857051943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268448623890170476069257 1701336467917627857051943)
          ·
            refine ⟨2552004701876441785577915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701336467917627857051943 2552004701876441785577915)
            ·
              refine ⟨3828007052814662678366873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552004701876441785577915 3828007052814662678366873)
              ·
                refine ⟨2871005289610997008775155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828007052814662678366873 2871005289610997008775155)
                ·
                  refine ⟨4306507934416495513162733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871005289610997008775155 4306507934416495513162733)
                  ·
                    refine ⟨1614940475406185817436025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4306507934416495513162733 1614940475406185817436025)
                    ·
                      refine ⟨1211205356554639363077019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614940475406185817436025 1211205356554639363077019)
                      ·
                        rfl

theorem cell23_2358814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2358814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358814 prefixEnd_2358814 := by exact prefixLift 2358814
  have htrace : WordTrace (prefixWord ++ tailWord_2358814) baseStart_2358814 baseEnd_2358814 := by
    simpa [prefixWord, tailWord_2358814, baseEnd_2358814] using wordTrace_append hprefix tailTrace_2358814
  have hstable : (prefixWord ++ tailWord_2358814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358814).length < 2 ^ (prefixWord ++ tailWord_2358814).sum := by decide
  have hdescent : baseEnd_2358814 < baseStart_2358814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358815 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2358815 : Nat := 118140960795 + 2358815 * 2 ^ 59
def prefixEnd_2358815 : Nat := 4983230072969 + 3 ^ 40 * 2358815 * 2
def baseEnd_2358815 : Nat := 1211205870035293859164513

theorem tailTrace_2358815 : CollatzResearch.WordTrace tailWord_2358815 prefixEnd_2358815 1211205870035293859164513 := by
  unfold tailWord_2358815
  simp only [CollatzResearch.WordTrace]
  refine ⟨86033050949423583374301899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57355367299615722249534599 86033050949423583374301899)
  ·
    refine ⟨129049576424135375061452849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86033050949423583374301899 129049576424135375061452849)
    ·
      refine ⟨96787182318101531296089637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129049576424135375061452849 96787182318101531296089637)
      ·
        refine ⟨18147596684644037118016807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96787182318101531296089637 18147596684644037118016807)
        ·
          refine ⟨27221395026966055677025211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18147596684644037118016807 27221395026966055677025211)
          ·
            refine ⟨40832092540449083515537817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27221395026966055677025211 40832092540449083515537817)
            ·
              refine ⟨30624069405336812636653363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40832092540449083515537817 30624069405336812636653363)
              ·
                refine ⟨45936104108005218954980045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30624069405336812636653363 45936104108005218954980045)
                ·
                  refine ⟨17226039040501957108117517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45936104108005218954980045 17226039040501957108117517)
                  ·
                    refine ⟨6459764640188233915544069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17226039040501957108117517 6459764640188233915544069)
                    ·
                      refine ⟨1211205870035293859164513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6459764640188233915544069 1211205870035293859164513)
                      ·
                        rfl

theorem cell23_2358815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2358815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358815 prefixEnd_2358815 := by exact prefixLift 2358815
  have htrace : WordTrace (prefixWord ++ tailWord_2358815) baseStart_2358815 baseEnd_2358815 := by
    simpa [prefixWord, tailWord_2358815, baseEnd_2358815] using wordTrace_append hprefix tailTrace_2358815
  have hstable : (prefixWord ++ tailWord_2358815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358815).length < 2 ^ (prefixWord ++ tailWord_2358815).sum := by decide
  have hdescent : baseEnd_2358815 < baseStart_2358815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358832 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 4, 4, 2]
def baseStart_2358832 : Nat := 118140960795 + 2358832 * 2 ^ 59
def prefixEnd_2358832 : Nat := 4983230072969 + 3 ^ 40 * 2358832 * 2
def baseEnd_2358832 : Nat := 1211214599206420292651935

theorem tailTrace_2358832 : CollatzResearch.WordTrace tailWord_2358832 prefixEnd_2358832 1211214599206420292651935 := by
  unfold tailWord_2358832
  simp only [CollatzResearch.WordTrace]
  refine ⟨43016835495180997638835375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57355780660241330185113833 43016835495180997638835375)
  ·
    refine ⟨64525253242771496458253063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43016835495180997638835375 64525253242771496458253063)
    ·
      refine ⟨96787879864157244687379595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64525253242771496458253063 96787879864157244687379595)
      ·
        refine ⟨145181819796235867031069393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96787879864157244687379595 145181819796235867031069393)
        ·
          refine ⟨108886364847176900273302045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145181819796235867031069393 108886364847176900273302045)
          ·
            refine ⟨40832386817691337602488267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108886364847176900273302045 40832386817691337602488267)
            ·
              refine ⟨61248580226537006403732401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40832386817691337602488267 61248580226537006403732401)
              ·
                refine ⟨45936435169902754802799301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61248580226537006403732401 45936435169902754802799301)
                ·
                  refine ⟨8613081594356766525524869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45936435169902754802799301 8613081594356766525524869)
                  ·
                    refine ⟨1614952798941893723535913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8613081594356766525524869 1614952798941893723535913)
                    ·
                      refine ⟨1211214599206420292651935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614952798941893723535913 1211214599206420292651935)
                      ·
                        rfl

theorem cell23_2358832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 4, 2].length) (baseStart_2358832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358832 prefixEnd_2358832 := by exact prefixLift 2358832
  have htrace : WordTrace (prefixWord ++ tailWord_2358832) baseStart_2358832 baseEnd_2358832 := by
    simpa [prefixWord, tailWord_2358832, baseEnd_2358832] using wordTrace_append hprefix tailTrace_2358832
  have hstable : (prefixWord ++ tailWord_2358832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358832).length < 2 ^ (prefixWord ++ tailWord_2358832).sum := by decide
  have hdescent : baseEnd_2358832 < baseStart_2358832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358849 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2358849 : Nat := 118140960795 + 2358849 * 2 ^ 59
def prefixEnd_2358849 : Nat := 4983230072969 + 3 ^ 40 * 2358849 * 2
def baseEnd_2358849 : Nat := 1211223328377546726139357

theorem tailTrace_2358849 : CollatzResearch.WordTrace tailWord_2358849 prefixEnd_2358849 1211223328377546726139357 := by
  unfold tailWord_2358849
  simp only [CollatzResearch.WordTrace]
  refine ⟨86034291031300407181039601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57356194020866938120693067 86034291031300407181039601)
  ·
    refine ⟨64525718273475305385779701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86034291031300407181039601 64525718273475305385779701)
    ·
      refine ⟨6049286088138309879916847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64525718273475305385779701 6049286088138309879916847)
      ·
        refine ⟨9073929132207464819875271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049286088138309879916847 9073929132207464819875271)
        ·
          refine ⟨13610893698311197229812907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073929132207464819875271 13610893698311197229812907)
          ·
            refine ⟨20416340547466795844719361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13610893698311197229812907 20416340547466795844719361)
            ·
              refine ⟨15312255410600096883539521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20416340547466795844719361 15312255410600096883539521)
              ·
                refine ⟨11484191557950072662654641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15312255410600096883539521 11484191557950072662654641)
                ·
                  refine ⟨8613143668462554496990981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11484191557950072662654641 8613143668462554496990981)
                  ·
                    refine ⟨1614964437836728968185809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8613143668462554496990981 1614964437836728968185809)
                    ·
                      refine ⟨1211223328377546726139357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1614964437836728968185809 1211223328377546726139357)
                      ·
                        rfl

theorem cell23_2358849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2358849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358849 prefixEnd_2358849 := by exact prefixLift 2358849
  have htrace : WordTrace (prefixWord ++ tailWord_2358849) baseStart_2358849 baseEnd_2358849 := by
    simpa [prefixWord, tailWord_2358849, baseEnd_2358849] using wordTrace_append hprefix tailTrace_2358849
  have hstable : (prefixWord ++ tailWord_2358849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358849).length < 2 ^ (prefixWord ++ tailWord_2358849).sum := by decide
  have hdescent : baseEnd_2358849 < baseStart_2358849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358893 : List Nat := [1, 5, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_2358893 : Nat := 118140960795 + 2358893 * 2 ^ 59
def prefixEnd_2358893 : Nat := 4983230072969 + 3 ^ 40 * 2358893 * 2
def baseEnd_2358893 : Nat := 403748640508781517996385

theorem tailTrace_2358893 : CollatzResearch.WordTrace tailWord_2358893 prefixEnd_2358893 403748640508781517996385 := by
  unfold tailWord_2358893
  simp only [CollatzResearch.WordTrace]
  refine ⟨86035895843141002695641333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57357263895427335130427555 86035895843141002695641333)
  ·
    refine ⟨8065865235294469002716375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86035895843141002695641333 8065865235294469002716375)
    ·
      refine ⟨12098797852941703504074563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8065865235294469002716375 12098797852941703504074563)
      ·
        refine ⟨18148196779412555256111845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12098797852941703504074563 18148196779412555256111845)
        ·
          refine ⟨3402786896139854110520971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18148196779412555256111845 3402786896139854110520971)
          ·
            refine ⟨5104180344209781165781457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3402786896139854110520971 5104180344209781165781457)
            ·
              refine ⟨3828135258157335874336093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5104180344209781165781457 3828135258157335874336093)
              ·
                refine ⟨1435550721809000952876035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3828135258157335874336093 1435550721809000952876035)
                ·
                  refine ⟨2153326082713501429314053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435550721809000952876035 2153326082713501429314053)
                  ·
                    refine ⟨403748640508781517996385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153326082713501429314053 403748640508781517996385)
                    ·
                      rfl

theorem cell23_2358893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_2358893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358893 prefixEnd_2358893 := by exact prefixLift 2358893
  have htrace : WordTrace (prefixWord ++ tailWord_2358893) baseStart_2358893 baseEnd_2358893 := by
    simpa [prefixWord, tailWord_2358893, baseEnd_2358893] using wordTrace_append hprefix tailTrace_2358893
  have hstable : (prefixWord ++ tailWord_2358893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358893).length < 2 ^ (prefixWord ++ tailWord_2358893).sum := by decide
  have hdescent : baseEnd_2358893 < baseStart_2358893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358895 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_2358895 : Nat := 118140960795 + 2358895 * 2 ^ 59
def prefixEnd_2358895 : Nat := 4983230072969 + 3 ^ 40 * 2358895 * 2
def baseEnd_2358895 : Nat := 1211246948487653546164145

theorem tailTrace_2358895 : CollatzResearch.WordTrace tailWord_2358895 prefixEnd_2358895 1211246948487653546164145 := by
  unfold tailWord_2358895
  simp only [CollatzResearch.WordTrace]
  refine ⟨86035968789133757037214139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57357312526089171358142759 86035968789133757037214139)
  ·
    refine ⟨129053953183700635555821209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86035968789133757037214139 129053953183700635555821209)
    ·
      refine ⟨96790464887775476666865907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129053953183700635555821209 96790464887775476666865907)
      ·
        refine ⟨145185697331663215000298861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96790464887775476666865907 145185697331663215000298861)
        ·
          refine ⟨54444636499373705625112073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145185697331663215000298861 54444636499373705625112073)
          ·
            refine ⟨40833477374530279218834055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54444636499373705625112073 40833477374530279218834055)
            ·
              refine ⟨61250216061795418828251083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40833477374530279218834055 61250216061795418828251083)
              ·
                refine ⟨91875324092693128242376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61250216061795418828251083 91875324092693128242376625)
                ·
                  refine ⟨68906493069519846181782469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91875324092693128242376625 68906493069519846181782469)
                  ·
                    refine ⟨12919967450534971159084213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68906493069519846181782469 12919967450534971159084213)
                    ·
                      refine ⟨1211246948487653546164145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12919967450534971159084213 1211246948487653546164145)
                      ·
                        rfl

theorem cell23_2358895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_2358895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358895 prefixEnd_2358895 := by exact prefixLift 2358895
  have htrace : WordTrace (prefixWord ++ tailWord_2358895) baseStart_2358895 baseEnd_2358895 := by
    simpa [prefixWord, tailWord_2358895, baseEnd_2358895] using wordTrace_append hprefix tailTrace_2358895
  have hstable : (prefixWord ++ tailWord_2358895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358895).length < 2 ^ (prefixWord ++ tailWord_2358895).sum := by decide
  have hdescent : baseEnd_2358895 < baseStart_2358895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358959 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 3]
def baseStart_2358959 : Nat := 118140960795 + 2358959 * 2 ^ 59
def prefixEnd_2358959 : Nat := 4983230072969 + 3 ^ 40 * 2358959 * 2
def baseEnd_2358959 : Nat := 1211279811249541295763851

theorem tailTrace_2358959 : CollatzResearch.WordTrace tailWord_2358959 prefixEnd_2358959 1211279811249541295763851 := by
  unfold tailWord_2358959
  simp only [CollatzResearch.WordTrace]
  refine ⟨86038303060901895967543931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57358868707267930645029287 86038303060901895967543931)
  ·
    refine ⟨129057454591352843951315897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86038303060901895967543931 129057454591352843951315897)
    ·
      refine ⟨96793090943514632963486923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129057454591352843951315897 96793090943514632963486923)
      ·
        refine ⟨145189636415271949445230385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96793090943514632963486923 145189636415271949445230385)
        ·
          refine ⟨108892227311453962083922789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145189636415271949445230385 108892227311453962083922789)
          ·
            refine ⟨20417292620897617890735523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108892227311453962083922789 20417292620897617890735523)
            ·
              refine ⟨30625938931346426836103285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20417292620897617890735523 30625938931346426836103285)
              ·
                refine ⟨2871181774813727515884683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30625938931346426836103285 2871181774813727515884683)
                ·
                  refine ⟨4306772662220591273827025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871181774813727515884683 4306772662220591273827025)
                  ·
                    refine ⟨3230079496665443455370269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4306772662220591273827025 3230079496665443455370269)
                    ·
                      refine ⟨1211279811249541295763851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3230079496665443455370269 1211279811249541295763851)
                      ·
                        rfl

theorem cell23_2358959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_2358959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2358959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2358959 prefixEnd_2358959 := by exact prefixLift 2358959
  have htrace : WordTrace (prefixWord ++ tailWord_2358959) baseStart_2358959 baseEnd_2358959 := by
    simpa [prefixWord, tailWord_2358959, baseEnd_2358959] using wordTrace_append hprefix tailTrace_2358959
  have hstable : (prefixWord ++ tailWord_2358959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358959).length < 2 ^ (prefixWord ++ tailWord_2358959).sum := by decide
  have hdescent : baseEnd_2358959 < baseStart_2358959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359032 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2359032 : Nat := 118140960795 + 2359032 * 2 ^ 59
def prefixEnd_2359032 : Nat := 4983230072969 + 3 ^ 40 * 2359032 * 2
def baseEnd_2359032 : Nat := 1211317295337319510151015

theorem tailTrace_2359032 : CollatzResearch.WordTrace tailWord_2359032 prefixEnd_2359032 1211317295337319510151015 := by
  unfold tailWord_2359032
  simp only [CollatzResearch.WordTrace]
  refine ⟨43020482794818714717475675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57360643726424952956634233 43020482794818714717475675)
  ·
    refine ⟨64530724192228072076213513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43020482794818714717475675 64530724192228072076213513)
    ·
      refine ⟨48398043144171054057160135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64530724192228072076213513 48398043144171054057160135)
      ·
        refine ⟨72597064716256581085740203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48398043144171054057160135 72597064716256581085740203)
        ·
          refine ⟨108895597074384871628610305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72597064716256581085740203 108895597074384871628610305)
          ·
            refine ⟨81671697805788653721457729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108895597074384871628610305 81671697805788653721457729)
            ·
              refine ⟨61253773354341490291093297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81671697805788653721457729 61253773354341490291093297)
              ·
                refine ⟨45940330015756117718319973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61253773354341490291093297 45940330015756117718319973)
                ·
                  refine ⟨8613811877954272072184995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45940330015756117718319973 8613811877954272072184995)
                  ·
                    refine ⟨12920717816931408108277493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8613811877954272072184995 12920717816931408108277493)
                    ·
                      refine ⟨1211317295337319510151015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12920717816931408108277493 1211317295337319510151015)
                      ·
                        rfl

theorem cell23_2359032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2359032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359032 prefixEnd_2359032 := by exact prefixLift 2359032
  have htrace : WordTrace (prefixWord ++ tailWord_2359032) baseStart_2359032 baseEnd_2359032 := by
    simpa [prefixWord, tailWord_2359032, baseEnd_2359032] using wordTrace_append hprefix tailTrace_2359032
  have hstable : (prefixWord ++ tailWord_2359032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359032).length < 2 ^ (prefixWord ++ tailWord_2359032).sum := by decide
  have hdescent : baseEnd_2359032 < baseStart_2359032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359052 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 9]
def baseStart_2359052 : Nat := 118140960795 + 2359052 * 2 ^ 59
def prefixEnd_2359052 : Nat := 4983230072969 + 3 ^ 40 * 2359052 * 2
def baseEnd_2359052 : Nat := 134591951661156603544547

theorem tailTrace_2359052 : CollatzResearch.WordTrace tailWord_2359052 prefixEnd_2359052 134591951661156603544547 := by
  unfold tailWord_2359052
  simp only [CollatzResearch.WordTrace]
  refine ⟨43020847524782486425339705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57361130033043315233786273 43020847524782486425339705)
  ·
    refine ⟨32265635643586864819004779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43020847524782486425339705 32265635643586864819004779)
    ·
      refine ⟨48398453465380297228507169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32265635643586864819004779 48398453465380297228507169)
      ·
        refine ⟨36298840099035222921380377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48398453465380297228507169 36298840099035222921380377)
        ·
          refine ⟨27224130074276417191035283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36298840099035222921380377 27224130074276417191035283)
          ·
            refine ⟨40836195111414625786552925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27224130074276417191035283 40836195111414625786552925)
            ·
              refine ⟨15313573166780484669957347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40836195111414625786552925 15313573166780484669957347)
              ·
                refine ⟨22970359750170727004936021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15313573166780484669957347 22970359750170727004936021)
                ·
                  refine ⟨134591951661156603544547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22970359750170727004936021 134591951661156603544547)
                  ·
                    rfl

theorem cell23_2359052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_2359052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359052 prefixEnd_2359052 := by exact prefixLift 2359052
  have htrace : WordTrace (prefixWord ++ tailWord_2359052) baseStart_2359052 baseEnd_2359052 := by
    simpa [prefixWord, tailWord_2359052, baseEnd_2359052] using wordTrace_append hprefix tailTrace_2359052
  have hstable : (prefixWord ++ tailWord_2359052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359052).length < 2 ^ (prefixWord ++ tailWord_2359052).sum := by decide
  have hdescent : baseEnd_2359052 < baseStart_2359052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359080 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_2359080 : Nat := 118140960795 + 2359080 * 2 ^ 59
def prefixEnd_2359080 : Nat := 4983230072969 + 3 ^ 40 * 2359080 * 2
def baseEnd_2359080 : Nat := 1211341942408735322350795

theorem tailTrace_2359080 : CollatzResearch.WordTrace tailWord_2359080 prefixEnd_2359080 1211341942408735322350795 := by
  unfold tailWord_2359080
  simp only [CollatzResearch.WordTrace]
  refine ⟨43021358146731766816349347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57361810862309022421799129 43021358146731766816349347)
  ·
    refine ⟨64532037220097650224524021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43021358146731766816349347 64532037220097650224524021)
    ·
      refine ⟨6049878489384154708549127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64532037220097650224524021 6049878489384154708549127)
      ·
        refine ⟨9074817734076232062823691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049878489384154708549127 9074817734076232062823691)
        ·
          refine ⟨13612226601114348094235537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9074817734076232062823691 13612226601114348094235537)
          ·
            refine ⟨10209169950835761070676653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13612226601114348094235537 10209169950835761070676653)
            ·
              refine ⟨3828438731563410401503745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10209169950835761070676653 3828438731563410401503745)
              ·
                refine ⟨2871329048672557801127809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828438731563410401503745 2871329048672557801127809)
                ·
                  refine ⟨2153496786504418350845857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871329048672557801127809 2153496786504418350845857)
                  ·
                    refine ⟨1615122589878313763134393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2153496786504418350845857 1615122589878313763134393)
                    ·
                      refine ⟨1211341942408735322350795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615122589878313763134393 1211341942408735322350795)
                      ·
                        rfl

theorem cell23_2359080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_2359080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359080 prefixEnd_2359080 := by exact prefixLift 2359080
  have htrace : WordTrace (prefixWord ++ tailWord_2359080) baseStart_2359080 baseEnd_2359080 := by
    simpa [prefixWord, tailWord_2359080, baseEnd_2359080] using wordTrace_append hprefix tailTrace_2359080
  have hstable : (prefixWord ++ tailWord_2359080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359080).length < 2 ^ (prefixWord ++ tailWord_2359080).sum := by decide
  have hdescent : baseEnd_2359080 < baseStart_2359080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359097 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2359097 : Nat := 118140960795 + 2359097 * 2 ^ 59
def prefixEnd_2359097 : Nat := 4983230072969 + 3 ^ 40 * 2359097 * 2
def baseEnd_2359097 : Nat := 1211350671579861755838217

theorem tailTrace_2359097 : CollatzResearch.WordTrace tailWord_2359097 prefixEnd_2359097 1211350671579861755838217 := by
  unfold tailWord_2359097
  simp only [CollatzResearch.WordTrace]
  refine ⟨86043336334401945536067545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57362224222934630357378363 86043336334401945536067545)
  ·
    refine ⟨64532502250801459152050659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86043336334401945536067545 64532502250801459152050659)
    ·
      refine ⟨96798753376202188728075989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64532502250801459152050659 96798753376202188728075989)
      ·
        refine ⟨2268720782254738798314281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 96798753376202188728075989 2268720782254738798314281)
        ·
          refine ⟨1701540586691054098735711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268720782254738798314281 1701540586691054098735711)
          ·
            refine ⟨2552310880036581148103567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701540586691054098735711 2552310880036581148103567)
            ·
              refine ⟨3828466320054871722155351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552310880036581148103567 3828466320054871722155351)
              ·
                refine ⟨5742699480082307583233027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828466320054871722155351 5742699480082307583233027)
                ·
                  refine ⟨8614049220123461374849541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5742699480082307583233027 8614049220123461374849541)
                  ·
                    refine ⟨1615134228773149007784289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8614049220123461374849541 1615134228773149007784289)
                    ·
                      refine ⟨1211350671579861755838217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615134228773149007784289 1211350671579861755838217)
                      ·
                        rfl

theorem cell23_2359097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2359097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359097 prefixEnd_2359097 := by exact prefixLift 2359097
  have htrace : WordTrace (prefixWord ++ tailWord_2359097) baseStart_2359097 baseEnd_2359097 := by
    simpa [prefixWord, tailWord_2359097, baseEnd_2359097] using wordTrace_append hprefix tailTrace_2359097
  have hstable : (prefixWord ++ tailWord_2359097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359097).length < 2 ^ (prefixWord ++ tailWord_2359097).sum := by decide
  have hdescent : baseEnd_2359097 < baseStart_2359097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359136 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2359136 : Nat := 118140960795 + 2359136 * 2 ^ 59
def prefixEnd_2359136 : Nat := 4983230072969 + 3 ^ 40 * 2359136 * 2
def baseEnd_2359136 : Nat := 1211370697325387103250537

theorem tailTrace_2359136 : CollatzResearch.WordTrace tailWord_2359136 prefixEnd_2359136 1211370697325387103250537 := by
  unfold tailWord_2359136
  simp only [CollatzResearch.WordTrace]
  refine ⟨43022379390630327598368631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57363172520840436797824841 43022379390630327598368631)
  ·
    refine ⟨64533569085945491397552947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43022379390630327598368631 64533569085945491397552947)
    ·
      refine ⟨96800353628918237096329421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64533569085945491397552947 96800353628918237096329421)
      ·
        refine ⟨36300132610844338911123533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96800353628918237096329421 36300132610844338911123533)
        ·
          refine ⟨13612549729066627091671325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36300132610844338911123533 13612549729066627091671325)
          ·
            refine ⟨5104706148399985159376747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13612549729066627091671325 5104706148399985159376747)
            ·
              refine ⟨7657059222599977739065121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5104706148399985159376747 7657059222599977739065121)
              ·
                refine ⟨5742794416949983304298841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7657059222599977739065121 5742794416949983304298841)
                ·
                  refine ⟨4307095812712487478224131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5742794416949983304298841 4307095812712487478224131)
                  ·
                    refine ⟨6460643719068731217336197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4307095812712487478224131 6460643719068731217336197)
                    ·
                      refine ⟨1211370697325387103250537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6460643719068731217336197 1211370697325387103250537)
                      ·
                        rfl

theorem cell23_2359136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2359136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359136 prefixEnd_2359136 := by exact prefixLift 2359136
  have htrace : WordTrace (prefixWord ++ tailWord_2359136) baseStart_2359136 baseEnd_2359136 := by
    simpa [prefixWord, tailWord_2359136, baseEnd_2359136] using wordTrace_append hprefix tailTrace_2359136
  have hstable : (prefixWord ++ tailWord_2359136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359136).length < 2 ^ (prefixWord ++ tailWord_2359136).sum := by decide
  have hdescent : baseEnd_2359136 < baseStart_2359136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359149 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2359149 : Nat := 118140960795 + 2359149 * 2 ^ 59
def prefixEnd_2359149 : Nat := 4983230072969 + 3 ^ 40 * 2359149 * 2
def baseEnd_2359149 : Nat := 1211377372573895552387977

theorem tailTrace_2359149 : CollatzResearch.WordTrace tailWord_2359149 prefixEnd_2359149 1211377372573895552387977 := by
  unfold tailWord_2359149
  simp only [CollatzResearch.WordTrace]
  refine ⟨86045232930213558416960501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57363488620142372277973667 86045232930213558416960501)
  ·
    refine ⟨8066740587207521101590047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86045232930213558416960501 8066740587207521101590047)
    ·
      refine ⟨12100110880811281652385071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8066740587207521101590047 12100110880811281652385071)
      ·
        refine ⟨18150166321216922478577607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12100110880811281652385071 18150166321216922478577607)
        ·
          refine ⟨27225249481825383717866411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18150166321216922478577607 27225249481825383717866411)
          ·
            refine ⟨40837874222738075576799617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27225249481825383717866411 40837874222738075576799617)
            ·
              refine ⟨30628405667053556682599713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40837874222738075576799617 30628405667053556682599713)
              ·
                refine ⟨22971304250290167511949785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30628405667053556682599713 22971304250290167511949785)
                ·
                  refine ⟨17228478187717625633962339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22971304250290167511949785 17228478187717625633962339)
                  ·
                    refine ⟨25842717281576438450943509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17228478187717625633962339 25842717281576438450943509)
                    ·
                      refine ⟨1211377372573895552387977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25842717281576438450943509 1211377372573895552387977)
                      ·
                        rfl

theorem cell23_2359149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2359149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359149 prefixEnd_2359149 := by exact prefixLift 2359149
  have htrace : WordTrace (prefixWord ++ tailWord_2359149) baseStart_2359149 baseEnd_2359149 := by
    simpa [prefixWord, tailWord_2359149, baseEnd_2359149] using wordTrace_append hprefix tailTrace_2359149
  have hstable : (prefixWord ++ tailWord_2359149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359149).length < 2 ^ (prefixWord ++ tailWord_2359149).sum := by decide
  have hdescent : baseEnd_2359149 < baseStart_2359149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359197 : List Nat := [1, 4, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_2359197 : Nat := 118140960795 + 2359197 * 2 ^ 59
def prefixEnd_2359197 : Nat := 4983230072969 + 3 ^ 40 * 2359197 * 2
def baseEnd_2359197 : Nat := 403800673215103788195919

theorem tailTrace_2359197 : CollatzResearch.WordTrace tailWord_2359197 prefixEnd_2359197 403800673215103788195919 := by
  unfold tailWord_2359197
  simp only [CollatzResearch.WordTrace]
  refine ⟨86046983634039662614707845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57364655756026441743138563 86046983634039662614707845)
  ·
    refine ⟨16133809431382436740257721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86046983634039662614707845 16133809431382436740257721)
    ·
      refine ⟨12100357073536827555193291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16133809431382436740257721 12100357073536827555193291)
      ·
        refine ⟨18150535610305241332789937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12100357073536827555193291 18150535610305241332789937)
        ·
          refine ⟨13612901707728930999592453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18150535610305241332789937 13612901707728930999592453)
          ·
            refine ⟨2552419070199174562423585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13612901707728930999592453 2552419070199174562423585)
            ·
              refine ⟨1914314302649380921817689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552419070199174562423585 1914314302649380921817689)
              ·
                refine ⟨1435735726987035691363267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1914314302649380921817689 1435735726987035691363267)
                ·
                  refine ⟨2153603590480553537044901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435735726987035691363267 2153603590480553537044901)
                  ·
                    refine ⟨403800673215103788195919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153603590480553537044901 403800673215103788195919)
                    ·
                      rfl

theorem cell23_2359197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_2359197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359197 prefixEnd_2359197 := by exact prefixLift 2359197
  have htrace : WordTrace (prefixWord ++ tailWord_2359197) baseStart_2359197 baseEnd_2359197 := by
    simpa [prefixWord, tailWord_2359197, baseEnd_2359197] using wordTrace_append hprefix tailTrace_2359197
  have hstable : (prefixWord ++ tailWord_2359197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359197).length < 2 ^ (prefixWord ++ tailWord_2359197).sum := by decide
  have hdescent : baseEnd_2359197 < baseStart_2359197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359226 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2]
def baseStart_2359226 : Nat := 118140960795 + 2359226 * 2 ^ 59
def prefixEnd_2359226 : Nat := 4983230072969 + 3 ^ 40 * 2359226 * 2
def baseEnd_2359226 : Nat := 1211416910584291751125123

theorem tailTrace_2359226 : CollatzResearch.WordTrace tailWord_2359226 prefixEnd_2359226 1211416910584291751125123 := by
  unfold tailWord_2359226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21512010337733650141878383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57365360900623067045009021 21512010337733650141878383)
  ·
    refine ⟨32268015506600475212817575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21512010337733650141878383 32268015506600475212817575)
    ·
      refine ⟨48402023259900712819226363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32268015506600475212817575 48402023259900712819226363)
      ·
        refine ⟨72603034889851069228839545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48402023259900712819226363 72603034889851069228839545)
        ·
          refine ⟨54452276167388301921629659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72603034889851069228839545 54452276167388301921629659)
          ·
            refine ⟨81678414251082452882444489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54452276167388301921629659 81678414251082452882444489)
            ·
              refine ⟨61258810688311839661833367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81678414251082452882444489 61258810688311839661833367)
              ·
                refine ⟨91888216032467759492750051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61258810688311839661833367 91888216032467759492750051)
                ·
                  refine ⟨137832324048701639239125077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91888216032467759492750051 137832324048701639239125077)
                  ·
                    refine ⟨1615222547445722334833497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 137832324048701639239125077 1615222547445722334833497)
                    ·
                      refine ⟨1211416910584291751125123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615222547445722334833497 1211416910584291751125123)
                      ·
                        rfl

theorem cell23_2359226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_2359226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359226 prefixEnd_2359226 := by exact prefixLift 2359226
  have htrace : WordTrace (prefixWord ++ tailWord_2359226) baseStart_2359226 baseEnd_2359226 := by
    simpa [prefixWord, tailWord_2359226, baseEnd_2359226] using wordTrace_append hprefix tailTrace_2359226
  have hstable : (prefixWord ++ tailWord_2359226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359226).length < 2 ^ (prefixWord ++ tailWord_2359226).sum := by decide
  have hdescent : baseEnd_2359226 < baseStart_2359226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359230 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_2359230 : Nat := 118140960795 + 2359230 * 2 ^ 59
def prefixEnd_2359230 : Nat := 4983230072969 + 3 ^ 40 * 2359230 * 2
def baseEnd_2359230 : Nat := 1211418964506909735475105

theorem tailTrace_2359230 : CollatzResearch.WordTrace tailWord_2359230 prefixEnd_2359230 1211418964506909735475105 := by
  unfold tailWord_2359230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756023405365013656332393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57365458161946739500439429 10756023405365013656332393)
  ·
    refine ⟨8067017554023760242249295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10756023405365013656332393 8067017554023760242249295)
    ·
      refine ⟨12100526331035640363373943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8067017554023760242249295 12100526331035640363373943)
      ·
        refine ⟨18150789496553460545060915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12100526331035640363373943 18150789496553460545060915)
        ·
          refine ⟨27226184244830190817591373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18150789496553460545060915 27226184244830190817591373)
          ·
            refine ⟨10209819091811321556596765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27226184244830190817591373 10209819091811321556596765)
            ·
              refine ⟨3828682159429245583723787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10209819091811321556596765 3828682159429245583723787)
              ·
                refine ⟨5743023239143868375585681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828682159429245583723787 5743023239143868375585681)
                ·
                  refine ⟨4307267429357901281689261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5743023239143868375585681 4307267429357901281689261)
                  ·
                    refine ⟨1615225286009212980633473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4307267429357901281689261 1615225286009212980633473)
                    ·
                      refine ⟨1211418964506909735475105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615225286009212980633473 1211418964506909735475105)
                      ·
                        rfl

theorem cell23_2359230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_2359230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359230 prefixEnd_2359230 := by exact prefixLift 2359230
  have htrace : WordTrace (prefixWord ++ tailWord_2359230) baseStart_2359230 baseEnd_2359230 := by
    simpa [prefixWord, tailWord_2359230, baseEnd_2359230] using wordTrace_append hprefix tailTrace_2359230
  have hstable : (prefixWord ++ tailWord_2359230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359230).length < 2 ^ (prefixWord ++ tailWord_2359230).sum := by decide
  have hdescent : baseEnd_2359230 < baseStart_2359230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359239 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2359239 : Nat := 118140960795 + 2359239 * 2 ^ 59
def prefixEnd_2359239 : Nat := 4983230072969 + 3 ^ 40 * 2359239 * 2
def baseEnd_2359239 : Nat := 1211423585832800200262563

theorem tailTrace_2359239 : CollatzResearch.WordTrace tailWord_2359239 prefixEnd_2359239 1211423585832800200262563 := by
  unfold tailWord_2359239
  simp only [CollatzResearch.WordTrace]
  refine ⟨86048515499887503787736771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57365676999925002525157847 86048515499887503787736771)
  ·
    refine ⟨129072773249831255681605157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86048515499887503787736771 129072773249831255681605157)
    ·
      refine ⟨24201144984343360440300967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129072773249831255681605157 24201144984343360440300967)
      ·
        refine ⟨36301717476515040660451451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24201144984343360440300967 36301717476515040660451451)
        ·
          refine ⟨54452576214772560990677177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36301717476515040660451451 54452576214772560990677177)
          ·
            refine ⟨40839432161079420743007883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54452576214772560990677177 40839432161079420743007883)
            ·
              refine ⟨61259148241619131114511825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40839432161079420743007883 61259148241619131114511825)
              ·
                refine ⟨45944361181214348335883869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61259148241619131114511825 45944361181214348335883869)
                ·
                  refine ⟨17229135442955380625956451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45944361181214348335883869 17229135442955380625956451)
                  ·
                    refine ⟨25843703164433070938934677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17229135442955380625956451 25843703164433070938934677)
                    ·
                      refine ⟨1211423585832800200262563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25843703164433070938934677 1211423585832800200262563)
                      ·
                        rfl

theorem cell23_2359239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2359239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359239 prefixEnd_2359239 := by exact prefixLift 2359239
  have htrace : WordTrace (prefixWord ++ tailWord_2359239) baseStart_2359239 baseEnd_2359239 := by
    simpa [prefixWord, tailWord_2359239, baseEnd_2359239] using wordTrace_append hprefix tailTrace_2359239
  have hstable : (prefixWord ++ tailWord_2359239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359239).length < 2 ^ (prefixWord ++ tailWord_2359239).sum := by decide
  have hdescent : baseEnd_2359239 < baseStart_2359239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359240 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 1, 5]
def baseStart_2359240 : Nat := 118140960795 + 2359240 * 2 ^ 59
def prefixEnd_2359240 : Nat := 4983230072969 + 3 ^ 40 * 2359240 * 2
def baseEnd_2359240 : Nat := 403808033104484898783353

theorem tailTrace_2359240 : CollatzResearch.WordTrace tailWord_2359240 prefixEnd_2359240 403808033104484898783353 := by
  unfold tailWord_2359240
  simp only [CollatzResearch.WordTrace]
  refine ⟨43024275986441940479261587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57365701315255920639015449 43024275986441940479261587)
  ·
    refine ⟨64536413979662910718892381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43024275986441940479261587 64536413979662910718892381)
    ·
      refine ⟨24201155242373591519584643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64536413979662910718892381 24201155242373591519584643)
      ·
        refine ⟨36301732863560387279376965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24201155242373591519584643 36301732863560387279376965)
        ·
          refine ⟨6806574911917572614883181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36301732863560387279376965 6806574911917572614883181)
          ·
            refine ⟨2552465591969089730581193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6806574911917572614883181 2552465591969089730581193)
            ·
              refine ⟨1914349193976817297935895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552465591969089730581193 1914349193976817297935895)
              ·
                refine ⟨2871523790965225946903843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914349193976817297935895 2871523790965225946903843)
                ·
                  refine ⟨4307285686447838920355765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871523790965225946903843 4307285686447838920355765)
                  ·
                    refine ⟨403808033104484898783353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4307285686447838920355765 403808033104484898783353)
                    ·
                      rfl

theorem cell23_2359240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_2359240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359240 prefixEnd_2359240 := by exact prefixLift 2359240
  have htrace : WordTrace (prefixWord ++ tailWord_2359240) baseStart_2359240 baseEnd_2359240 := by
    simpa [prefixWord, tailWord_2359240, baseEnd_2359240] using wordTrace_append hprefix tailTrace_2359240
  have hstable : (prefixWord ++ tailWord_2359240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359240).length < 2 ^ (prefixWord ++ tailWord_2359240).sum := by decide
  have hdescent : baseEnd_2359240 < baseStart_2359240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359243 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 5, 2, 2]
def baseStart_2359243 : Nat := 118140960795 + 2359243 * 2 ^ 59
def prefixEnd_2359243 : Nat := 4983230072969 + 3 ^ 40 * 2359243 * 2
def baseEnd_2359243 : Nat := 1211425639755418184612545

theorem tailTrace_2359243 : CollatzResearch.WordTrace tailWord_2359243 prefixEnd_2359243 1211425639755418184612545 := by
  unfold tailWord_2359243
  simp only [CollatzResearch.WordTrace]
  refine ⟨86048661391873012470882383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57365774261248674980588255 86048661391873012470882383)
  ·
    refine ⟨129072992087809518706323575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86048661391873012470882383 129072992087809518706323575)
    ·
      refine ⟨193609488131714278059485363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129072992087809518706323575 193609488131714278059485363)
      ·
        refine ⟨290414232197571417089228045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193609488131714278059485363 290414232197571417089228045)
        ·
          refine ⟨108905337074089281408460517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290414232197571417089228045 108905337074089281408460517)
          ·
            refine ⟨20419750701391740264086347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108905337074089281408460517 20419750701391740264086347)
            ·
              refine ⟨30629626052087610396129521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20419750701391740264086347 30629626052087610396129521)
              ·
                refine ⟨22972219539065707797097141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30629626052087610396129521 22972219539065707797097141)
                ·
                  refine ⟨2153645581787410105977857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22972219539065707797097141 2153645581787410105977857)
                  ·
                    refine ⟨1615234186340557579483393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2153645581787410105977857 1615234186340557579483393)
                    ·
                      refine ⟨1211425639755418184612545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615234186340557579483393 1211425639755418184612545)
                      ·
                        rfl

theorem cell23_2359243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 2, 2].length) (baseStart_2359243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359243 prefixEnd_2359243 := by exact prefixLift 2359243
  have htrace : WordTrace (prefixWord ++ tailWord_2359243) baseStart_2359243 baseEnd_2359243 := by
    simpa [prefixWord, tailWord_2359243, baseEnd_2359243] using wordTrace_append hprefix tailTrace_2359243
  have hstable : (prefixWord ++ tailWord_2359243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359243).length < 2 ^ (prefixWord ++ tailWord_2359243).sum := by decide
  have hdescent : baseEnd_2359243 < baseStart_2359243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359246 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2359246 : Nat := 118140960795 + 2359246 * 2 ^ 59
def prefixEnd_2359246 : Nat := 4983230072969 + 3 ^ 40 * 2359246 * 2
def baseEnd_2359246 : Nat := 1211427180197381672875031

theorem tailTrace_2359246 : CollatzResearch.WordTrace tailWord_2359246 prefixEnd_2359246 1211427180197381672875031 := by
  unfold tailWord_2359246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756096351357767997905199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57365847207241429322161061 10756096351357767997905199)
  ·
    refine ⟨16134144527036651996857799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10756096351357767997905199 16134144527036651996857799)
    ·
      refine ⟨24201216790554977995286699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16134144527036651996857799 24201216790554977995286699)
      ·
        refine ⟨36301825185832466992930049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24201216790554977995286699 36301825185832466992930049)
        ·
          refine ⟨27226368889374350244697537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36301825185832466992930049 27226368889374350244697537)
          ·
            refine ⟨20419776667030762683523153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27226368889374350244697537 20419776667030762683523153)
            ·
              refine ⟨15314832500273072012642365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20419776667030762683523153 15314832500273072012642365)
              ·
                refine ⟨5743062187602402004740887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15314832500273072012642365 5743062187602402004740887)
                ·
                  refine ⟨8614593281403603007111331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743062187602402004740887 8614593281403603007111331)
                  ·
                    refine ⟨12921889922105404510666997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8614593281403603007111331 12921889922105404510666997)
                    ·
                      refine ⟨1211427180197381672875031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12921889922105404510666997 1211427180197381672875031)
                      ·
                        rfl

theorem cell23_2359246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2359246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359246 prefixEnd_2359246 := by exact prefixLift 2359246
  have htrace : WordTrace (prefixWord ++ tailWord_2359246) baseStart_2359246 baseEnd_2359246 := by
    simpa [prefixWord, tailWord_2359246, baseEnd_2359246] using wordTrace_append hprefix tailTrace_2359246
  have hstable : (prefixWord ++ tailWord_2359246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359246).length < 2 ^ (prefixWord ++ tailWord_2359246).sum := by decide
  have hdescent : baseEnd_2359246 < baseStart_2359246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359253 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_2359253 : Nat := 118140960795 + 2359253 * 2 ^ 59
def prefixEnd_2359253 : Nat := 4983230072969 + 3 ^ 40 * 2359253 * 2
def baseEnd_2359253 : Nat := 403810258187321048495833

theorem tailTrace_2359253 : CollatzResearch.WordTrace tailWord_2359253 prefixEnd_2359253 403810258187321048495833 := by
  unfold tailWord_2359253
  simp only [CollatzResearch.WordTrace]
  refine ⟨86049026121836784178746413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57366017414557856119164275 86049026121836784178746413)
  ·
    refine ⟨32268384795688794067029905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86049026121836784178746413 32268384795688794067029905)
    ·
      refine ⟨24201288596766595550272429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32268384795688794067029905 24201288596766595550272429)
      ·
        refine ⟨9075483223787473331352161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24201288596766595550272429 9075483223787473331352161)
        ·
          refine ⟨6806612417840604998514121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9075483223787473331352161 6806612417840604998514121)
          ·
            refine ⟨5104959313380453748885591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6806612417840604998514121 5104959313380453748885591)
            ·
              refine ⟨7657438970070680623328387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5104959313380453748885591 7657438970070680623328387)
              ·
                refine ⟨11486158455106020934992581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7657438970070680623328387 11486158455106020934992581)
                ·
                  refine ⟨2153654710332378925311109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11486158455106020934992581 2153654710332378925311109)
                  ·
                    refine ⟨403810258187321048495833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153654710332378925311109 403810258187321048495833)
                    ·
                      rfl

theorem cell23_2359253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_2359253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359253 prefixEnd_2359253 := by exact prefixLift 2359253
  have htrace : WordTrace (prefixWord ++ tailWord_2359253) baseStart_2359253 baseEnd_2359253 := by
    simpa [prefixWord, tailWord_2359253, baseEnd_2359253] using wordTrace_append hprefix tailTrace_2359253
  have hstable : (prefixWord ++ tailWord_2359253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359253).length < 2 ^ (prefixWord ++ tailWord_2359253).sum := by decide
  have hdescent : baseEnd_2359253 < baseStart_2359253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359277 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2359277 : Nat := 118140960795 + 2359277 * 2 ^ 59
def prefixEnd_2359277 : Nat := 4983230072969 + 3 ^ 40 * 2359277 * 2
def baseEnd_2359277 : Nat := 1211443098097671051587389

theorem tailTrace_2359277 : CollatzResearch.WordTrace tailWord_2359277 prefixEnd_2359277 1211443098097671051587389 := by
  unfold tailWord_2359277
  simp only [CollatzResearch.WordTrace]
  refine ⟨86049901473749836277620085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57366600982499890851746723 86049901473749836277620085)
  ·
    refine ⟨8067178263164047151026883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86049901473749836277620085 8067178263164047151026883)
    ·
      refine ⟨12100767394746070726540325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8067178263164047151026883 12100767394746070726540325)
      ·
        refine ⟨2268893886514888261226311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12100767394746070726540325 2268893886514888261226311)
        ·
          refine ⟨3403340829772332391839467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268893886514888261226311 3403340829772332391839467)
          ·
            refine ⟨5105011244658498587759201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403340829772332391839467 5105011244658498587759201)
            ·
              refine ⟨3828758433493873940819401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5105011244658498587759201 3828758433493873940819401)
              ·
                refine ⟨2871568825120405455614551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828758433493873940819401 2871568825120405455614551)
                ·
                  refine ⟨4307353237680608183421827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871568825120405455614551 4307353237680608183421827)
                  ·
                    refine ⟨6461029856520912275132741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4307353237680608183421827 6461029856520912275132741)
                    ·
                      refine ⟨1211443098097671051587389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6461029856520912275132741 1211443098097671051587389)
                      ·
                        rfl

theorem cell23_2359277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2359277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359277 prefixEnd_2359277 := by exact prefixLift 2359277
  have htrace : WordTrace (prefixWord ++ tailWord_2359277) baseStart_2359277 baseEnd_2359277 := by
    simpa [prefixWord, tailWord_2359277, baseEnd_2359277] using wordTrace_append hprefix tailTrace_2359277
  have hstable : (prefixWord ++ tailWord_2359277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359277).length < 2 ^ (prefixWord ++ tailWord_2359277).sum := by decide
  have hdescent : baseEnd_2359277 < baseStart_2359277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359293 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_2359293 : Nat := 118140960795 + 2359293 * 2 ^ 59
def prefixEnd_2359293 : Nat := 4983230072969 + 3 ^ 40 * 2359293 * 2
def baseEnd_2359293 : Nat := 1211451313788142988987315

theorem tailTrace_2359293 : CollatzResearch.WordTrace tailWord_2359293 prefixEnd_2359293 1211451313788142988987315 := by
  unfold tailWord_2359293
  simp only [CollatzResearch.WordTrace]
  refine ⟨86050485041691871010202533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57366990027794580673468355 86050485041691871010202533)
  ·
    refine ⟨16134465945317225814412975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86050485041691871010202533 16134465945317225814412975)
    ·
      refine ⟨24201698917975838721619463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16134465945317225814412975 24201698917975838721619463)
      ·
        refine ⟨36302548376963758082429195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24201698917975838721619463 36302548376963758082429195)
        ·
          refine ⟨54453822565445637123643793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36302548376963758082429195 54453822565445637123643793)
          ·
            refine ⟨40840366924084227842732845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54453822565445637123643793 40840366924084227842732845)
            ·
              refine ⟨15315137596531585441024817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40840366924084227842732845 15315137596531585441024817)
              ·
                refine ⟨11486353197398689080768613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15315137596531585441024817 11486353197398689080768613)
                ·
                  refine ⟨2153691224512254202644115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11486353197398689080768613 2153691224512254202644115)
                  ·
                    refine ⟨3230536836768381303966173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2153691224512254202644115 3230536836768381303966173)
                    ·
                      refine ⟨1211451313788142988987315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3230536836768381303966173 1211451313788142988987315)
                      ·
                        rfl

theorem cell23_2359293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_2359293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359293 prefixEnd_2359293 := by exact prefixLift 2359293
  have htrace : WordTrace (prefixWord ++ tailWord_2359293) baseStart_2359293 baseEnd_2359293 := by
    simpa [prefixWord, tailWord_2359293, baseEnd_2359293] using wordTrace_append hprefix tailTrace_2359293
  have hstable : (prefixWord ++ tailWord_2359293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359293).length < 2 ^ (prefixWord ++ tailWord_2359293).sum := by decide
  have hdescent : baseEnd_2359293 < baseStart_2359293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359299 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8]
def baseStart_2359299 : Nat := 118140960795 + 2359299 * 2 ^ 59
def prefixEnd_2359299 : Nat := 4983230072969 + 3 ^ 40 * 2359299 * 2
def baseEnd_2359299 : Nat := 1211454394672069965512287

theorem tailTrace_2359299 : CollatzResearch.WordTrace tailWord_2359299 prefixEnd_2359299 1211454394672069965512287 := by
  unfold tailWord_2359299
  simp only [CollatzResearch.WordTrace]
  refine ⟨86050703879670134034920951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57367135919780089356613967 86050703879670134034920951)
  ·
    refine ⟨129076055819505201052381427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86050703879670134034920951 129076055819505201052381427)
    ·
      refine ⟨193614083729257801578572141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129076055819505201052381427 193614083729257801578572141)
      ·
        refine ⟨72605281398471675591964553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193614083729257801578572141 72605281398471675591964553)
        ·
          refine ⟨54453961048853756693973415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72605281398471675591964553 54453961048853756693973415)
          ·
            refine ⟨81680941573280635040960123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54453961048853756693973415 81680941573280635040960123)
            ·
              refine ⟨122521412359920952561440185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81680941573280635040960123 122521412359920952561440185)
              ·
                refine ⟨91891059269940714421080139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122521412359920952561440185 91891059269940714421080139)
                ·
                  refine ⟨137836588904911071631620209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91891059269940714421080139 137836588904911071631620209)
                  ·
                    refine ⟨103377441678683303723715157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137836588904911071631620209 103377441678683303723715157)
                    ·
                      refine ⟨1211454394672069965512287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103377441678683303723715157 1211454394672069965512287)
                      ·
                        rfl

theorem cell23_2359299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_2359299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359299 prefixEnd_2359299 := by exact prefixLift 2359299
  have htrace : WordTrace (prefixWord ++ tailWord_2359299) baseStart_2359299 baseEnd_2359299 := by
    simpa [prefixWord, tailWord_2359299, baseEnd_2359299] using wordTrace_append hprefix tailTrace_2359299
  have hstable : (prefixWord ++ tailWord_2359299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359299).length < 2 ^ (prefixWord ++ tailWord_2359299).sum := by decide
  have hdescent : baseEnd_2359299 < baseStart_2359299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359300 : List Nat := [2, 3, 2, 4, 2, 1, 9]
def baseStart_2359300 : Nat := 118140960795 + 2359300 * 2 ^ 59
def prefixEnd_2359300 : Nat := 4983230072969 + 3 ^ 40 * 2359300 * 2
def baseEnd_2359300 : Nat := 14956233433984252612343

theorem tailTrace_2359300 : CollatzResearch.WordTrace tailWord_2359300 prefixEnd_2359300 14956233433984252612343 := by
  unfold tailWord_2359300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43025370176333255602853677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57367160235111007470471569 43025370176333255602853677)
  ·
    refine ⟨16134513816124970851070129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43025370176333255602853677 16134513816124970851070129)
    ·
      refine ⟨12100885362093728138302597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16134513816124970851070129 12100885362093728138302597)
      ·
        refine ⟨2268916005392574025931737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12100885362093728138302597 2268916005392574025931737)
        ·
          refine ⟨1701687004044430519448803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268916005392574025931737 1701687004044430519448803)
          ·
            refine ⟨2552530506066645779173205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701687004044430519448803 2552530506066645779173205)
            ·
              refine ⟨14956233433984252612343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2552530506066645779173205 14956233433984252612343)
              ·
                rfl

theorem cell23_2359300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 9].length) (baseStart_2359300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359300 prefixEnd_2359300 := by exact prefixLift 2359300
  have htrace : WordTrace (prefixWord ++ tailWord_2359300) baseStart_2359300 baseEnd_2359300 := by
    simpa [prefixWord, tailWord_2359300, baseEnd_2359300] using wordTrace_append hprefix tailTrace_2359300
  have hstable : (prefixWord ++ tailWord_2359300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359300).length < 2 ^ (prefixWord ++ tailWord_2359300).sum := by decide
  have hdescent : baseEnd_2359300 < baseStart_2359300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359310 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2359310 : Nat := 118140960795 + 2359310 * 2 ^ 59
def prefixEnd_2359310 : Nat := 4983230072969 + 3 ^ 40 * 2359310 * 2
def baseEnd_2359310 : Nat := 1211460042959269422474737

theorem tailTrace_2359310 : CollatzResearch.WordTrace tailWord_2359310 prefixEnd_2359310 1211460042959269422474737 := by
  unfold tailWord_2359310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756388135328785364196423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57367403388420188609047589 10756388135328785364196423)
  ·
    refine ⟨16134582202993178046294635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10756388135328785364196423 16134582202993178046294635)
    ·
      refine ⟨24201873304489767069441953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16134582202993178046294635 24201873304489767069441953)
      ·
        refine ⟨18151404978367325302081465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24201873304489767069441953 18151404978367325302081465)
        ·
          refine ⟨13613553733775493976561099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18151404978367325302081465 13613553733775493976561099)
          ·
            refine ⟨20420330600663240964841649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13613553733775493976561099 20420330600663240964841649)
            ·
              refine ⟨15315247950497430723631237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20420330600663240964841649 15315247950497430723631237)
              ·
                refine ⟨2871608990718268260680857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15315247950497430723631237 2871608990718268260680857)
                ·
                  refine ⟨2153706743038701195510643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871608990718268260680857 2153706743038701195510643)
                  ·
                    refine ⟨3230560114558051793265965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2153706743038701195510643 3230560114558051793265965)
                    ·
                      refine ⟨1211460042959269422474737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3230560114558051793265965 1211460042959269422474737)
                      ·
                        rfl

theorem cell23_2359310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2359310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359310 prefixEnd_2359310 := by exact prefixLift 2359310
  have htrace : WordTrace (prefixWord ++ tailWord_2359310) baseStart_2359310 baseEnd_2359310 := by
    simpa [prefixWord, tailWord_2359310, baseEnd_2359310] using wordTrace_append hprefix tailTrace_2359310
  have hstable : (prefixWord ++ tailWord_2359310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359310).length < 2 ^ (prefixWord ++ tailWord_2359310).sum := by decide
  have hdescent : baseEnd_2359310 < baseStart_2359310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359367 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_2359367 : Nat := 118140960795 + 2359367 * 2 ^ 59
def prefixEnd_2359367 : Nat := 4983230072969 + 3 ^ 40 * 2359367 * 2
def baseEnd_2359367 : Nat := 1211489311356575699461975

theorem tailTrace_2359367 : CollatzResearch.WordTrace tailWord_2359367 prefixEnd_2359367 1211489311356575699461975 := by
  unfold tailWord_2359367
  simp only [CollatzResearch.WordTrace]
  refine ⟨86053184043423781648396355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57368789362282521098930903 86053184043423781648396355)
  ·
    refine ⟨129079776065135672472594533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86053184043423781648396355 129079776065135672472594533)
    ·
      refine ⟨24202458012212938588611475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129079776065135672472594533 24202458012212938588611475)
      ·
        refine ⟨36303687018319407882917213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24202458012212938588611475 36303687018319407882917213)
        ·
          refine ⟨13613882631869777956093955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36303687018319407882917213 13613882631869777956093955)
          ·
            refine ⟨20420823947804666934140933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13613882631869777956093955 20420823947804666934140933)
            ·
              refine ⟨3828904490213375050151425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20420823947804666934140933 3828904490213375050151425)
              ·
                refine ⟨2871678367660031287613569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828904490213375050151425 2871678367660031287613569)
                ·
                  refine ⟨2153758775745023465710177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871678367660031287613569 2153758775745023465710177)
                  ·
                    refine ⟨1615319081808767599282633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2153758775745023465710177 1615319081808767599282633)
                    ·
                      refine ⟨1211489311356575699461975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615319081808767599282633 1211489311356575699461975)
                      ·
                        rfl

theorem cell23_2359367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_2359367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359367 prefixEnd_2359367 := by exact prefixLift 2359367
  have htrace : WordTrace (prefixWord ++ tailWord_2359367) baseStart_2359367 baseEnd_2359367 := by
    simpa [prefixWord, tailWord_2359367, baseEnd_2359367] using wordTrace_append hprefix tailTrace_2359367
  have hstable : (prefixWord ++ tailWord_2359367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359367).length < 2 ^ (prefixWord ++ tailWord_2359367).sum := by decide
  have hdescent : baseEnd_2359367 < baseStart_2359367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359373 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2359373 : Nat := 118140960795 + 2359373 * 2 ^ 59
def prefixEnd_2359373 : Nat := 4983230072969 + 3 ^ 40 * 2359373 * 2
def baseEnd_2359373 : Nat := 134610265804500297331883

theorem tailTrace_2359373 : CollatzResearch.WordTrace tailWord_2359373 prefixEnd_2359373 134610265804500297331883 := by
  unfold tailWord_2359373
  simp only [CollatzResearch.WordTrace]
  refine ⟨86053402881402044673114773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57368935254268029782076515 86053402881402044673114773)
  ·
    refine ⟨4033753260065720844052255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86053402881402044673114773 4033753260065720844052255)
    ·
      refine ⟨6050629890098581266078383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033753260065720844052255 6050629890098581266078383)
      ·
        refine ⟨9075944835147871899117575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050629890098581266078383 9075944835147871899117575)
        ·
          refine ⟨13613917252721807848676363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075944835147871899117575 13613917252721807848676363)
          ·
            refine ⟨20420875879082711773014545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13613917252721807848676363 20420875879082711773014545)
            ·
              refine ⟨15315656909312033829760909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20420875879082711773014545 15315656909312033829760909)
              ·
                refine ⟨5743371340992012686160341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15315656909312033829760909 5743371340992012686160341)
                ·
                  refine ⟨134610265804500297331883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5743371340992012686160341 134610265804500297331883)
                  ·
                    rfl

theorem cell23_2359373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2359373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359373 prefixEnd_2359373 := by exact prefixLift 2359373
  have htrace : WordTrace (prefixWord ++ tailWord_2359373) baseStart_2359373 baseEnd_2359373 := by
    simpa [prefixWord, tailWord_2359373, baseEnd_2359373] using wordTrace_append hprefix tailTrace_2359373
  have hstable : (prefixWord ++ tailWord_2359373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359373).length < 2 ^ (prefixWord ++ tailWord_2359373).sum := by decide
  have hdescent : baseEnd_2359373 < baseStart_2359373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
