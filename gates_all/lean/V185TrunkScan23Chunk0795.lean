import V185TrunkScan23Chunk0794

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4701477 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 6]
def baseStart_4701477 : Nat := 118140960795 + 4701477 * 2 ^ 59
def prefixEnd_4701477 : Nat := 4983230072969 + 3 ^ 40 * 4701477 * 2
def baseEnd_4701477 : Nat := 268235276339823020368423

theorem tailTrace_4701477 : CollatzResearch.WordTrace tailWord_4701477 prefixEnd_4701477 268235276339823020368423 := by
  unfold tailWord_4701477
  simp only [CollatzResearch.WordTrace]
  refine ⟨171476953588359252190726685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114317969058906168127151123 171476953588359252190726685)
  ·
    refine ⟨64303857595634719571522507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171476953588359252190726685 64303857595634719571522507)
    ·
      refine ⟨96455786393452079357283761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64303857595634719571522507 96455786393452079357283761)
      ·
        refine ⟨72341839795089059517962821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96455786393452079357283761 72341839795089059517962821)
        ·
          refine ⟨13564094961579198659618029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72341839795089059517962821 13564094961579198659618029)
          ·
            refine ⟨5086535610592199497356761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13564094961579198659618029 5086535610592199497356761)
            ·
              refine ⟨3814901707944149623017571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5086535610592199497356761 3814901707944149623017571)
              ·
                refine ⟨5722352561916224434526357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814901707944149623017571 5722352561916224434526357)
                ·
                  refine ⟨268235276339823020368423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5722352561916224434526357 268235276339823020368423)
                  ·
                    rfl

theorem cell23_4701477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_4701477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701477 prefixEnd_4701477 := by exact prefixLift 4701477
  have htrace : WordTrace (prefixWord ++ tailWord_4701477) baseStart_4701477 baseEnd_4701477 := by
    simpa [prefixWord, tailWord_4701477, baseEnd_4701477] using wordTrace_append hprefix tailTrace_4701477
  have hstable : (prefixWord ++ tailWord_4701477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701477).length < 2 ^ (prefixWord ++ tailWord_4701477).sum := by decide
  have hdescent : baseEnd_4701477 < baseStart_4701477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701490 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_4701490 : Nat := 118140960795 + 4701490 * 2 ^ 59
def prefixEnd_4701490 : Nat := 4983230072969 + 3 ^ 40 * 4701490 * 2
def baseEnd_4701490 : Nat := 804708054102305210817749

theorem tailTrace_4701490 : CollatzResearch.WordTrace tailWord_4701490 prefixEnd_4701490 804708054102305210817749 := by
  unfold tailWord_4701490
  simp only [CollatzResearch.WordTrace]
  refine ⟨42869356934328038852737481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114318285158208103607299949 42869356934328038852737481)
  ·
    refine ⟨32152017700746029139553111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42869356934328038852737481 32152017700746029139553111)
    ·
      refine ⟨48228026551119043709329667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32152017700746029139553111 48228026551119043709329667)
      ·
        refine ⟨72342039826678565563994501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48228026551119043709329667 72342039826678565563994501)
        ·
          refine ⟨13564132467502231043248969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72342039826678565563994501 13564132467502231043248969)
          ·
            refine ⟨10173099350626673282436727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13564132467502231043248969 10173099350626673282436727)
            ·
              refine ⟨15259649025940009923655091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10173099350626673282436727 15259649025940009923655091)
              ·
                refine ⟨22889473538910014885482637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15259649025940009923655091 22889473538910014885482637)
                ·
                  refine ⟨8583552577091255582055989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22889473538910014885482637 8583552577091255582055989)
                  ·
                    refine ⟨804708054102305210817749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8583552577091255582055989 804708054102305210817749)
                    ·
                      rfl

theorem cell23_4701490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_4701490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701490 prefixEnd_4701490 := by exact prefixLift 4701490
  have htrace : WordTrace (prefixWord ++ tailWord_4701490) baseStart_4701490 baseEnd_4701490 := by
    simpa [prefixWord, tailWord_4701490, baseEnd_4701490] using wordTrace_append hprefix tailTrace_4701490
  have hstable : (prefixWord ++ tailWord_4701490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701490).length < 2 ^ (prefixWord ++ tailWord_4701490).sum := by decide
  have hdescent : baseEnd_4701490 < baseStart_4701490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701503 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 3, 6]
def baseStart_4701503 : Nat := 118140960795 + 4701503 * 2 ^ 59
def prefixEnd_4701503 : Nat := 4983230072969 + 3 ^ 40 * 4701503 * 2
def baseEnd_4701503 : Nat := 804710279185141360530229

theorem tailTrace_4701503 : CollatzResearch.WordTrace tailWord_4701503 prefixEnd_4701503 804710279185141360530229 := by
  unfold tailWord_4701503
  simp only [CollatzResearch.WordTrace]
  refine ⟨171477901886265058631173163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114318601257510039087448775 171477901886265058631173163)
  ·
    refine ⟨257216852829397587946759745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171477901886265058631173163 257216852829397587946759745)
    ·
      refine ⟨192912639622048190960069809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257216852829397587946759745 192912639622048190960069809)
      ·
        refine ⟨144684479716536143220052357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192912639622048190960069809 144684479716536143220052357)
        ·
          refine ⟨27128339946850526853759817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144684479716536143220052357 27128339946850526853759817)
          ·
            refine ⟨20346254960137895140319863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27128339946850526853759817 20346254960137895140319863)
            ·
              refine ⟨30519382440206842710479795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20346254960137895140319863 30519382440206842710479795)
              ·
                refine ⟨45779073660310264065719693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30519382440206842710479795 45779073660310264065719693)
                ·
                  refine ⟨17167152622616349024644885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45779073660310264065719693 17167152622616349024644885)
                  ·
                    refine ⟨804710279185141360530229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17167152622616349024644885 804710279185141360530229)
                    ·
                      rfl

theorem cell23_4701503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_4701503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701503 prefixEnd_4701503 := by exact prefixLift 4701503
  have htrace : WordTrace (prefixWord ++ tailWord_4701503) baseStart_4701503 baseEnd_4701503 := by
    simpa [prefixWord, tailWord_4701503, baseEnd_4701503] using wordTrace_append hprefix tailTrace_4701503
  have hstable : (prefixWord ++ tailWord_4701503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701503).length < 2 ^ (prefixWord ++ tailWord_4701503).sum := by decide
  have hdescent : baseEnd_4701503 < baseStart_4701503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701523 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4]
def baseStart_4701523 : Nat := 118140960795 + 4701523 * 2 ^ 59
def prefixEnd_4701523 : Nat := 4983230072969 + 3 ^ 40 * 4701523 * 2
def baseEnd_4701523 : Nat := 2414141107168514003340595

theorem tailTrace_4701523 : CollatzResearch.WordTrace tailWord_4701523 prefixEnd_4701523 2414141107168514003340595 := by
  unfold tailWord_4701523
  simp only [CollatzResearch.WordTrace]
  refine ⟨171478631346192602046901223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114319087564128401364600815 171478631346192602046901223)
  ·
    refine ⟨257217947019288903070351835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171478631346192602046901223 257217947019288903070351835)
    ·
      refine ⟨385826920528933354605527753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257217947019288903070351835 385826920528933354605527753)
      ·
        refine ⟨289370190396700015954145815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385826920528933354605527753 289370190396700015954145815)
        ·
          refine ⟨434055285595050023931218723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289370190396700015954145815 434055285595050023931218723)
          ·
            refine ⟨651082928392575035896828085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434055285595050023931218723 651082928392575035896828085)
            ·
              refine ⟨61039024536803909615327633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 651082928392575035896828085 61039024536803909615327633)
              ·
                refine ⟨45779268402602932211495725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61039024536803909615327633 45779268402602932211495725)
                ·
                  refine ⟨17167225650976099579310897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45779268402602932211495725 17167225650976099579310897)
                  ·
                    refine ⟨12875419238232074684483173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17167225650976099579310897 12875419238232074684483173)
                    ·
                      refine ⟨2414141107168514003340595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12875419238232074684483173 2414141107168514003340595)
                      ·
                        rfl

theorem cell23_4701523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_4701523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701523 prefixEnd_4701523 := by exact prefixLift 4701523
  have htrace : WordTrace (prefixWord ++ tailWord_4701523) baseStart_4701523 baseEnd_4701523 := by
    simpa [prefixWord, tailWord_4701523, baseEnd_4701523] using wordTrace_append hprefix tailTrace_4701523
  have hstable : (prefixWord ++ tailWord_4701523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701523).length < 2 ^ (prefixWord ++ tailWord_4701523).sum := by decide
  have hdescent : baseEnd_4701523 < baseStart_4701523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701530 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_4701530 : Nat := 118140960795 + 4701530 * 2 ^ 59
def prefixEnd_4701530 : Nat := 4983230072969 + 3 ^ 40 * 4701530 * 2
def baseEnd_4701530 : Nat := 2414144701533095475953063

theorem tailTrace_4701530 : CollatzResearch.WordTrace tailWord_4701530 prefixEnd_4701530 2414144701533095475953063 := by
  unfold tailWord_4701530
  simp only [CollatzResearch.WordTrace]
  refine ⟨42869721664291810560601511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114319257771444828161604029 42869721664291810560601511)
  ·
    refine ⟨64304582496437715840902267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42869721664291810560601511 64304582496437715840902267)
    ·
      refine ⟨96456873744656573761353401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64304582496437715840902267 96456873744656573761353401)
      ·
        refine ⟨72342655308492430321015051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96456873744656573761353401 72342655308492430321015051)
        ·
          refine ⟨108513982962738645481522577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72342655308492430321015051 108513982962738645481522577)
          ·
            refine ⟨81385487222053984111141933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108513982962738645481522577 81385487222053984111141933)
            ·
              refine ⟨30519557708270244041678225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81385487222053984111141933 30519557708270244041678225)
              ·
                refine ⟨22889668281202683031258669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30519557708270244041678225 22889668281202683031258669)
                ·
                  refine ⟨8583625605451006136722001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22889668281202683031258669 8583625605451006136722001)
                  ·
                    refine ⟨6437719204088254602541501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8583625605451006136722001 6437719204088254602541501)
                    ·
                      refine ⟨2414144701533095475953063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6437719204088254602541501 2414144701533095475953063)
                      ·
                        rfl

theorem cell23_4701530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_4701530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701530 prefixEnd_4701530 := by exact prefixLift 4701530
  have htrace : WordTrace (prefixWord ++ tailWord_4701530) baseStart_4701530 baseEnd_4701530 := by
    simpa [prefixWord, tailWord_4701530, baseEnd_4701530] using wordTrace_append hprefix tailTrace_4701530
  have hstable : (prefixWord ++ tailWord_4701530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701530).length < 2 ^ (prefixWord ++ tailWord_4701530).sum := by decide
  have hdescent : baseEnd_4701530 < baseStart_4701530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701540 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_4701540 : Nat := 118140960795 + 4701540 * 2 ^ 59
def prefixEnd_4701540 : Nat := 4983230072969 + 3 ^ 40 * 4701540 * 2
def baseEnd_4701540 : Nat := 2414149836339640436828017

theorem tailTrace_4701540 : CollatzResearch.WordTrace tailWord_4701540 prefixEnd_4701540 2414149836339640436828017 := by
  unfold tailWord_4701540
  simp only [CollatzResearch.WordTrace]
  refine ⟨85739625693565506975135037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114319500924754009300180049 85739625693565506975135037)
  ·
    refine ⟨32152359635087065115675639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85739625693565506975135037 32152359635087065115675639)
    ·
      refine ⟨48228539452630597673513459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32152359635087065115675639 48228539452630597673513459)
      ·
        refine ⟨72342809178945896510270189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48228539452630597673513459 72342809178945896510270189)
        ·
          refine ⟨27128553442104711191351321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72342809178945896510270189 27128553442104711191351321)
          ·
            refine ⟨20346415081578533393513491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27128553442104711191351321 20346415081578533393513491)
            ·
              refine ⟨30519622622367800090270237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20346415081578533393513491 30519622622367800090270237)
              ·
                refine ⟨11444858483387925033851339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30519622622367800090270237 11444858483387925033851339)
                ·
                  refine ⟨17167287725081887550777009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11444858483387925033851339 17167287725081887550777009)
                  ·
                    refine ⟨12875465793811415663082757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17167287725081887550777009 12875465793811415663082757)
                    ·
                      refine ⟨2414149836339640436828017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12875465793811415663082757 2414149836339640436828017)
                      ·
                        rfl

theorem cell23_4701540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_4701540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701540 prefixEnd_4701540 := by exact prefixLift 4701540
  have htrace : WordTrace (prefixWord ++ tailWord_4701540) baseStart_4701540 baseEnd_4701540 := by
    simpa [prefixWord, tailWord_4701540, baseEnd_4701540] using wordTrace_append hprefix tailTrace_4701540
  have hstable : (prefixWord ++ tailWord_4701540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701540).length < 2 ^ (prefixWord ++ tailWord_4701540).sum := by decide
  have hdescent : baseEnd_4701540 < baseStart_4701540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701617 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 3, 4, 2]
def baseStart_4701617 : Nat := 118140960795 + 4701617 * 2 ^ 59
def prefixEnd_4701617 : Nat := 4983230072969 + 3 ^ 40 * 4701617 * 2
def baseEnd_4701617 : Nat := 2414189374350036635565163

theorem tailTrace_4701617 : CollatzResearch.WordTrace tailWord_4701617 prefixEnd_4701617 2414189374350036635565163 := by
  unfold tailWord_4701617
  simp only [CollatzResearch.WordTrace]
  refine ⟨171482059807852056100823105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114321373205234704067215403 171482059807852056100823105)
  ·
    refine ⟨128611544855889042075617329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171482059807852056100823105 128611544855889042075617329)
    ·
      refine ⟨96458658641916781556712997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128611544855889042075617329 96458658641916781556712997)
      ·
        refine ⟨18085998495359396541883687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96458658641916781556712997 18085998495359396541883687)
        ·
          refine ⟨27128997743039094812825531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18085998495359396541883687 27128997743039094812825531)
          ·
            refine ⟨40693496614558642219238297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27128997743039094812825531 40693496614558642219238297)
            ·
              refine ⟨30520122460918981664428723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40693496614558642219238297 30520122460918981664428723)
              ·
                refine ⟨45780183691378472496643085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30520122460918981664428723 45780183691378472496643085)
                ·
                  refine ⟨17167568884266927186241157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45780183691378472496643085 17167568884266927186241157)
                  ·
                    refine ⟨3218919165800048847420217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17167568884266927186241157 3218919165800048847420217)
                    ·
                      refine ⟨2414189374350036635565163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218919165800048847420217 2414189374350036635565163)
                      ·
                        rfl

theorem cell23_4701617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_4701617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701617 prefixEnd_4701617 := by exact prefixLift 4701617
  have htrace : WordTrace (prefixWord ++ tailWord_4701617) baseStart_4701617 baseEnd_4701617 := by
    simpa [prefixWord, tailWord_4701617, baseEnd_4701617] using wordTrace_append hprefix tailTrace_4701617
  have hstable : (prefixWord ++ tailWord_4701617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701617).length < 2 ^ (prefixWord ++ tailWord_4701617).sum := by decide
  have hdescent : baseEnd_4701617 < baseStart_4701617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701680 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_4701680 : Nat := 118140960795 + 4701680 * 2 ^ 59
def prefixEnd_4701680 : Nat := 4983230072969 + 3 ^ 40 * 4701680 * 2
def baseEnd_4701680 : Nat := 2414221723631269889077373

theorem tailTrace_4701680 : CollatzResearch.WordTrace tailWord_4701680 prefixEnd_4701680 2414221723631269889077373 := by
  unfold tailWord_4701680
  simp only [CollatzResearch.WordTrace]
  refine ⟨85742178803311908930183247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114322905071082545240244329 85742178803311908930183247)
  ·
    refine ⟨128613268204967863395274871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85742178803311908930183247 128613268204967863395274871)
    ·
      refine ⟨192919902307451795092912307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128613268204967863395274871 192919902307451795092912307)
      ·
        refine ⟨289379853461177692639368461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192919902307451795092912307 289379853461177692639368461)
        ·
          refine ⟨108517445047941634739763173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289379853461177692639368461 108517445047941634739763173)
          ·
            refine ⟨20347020946489056513705595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108517445047941634739763173 20347020946489056513705595)
            ·
              refine ⟨30520531419733584770558393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20347020946489056513705595 30520531419733584770558393)
              ·
                refine ⟨22890398564800188577918795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30520531419733584770558393 22890398564800188577918795)
                ·
                  refine ⟨34335597847200282866878193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22890398564800188577918795 34335597847200282866878193)
                  ·
                    refine ⟨25751698385400212150158645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34335597847200282866878193 25751698385400212150158645)
                    ·
                      refine ⟨2414221723631269889077373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25751698385400212150158645 2414221723631269889077373)
                      ·
                        rfl

theorem cell23_4701680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_4701680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701680 prefixEnd_4701680 := by exact prefixLift 4701680
  have htrace : WordTrace (prefixWord ++ tailWord_4701680) baseStart_4701680 baseEnd_4701680 := by
    simpa [prefixWord, tailWord_4701680, baseEnd_4701680] using wordTrace_append hprefix tailTrace_4701680
  have hstable : (prefixWord ++ tailWord_4701680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701680).length < 2 ^ (prefixWord ++ tailWord_4701680).sum := by decide
  have hdescent : baseEnd_4701680 < baseStart_4701680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701717 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_4701717 : Nat := 118140960795 + 4701717 * 2 ^ 59
def prefixEnd_4701717 : Nat := 4983230072969 + 3 ^ 40 * 4701717 * 2
def baseEnd_4701717 : Nat := 804746907471828748104901

theorem tailTrace_4701717 : CollatzResearch.WordTrace tailWord_4701717 prefixEnd_4701717 804746907471828748104901 := by
  unfold tailWord_4701717
  simp only [CollatzResearch.WordTrace]
  refine ⟨171485707107489773179463405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114323804738326515452975603 171485707107489773179463405)
  ·
    refine ⟨64307140165308664942298777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171485707107489773179463405 64307140165308664942298777)
    ·
      refine ⟨48230355123981498706724083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64307140165308664942298777 48230355123981498706724083)
      ·
        refine ⟨72345532685972248060086125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48230355123981498706724083 72345532685972248060086125)
        ·
          refine ⟨27129574757239593022532297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72345532685972248060086125 27129574757239593022532297)
          ·
            refine ⟨20347181067929694766899223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27129574757239593022532297 20347181067929694766899223)
            ·
              refine ⟨30520771601894542150348835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20347181067929694766899223 30520771601894542150348835)
              ·
                refine ⟨45781157402841813225523253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30520771601894542150348835 45781157402841813225523253)
                ·
                  refine ⟨4291983506516419989892805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45781157402841813225523253 4291983506516419989892805)
                  ·
                    refine ⟨804746907471828748104901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4291983506516419989892805 804746907471828748104901)
                    ·
                      rfl

theorem cell23_4701717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_4701717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701717 prefixEnd_4701717 := by exact prefixLift 4701717
  have htrace : WordTrace (prefixWord ++ tailWord_4701717) baseStart_4701717 baseEnd_4701717 := by
    simpa [prefixWord, tailWord_4701717, baseEnd_4701717] using wordTrace_append hprefix tailTrace_4701717
  have hstable : (prefixWord ++ tailWord_4701717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701717).length < 2 ^ (prefixWord ++ tailWord_4701717).sum := by decide
  have hdescent : baseEnd_4701717 < baseStart_4701717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701747 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 6]
def baseStart_4701747 : Nat := 118140960795 + 4701747 * 2 ^ 59
def prefixEnd_4701747 : Nat := 4983230072969 + 3 ^ 40 * 4701747 * 2
def baseEnd_4701747 : Nat := 268250680759457902993285

theorem tailTrace_4701747 : CollatzResearch.WordTrace tailWord_4701747 prefixEnd_4701747 268250680759457902993285 := by
  unfold tailWord_4701747
  simp only [CollatzResearch.WordTrace]
  refine ⟨171486801297381088303055495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114324534198254058868703663 171486801297381088303055495)
  ·
    refine ⟨257230201946071632454583243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171486801297381088303055495 257230201946071632454583243)
    ·
      refine ⟨385845302919107448681874865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257230201946071632454583243 385845302919107448681874865)
      ·
        refine ⟨289383977189330586511406149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385845302919107448681874865 289383977189330586511406149)
        ·
          refine ⟨54259495722999484970888653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 289383977189330586511406149 54259495722999484970888653)
          ·
            refine ⟨20347310896124806864083245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54259495722999484970888653 20347310896124806864083245)
            ·
              refine ⟨7630241586046802574031217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20347310896124806864083245 7630241586046802574031217)
              ·
                refine ⟨5722681189535101930523413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7630241586046802574031217 5722681189535101930523413)
                ·
                  refine ⟨268250680759457902993285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5722681189535101930523413 268250680759457902993285)
                  ·
                    rfl

theorem cell23_4701747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 6].length) (baseStart_4701747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701747 prefixEnd_4701747 := by exact prefixLift 4701747
  have htrace : WordTrace (prefixWord ++ tailWord_4701747) baseStart_4701747 baseEnd_4701747 := by
    simpa [prefixWord, tailWord_4701747, baseEnd_4701747] using wordTrace_append hprefix tailTrace_4701747
  have hstable : (prefixWord ++ tailWord_4701747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701747).length < 2 ^ (prefixWord ++ tailWord_4701747).sum := by decide
  have hdescent : baseEnd_4701747 < baseStart_4701747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701784 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 2, 3, 2]
def baseStart_4701784 : Nat := 118140960795 + 4701784 * 2 ^ 59
def prefixEnd_4701784 : Nat := 4983230072969 + 3 ^ 40 * 4701784 * 2
def baseEnd_4701784 : Nat := 2414275125619337482176895

theorem tailTrace_4701784 : CollatzResearch.WordTrace tailWord_4701784 prefixEnd_4701784 2414275125619337482176895 := by
  unfold tailWord_4701784
  simp only [CollatzResearch.WordTrace]
  refine ⟨85744075399123521811076203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114325433865498029081434937 85744075399123521811076203)
  ·
    refine ⟨128616113098685282716614305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85744075399123521811076203 128616113098685282716614305)
    ·
      refine ⟨96462084824013962037460729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128616113098685282716614305 96462084824013962037460729)
      ·
        refine ⟨72346563618010471528095547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96462084824013962037460729 72346563618010471528095547)
        ·
          refine ⟨108519845427015707292143321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72346563618010471528095547 108519845427015707292143321)
          ·
            refine ⟨81389884070261780469107491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108519845427015707292143321 81389884070261780469107491)
            ·
              refine ⟨122084826105392670703661237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81389884070261780469107491 122084826105392670703661237)
              ·
                refine ⟨11445452447380562878468241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122084826105392670703661237 11445452447380562878468241)
                ·
                  refine ⟨8584089335535422158851181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11445452447380562878468241 8584089335535422158851181)
                  ·
                    refine ⟨3219033500825783309569193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8584089335535422158851181 3219033500825783309569193)
                    ·
                      refine ⟨2414275125619337482176895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219033500825783309569193 2414275125619337482176895)
                      ·
                        rfl

theorem cell23_4701784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_4701784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701784 prefixEnd_4701784 := by exact prefixLift 4701784
  have htrace : WordTrace (prefixWord ++ tailWord_4701784) baseStart_4701784 baseEnd_4701784 := by
    simpa [prefixWord, tailWord_4701784, baseEnd_4701784] using wordTrace_append hprefix tailTrace_4701784
  have hstable : (prefixWord ++ tailWord_4701784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701784).length < 2 ^ (prefixWord ++ tailWord_4701784).sum := by decide
  have hdescent : baseEnd_4701784 < baseStart_4701784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701817 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_4701817 : Nat := 118140960795 + 4701817 * 2 ^ 59
def prefixEnd_4701817 : Nat := 4983230072969 + 3 ^ 40 * 4701817 * 2
def baseEnd_4701817 : Nat := 2414292070480935853064243

theorem tailTrace_4701817 : CollatzResearch.WordTrace tailWord_4701817 prefixEnd_4701817 2414292070480935853064243 := by
  unfold tailWord_4701817
  simp only [CollatzResearch.WordTrace]
  refine ⟨171489354407127490258103705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114326236271418326838735803 171489354407127490258103705)
  ·
    refine ⟨128617015805345617693577779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171489354407127490258103705 128617015805345617693577779)
    ·
      refine ⟨192925523708018426540366669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128617015805345617693577779 192925523708018426540366669)
      ·
        refine ⟨72347071390506909952637501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192925523708018426540366669 72347071390506909952637501)
        ·
          refine ⟨27130151771440091232239063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72347071390506909952637501 27130151771440091232239063)
          ·
            refine ⟨40695227657160136848358595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27130151771440091232239063 40695227657160136848358595)
            ·
              refine ⟨61042841485740205272537893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40695227657160136848358595 61042841485740205272537893)
              ·
                refine ⟨11445532778576288488600855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61042841485740205272537893 11445532778576288488600855)
                ·
                  refine ⟨17168299167864432732901283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11445532778576288488600855 17168299167864432732901283)
                  ·
                    refine ⟨25752448751796649099351925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17168299167864432732901283 25752448751796649099351925)
                    ·
                      refine ⟨2414292070480935853064243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25752448751796649099351925 2414292070480935853064243)
                      ·
                        rfl

theorem cell23_4701817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_4701817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701817 prefixEnd_4701817 := by exact prefixLift 4701817
  have htrace : WordTrace (prefixWord ++ tailWord_4701817) baseStart_4701817 baseEnd_4701817 := by
    simpa [prefixWord, tailWord_4701817, baseEnd_4701817] using wordTrace_append hprefix tailTrace_4701817
  have hstable : (prefixWord ++ tailWord_4701817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701817).length < 2 ^ (prefixWord ++ tailWord_4701817).sum := by decide
  have hdescent : baseEnd_4701817 < baseStart_4701817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701824 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 2, 4]
def baseStart_4701824 : Nat := 118140960795 + 4701824 * 2 ^ 59
def prefixEnd_4701824 : Nat := 4983230072969 + 3 ^ 40 * 4701824 * 2
def baseEnd_4701824 : Nat := 804765221615172441892237

theorem tailTrace_4701824 : CollatzResearch.WordTrace tailWord_4701824 prefixEnd_4701824 804765221615172441892237 := by
  unfold tailWord_4701824
  simp only [CollatzResearch.WordTrace]
  refine ⟨85744804859051065226804263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114326406478734753635739017 85744804859051065226804263)
  ·
    refine ⟨128617207288576597840206395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85744804859051065226804263 128617207288576597840206395)
    ·
      refine ⟨192925810932864896760309593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128617207288576597840206395 192925810932864896760309593)
      ·
        refine ⟨144694358199648672570232195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192925810932864896760309593 144694358199648672570232195)
        ·
          refine ⟨217041537299473008855348293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144694358199648672570232195 217041537299473008855348293)
          ·
            refine ⟨40695288243651189160377805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217041537299473008855348293 40695288243651189160377805)
            ·
              refine ⟨15260733091369195935141677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40695288243651189160377805 15260733091369195935141677)
              ·
                refine ⟨5722774909263448475678129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15260733091369195935141677 5722774909263448475678129)
                ·
                  refine ⟨4292081181947586356758597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5722774909263448475678129 4292081181947586356758597)
                  ·
                    refine ⟨804765221615172441892237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4292081181947586356758597 804765221615172441892237)
                    ·
                      rfl

theorem cell23_4701824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_4701824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701824 prefixEnd_4701824 := by exact prefixLift 4701824
  have htrace : WordTrace (prefixWord ++ tailWord_4701824) baseStart_4701824 baseEnd_4701824 := by
    simpa [prefixWord, tailWord_4701824, baseEnd_4701824] using wordTrace_append hprefix tailTrace_4701824
  have hstable : (prefixWord ++ tailWord_4701824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701824).length < 2 ^ (prefixWord ++ tailWord_4701824).sum := by decide
  have hdescent : baseEnd_4701824 < baseStart_4701824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701827 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4]
def baseStart_4701827 : Nat := 118140960795 + 4701827 * 2 ^ 59
def prefixEnd_4701827 : Nat := 4983230072969 + 3 ^ 40 * 4701827 * 2
def baseEnd_4701827 : Nat := 2414297205287480813939197

theorem tailTrace_4701827 : CollatzResearch.WordTrace tailWord_4701827 prefixEnd_4701827 2414297205287480813939197 := by
  unfold tailWord_4701827
  simp only [CollatzResearch.WordTrace]
  refine ⟨171489719137091261965967735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114326479424727507977311823 171489719137091261965967735)
  ·
    refine ⟨257234578705636892948951603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171489719137091261965967735 257234578705636892948951603)
    ·
      refine ⟨385851868058455339423427405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257234578705636892948951603 385851868058455339423427405)
      ·
        refine ⟨144694450521920752283785277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385851868058455339423427405 144694450521920752283785277)
        ·
          refine ⟨54260418945720282106419479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144694450521920752283785277 54260418945720282106419479)
          ·
            refine ⟨81390628418580423159629219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54260418945720282106419479 81390628418580423159629219)
            ·
              refine ⟨122085942627870634739443829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81390628418580423159629219 122085942627870634739443829)
              ·
                refine ⟨11445557121362872006822859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122085942627870634739443829 11445557121362872006822859)
                ·
                  refine ⟨17168335682044308010234289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11445557121362872006822859 17168335682044308010234289)
                  ·
                    refine ⟨12876251761533231007675717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17168335682044308010234289 12876251761533231007675717)
                    ·
                      refine ⟨2414297205287480813939197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12876251761533231007675717 2414297205287480813939197)
                      ·
                        rfl

theorem cell23_4701827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_4701827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701827 prefixEnd_4701827 := by exact prefixLift 4701827
  have htrace : WordTrace (prefixWord ++ tailWord_4701827) baseStart_4701827 baseEnd_4701827 := by
    simpa [prefixWord, tailWord_4701827, baseEnd_4701827] using wordTrace_append hprefix tailTrace_4701827
  have hstable : (prefixWord ++ tailWord_4701827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701827).length < 2 ^ (prefixWord ++ tailWord_4701827).sum := by decide
  have hdescent : baseEnd_4701827 < baseStart_4701827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701828 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_4701828 : Nat := 118140960795 + 4701828 * 2 ^ 59
def prefixEnd_4701828 : Nat := 4983230072969 + 3 ^ 40 * 4701828 * 2
def baseEnd_4701828 : Nat := 804765906256045103342231

theorem tailTrace_4701828 : CollatzResearch.WordTrace tailWord_4701828 prefixEnd_4701828 804765906256045103342231 := by
  unfold tailWord_4701828
  simp only [CollatzResearch.WordTrace]
  refine ⟨85744877805043819568377069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114326503740058426091169425 85744877805043819568377069)
  ·
    refine ⟨32154329176891432338141401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85744877805043819568377069 32154329176891432338141401)
    ·
      refine ⟨24115746882668574253606051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32154329176891432338141401 24115746882668574253606051)
      ·
        refine ⟨36173620324002861380409077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24115746882668574253606051 36173620324002861380409077)
        ·
          refine ⟨3391276905375268254413351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36173620324002861380409077 3391276905375268254413351)
          ·
            refine ⟨5086915358062902381620027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391276905375268254413351 5086915358062902381620027)
            ·
              refine ⟨7630373037094353572430041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086915358062902381620027 7630373037094353572430041)
              ·
                refine ⟨5722779777820765179322531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7630373037094353572430041 5722779777820765179322531)
                ·
                  refine ⟨8584169666731147768983797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5722779777820765179322531 8584169666731147768983797)
                  ·
                    refine ⟨804765906256045103342231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8584169666731147768983797 804765906256045103342231)
                    ·
                      rfl

theorem cell23_4701828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_4701828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701828 prefixEnd_4701828 := by exact prefixLift 4701828
  have htrace : WordTrace (prefixWord ++ tailWord_4701828) baseStart_4701828 baseEnd_4701828 := by
    simpa [prefixWord, tailWord_4701828, baseEnd_4701828] using wordTrace_append hprefix tailTrace_4701828
  have hstable : (prefixWord ++ tailWord_4701828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701828).length < 2 ^ (prefixWord ++ tailWord_4701828).sum := by decide
  have hdescent : baseEnd_4701828 < baseStart_4701828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701831 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_4701831 : Nat := 118140960795 + 4701831 * 2 ^ 59
def prefixEnd_4701831 : Nat := 4983230072969 + 3 ^ 40 * 4701831 * 2
def baseEnd_4701831 : Nat := 2414299259210098798289179

theorem tailTrace_4701831 : CollatzResearch.WordTrace tailWord_4701831 prefixEnd_4701831 2414299259210098798289179 := by
  unfold tailWord_4701831
  simp only [CollatzResearch.WordTrace]
  refine ⟨171489865029076770649113347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114326576686051180432742231 171489865029076770649113347)
  ·
    refine ⟨257234797543615155973670021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171489865029076770649113347 257234797543615155973670021)
    ·
      refine ⟨48231524539427841745063129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257234797543615155973670021 48231524539427841745063129)
      ·
        refine ⟨36173643404570881308797347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48231524539427841745063129 36173643404570881308797347)
        ·
          refine ⟨54260465106856321963196021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36173643404570881308797347 54260465106856321963196021)
          ·
            refine ⟨5086918603767780184049627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54260465106856321963196021 5086918603767780184049627)
            ·
              refine ⟨7630377905651670276074441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086918603767780184049627 7630377905651670276074441)
              ·
                refine ⟨5722783429238752707055831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7630377905651670276074441 5722783429238752707055831)
                ·
                  refine ⟨8584175143858129060583747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5722783429238752707055831 8584175143858129060583747)
                  ·
                    refine ⟨12876262715787193590875621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8584175143858129060583747 12876262715787193590875621)
                    ·
                      refine ⟨2414299259210098798289179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12876262715787193590875621 2414299259210098798289179)
                      ·
                        rfl

theorem cell23_4701831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_4701831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701831 prefixEnd_4701831 := by exact prefixLift 4701831
  have htrace : WordTrace (prefixWord ++ tailWord_4701831) baseStart_4701831 baseEnd_4701831 := by
    simpa [prefixWord, tailWord_4701831, baseEnd_4701831] using wordTrace_append hprefix tailTrace_4701831
  have hstable : (prefixWord ++ tailWord_4701831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701831).length < 2 ^ (prefixWord ++ tailWord_4701831).sum := by decide
  have hdescent : baseEnd_4701831 < baseStart_4701831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701878 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4701878 : Nat := 118140960795 + 4701878 * 2 ^ 59
def prefixEnd_4701878 : Nat := 4983230072969 + 3 ^ 40 * 4701878 * 2
def baseEnd_4701878 : Nat := 2414323392800860114401463

theorem tailTrace_4701878 : CollatzResearch.WordTrace tailWord_4701878 prefixEnd_4701878 2414323392800860114401463 := by
  unfold tailWord_4701878
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718223703744156104754643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114327719506604331784049525 10718223703744156104754643)
  ·
    refine ⟨16077335555616234157131965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10718223703744156104754643 16077335555616234157131965)
    ·
      refine ⟨6029000833356087808924487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16077335555616234157131965 6029000833356087808924487)
      ·
        refine ⟨9043501250034131713386731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6029000833356087808924487 9043501250034131713386731)
        ·
          refine ⟨13565251875051197570080097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9043501250034131713386731 13565251875051197570080097)
          ·
            refine ⟨10173938906288398177560073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13565251875051197570080097 10173938906288398177560073)
            ·
              refine ⟨7630454179716298633170055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10173938906288398177560073 7630454179716298633170055)
              ·
                refine ⟨11445681269574447949755083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7630454179716298633170055 11445681269574447949755083)
                ·
                  refine ⟨17168521904361671924632625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11445681269574447949755083 17168521904361671924632625)
                  ·
                    refine ⟨12876391428271253943474469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17168521904361671924632625 12876391428271253943474469)
                    ·
                      refine ⟨2414323392800860114401463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12876391428271253943474469 2414323392800860114401463)
                      ·
                        rfl

theorem cell23_4701878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4701878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701878 prefixEnd_4701878 := by exact prefixLift 4701878
  have htrace : WordTrace (prefixWord ++ tailWord_4701878) baseStart_4701878 baseEnd_4701878 := by
    simpa [prefixWord, tailWord_4701878, baseEnd_4701878] using wordTrace_append hprefix tailTrace_4701878
  have hstable : (prefixWord ++ tailWord_4701878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701878).length < 2 ^ (prefixWord ++ tailWord_4701878).sum := by decide
  have hdescent : baseEnd_4701878 < baseStart_4701878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701881 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4701881 : Nat := 118140960795 + 4701881 * 2 ^ 59
def prefixEnd_4701881 : Nat := 4983230072969 + 3 ^ 40 * 4701881 * 2
def baseEnd_4701881 : Nat := 2414324933242823602663949

theorem tailTrace_4701881 : CollatzResearch.WordTrace tailWord_4701881 prefixEnd_4701881 2414324933242823602663949 := by
  unfold tailWord_4701881
  simp only [CollatzResearch.WordTrace]
  refine ⟨171491688678895629188433497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114327792452597086125622331 171491688678895629188433497)
  ·
    refine ⟨128618766509171721891325123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171491688678895629188433497 128618766509171721891325123)
    ·
      refine ⟨192928149763757582836987685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128618766509171721891325123 192928149763757582836987685)
      ·
        refine ⟨36174028080704546781935191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192928149763757582836987685 36174028080704546781935191)
        ·
          refine ⟨54261042121056820172902787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36174028080704546781935191 54261042121056820172902787)
          ·
            refine ⟨81391563181585230259354181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54261042121056820172902787 81391563181585230259354181)
            ·
              refine ⟨15260918096547230673628909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81391563181585230259354181 15260918096547230673628909)
              ·
                refine ⟨5722844286205211502610841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15260918096547230673628909 5722844286205211502610841)
                ·
                  refine ⟨4292133214653908626958131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5722844286205211502610841 4292133214653908626958131)
                  ·
                    refine ⟨6438199821980862940437197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4292133214653908626958131 6438199821980862940437197)
                    ·
                      refine ⟨2414324933242823602663949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6438199821980862940437197 2414324933242823602663949)
                      ·
                        rfl

theorem cell23_4701881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4701881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701881 prefixEnd_4701881 := by exact prefixLift 4701881
  have htrace : WordTrace (prefixWord ++ tailWord_4701881) baseStart_4701881 baseEnd_4701881 := by
    simpa [prefixWord, tailWord_4701881, baseEnd_4701881] using wordTrace_append hprefix tailTrace_4701881
  have hstable : (prefixWord ++ tailWord_4701881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701881).length < 2 ^ (prefixWord ++ tailWord_4701881).sum := by decide
  have hdescent : baseEnd_4701881 < baseStart_4701881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701887 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_4701887 : Nat := 118140960795 + 4701887 * 2 ^ 59
def prefixEnd_4701887 : Nat := 4983230072969 + 3 ^ 40 * 4701887 * 2
def baseEnd_4701887 : Nat := 2414328014126750579188921

theorem tailTrace_4701887 : CollatzResearch.WordTrace tailWord_4701887 prefixEnd_4701887 2414328014126750579188921 := by
  unfold tailWord_4701887
  simp only [CollatzResearch.WordTrace]
  refine ⟨171491907516873892213151915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114327938344582594808767943 171491907516873892213151915)
  ·
    refine ⟨257237861275310838319727873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171491907516873892213151915 257237861275310838319727873)
    ·
      refine ⟨192928395956483128739795905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257237861275310838319727873 192928395956483128739795905)
      ·
        refine ⟨144696296967362346554846929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192928395956483128739795905 144696296967362346554846929)
        ·
          refine ⟨108522222725521759916135197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144696296967362346554846929 108522222725521759916135197)
          ·
            refine ⟨40695833522070659968550699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108522222725521759916135197 40695833522070659968550699)
            ·
              refine ⟨61043750283105989952826049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40695833522070659968550699 61043750283105989952826049)
              ·
                refine ⟨45782812712329492464619537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61043750283105989952826049 45782812712329492464619537)
                ·
                  refine ⟨34337109534247119348464653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45782812712329492464619537 34337109534247119348464653)
                  ·
                    refine ⟨12876416075342669755674245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34337109534247119348464653 12876416075342669755674245)
                    ·
                      refine ⟨2414328014126750579188921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12876416075342669755674245 2414328014126750579188921)
                      ·
                        rfl

theorem cell23_4701887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_4701887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701887 prefixEnd_4701887 := by exact prefixLift 4701887
  have htrace : WordTrace (prefixWord ++ tailWord_4701887) baseStart_4701887 baseEnd_4701887 := by
    simpa [prefixWord, tailWord_4701887, baseEnd_4701887] using wordTrace_append hprefix tailTrace_4701887
  have hstable : (prefixWord ++ tailWord_4701887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701887).length < 2 ^ (prefixWord ++ tailWord_4701887).sum := by decide
  have hdescent : baseEnd_4701887 < baseStart_4701887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701904 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 3, 4, 2]
def baseStart_4701904 : Nat := 118140960795 + 4701904 * 2 ^ 59
def prefixEnd_4701904 : Nat := 4983230072969 + 3 ^ 40 * 4701904 * 2
def baseEnd_4701904 : Nat := 2414336743297877012676343

theorem tailTrace_4701904 : CollatzResearch.WordTrace tailWord_4701904 prefixEnd_4701904 2414336743297877012676343 := by
  unfold tailWord_4701904
  simp only [CollatzResearch.WordTrace]
  refine ⟨85746263778906152058260383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114328351705208202744347177 85746263778906152058260383)
  ·
    refine ⟨128619395668359228087390575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85746263778906152058260383 128619395668359228087390575)
    ·
      refine ⟨192929093502538842131085863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128619395668359228087390575 192929093502538842131085863)
      ·
        refine ⟨289393640253808263196628795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192929093502538842131085863 289393640253808263196628795)
        ·
          refine ⟨434090460380712394794943193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289393640253808263196628795 434090460380712394794943193)
          ·
            refine ⟨325567845285534296096207395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434090460380712394794943193 325567845285534296096207395)
            ·
              refine ⟨488351767928301444144311093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325567845285534296096207395 488351767928301444144311093)
              ·
                refine ⟨45782978243278260388529165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488351767928301444144311093 45782978243278260388529165)
                ·
                  refine ⟨17168616841229347645698437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45782978243278260388529165 17168616841229347645698437)
                  ·
                    refine ⟨3219115657730502683568457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17168616841229347645698437 3219115657730502683568457)
                    ·
                      refine ⟨2414336743297877012676343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219115657730502683568457 2414336743297877012676343)
                      ·
                        rfl

theorem cell23_4701904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 4, 2].length) (baseStart_4701904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701904 prefixEnd_4701904 := by exact prefixLift 4701904
  have htrace : WordTrace (prefixWord ++ tailWord_4701904) baseStart_4701904 baseEnd_4701904 := by
    simpa [prefixWord, tailWord_4701904, baseEnd_4701904] using wordTrace_append hprefix tailTrace_4701904
  have hstable : (prefixWord ++ tailWord_4701904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701904).length < 2 ^ (prefixWord ++ tailWord_4701904).sum := by decide
  have hdescent : baseEnd_4701904 < baseStart_4701904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701934 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_4701934 : Nat := 118140960795 + 4701934 * 2 ^ 59
def prefixEnd_4701934 : Nat := 4983230072969 + 3 ^ 40 * 4701934 * 2
def baseEnd_4701934 : Nat := 2414352147717511895301205

theorem tailTrace_4701934 : CollatzResearch.WordTrace tailWord_4701934 prefixEnd_4701934 2414352147717511895301205 := by
  unfold tailWord_4701934
  simp only [CollatzResearch.WordTrace]
  refine ⟨21436702718462952405014107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114329081165135746160075237 21436702718462952405014107)
  ·
    refine ⟨32155054077694428607521161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21436702718462952405014107 32155054077694428607521161)
    ·
      refine ⟨24116290558270821455640871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32155054077694428607521161 24116290558270821455640871)
      ·
        refine ⟨36174435837406232183461307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24116290558270821455640871 36174435837406232183461307)
        ·
          refine ⟨54261653756109348275191961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36174435837406232183461307 54261653756109348275191961)
          ·
            refine ⟨40696240317082011206393971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54261653756109348275191961 40696240317082011206393971)
            ·
              refine ⟨61044360475623016809590957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40696240317082011206393971 61044360475623016809590957)
              ·
                refine ⟨22891635178358631303596609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61044360475623016809590957 22891635178358631303596609)
                ·
                  refine ⟨17168726383768973477697457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22891635178358631303596609 17168726383768973477697457)
                  ·
                    refine ⟨12876544787826730108273093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17168726383768973477697457 12876544787826730108273093)
                    ·
                      refine ⟨2414352147717511895301205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12876544787826730108273093 2414352147717511895301205)
                      ·
                        rfl

theorem cell23_4701934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_4701934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701934 prefixEnd_4701934 := by exact prefixLift 4701934
  have htrace : WordTrace (prefixWord ++ tailWord_4701934) baseStart_4701934 baseEnd_4701934 := by
    simpa [prefixWord, tailWord_4701934, baseEnd_4701934] using wordTrace_append hprefix tailTrace_4701934
  have hstable : (prefixWord ++ tailWord_4701934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701934).length < 2 ^ (prefixWord ++ tailWord_4701934).sum := by decide
  have hdescent : baseEnd_4701934 < baseStart_4701934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701978 : List Nat := [3, 1, 1, 3, 2, 3, 3, 2, 5]
def baseStart_4701978 : Nat := 118140960795 + 4701978 * 2 ^ 59
def prefixEnd_4701978 : Nat := 4983230072969 + 3 ^ 40 * 4701978 * 2
def baseEnd_4701978 : Nat := 268263860096256635905667

theorem tailTrace_4701978 : CollatzResearch.WordTrace tailWord_4701978 prefixEnd_4701978 268263860096256635905667 := by
  unfold tailWord_4701978
  simp only [CollatzResearch.WordTrace]
  refine ⟨42873806639886053688678647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114330151039696143169809725 42873806639886053688678647)
  ·
    refine ⟨64310709959829080533017971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42873806639886053688678647 64310709959829080533017971)
    ·
      refine ⟨96466064939743620799526957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64310709959829080533017971 96466064939743620799526957)
      ·
        refine ⟨36174774352403857799822609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96466064939743620799526957 36174774352403857799822609)
        ·
          refine ⟨27131080764302893349866957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36174774352403857799822609 27131080764302893349866957)
          ·
            refine ⟨10174155286613585006200109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27131080764302893349866957 10174155286613585006200109)
            ·
              refine ⟨3815308232480094377325041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10174155286613585006200109 3815308232480094377325041)
              ·
                refine ⟨2861481174360070782993781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3815308232480094377325041 2861481174360070782993781)
                ·
                  refine ⟨268263860096256635905667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2861481174360070782993781 268263860096256635905667)
                  ·
                    rfl

theorem cell23_4701978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_4701978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701978 prefixEnd_4701978 := by exact prefixLift 4701978
  have htrace : WordTrace (prefixWord ++ tailWord_4701978) baseStart_4701978 baseEnd_4701978 := by
    simpa [prefixWord, tailWord_4701978, baseEnd_4701978] using wordTrace_append hprefix tailTrace_4701978
  have hstable : (prefixWord ++ tailWord_4701978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701978).length < 2 ^ (prefixWord ++ tailWord_4701978).sum := by decide
  have hdescent : baseEnd_4701978 < baseStart_4701978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701984 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4701984 : Nat := 118140960795 + 4701984 * 2 ^ 59
def prefixEnd_4701984 : Nat := 4983230072969 + 3 ^ 40 * 4701984 * 2
def baseEnd_4701984 : Nat := 2414377821750236699675975

theorem tailTrace_4701984 : CollatzResearch.WordTrace tailWord_4701984 prefixEnd_4701984 2414377821750236699675975 := by
  unfold tailWord_4701984
  simp only [CollatzResearch.WordTrace]
  refine ⟨85747722698761238889716503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114330296931681651852955337 85747722698761238889716503)
  ·
    refine ⟨128621584048141858334574755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85747722698761238889716503 128621584048141858334574755)
    ·
      refine ⟨192932376072212787501862133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128621584048141858334574755 192932376072212787501862133)
      ·
        refine ⟨18087410256769948828299575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192932376072212787501862133 18087410256769948828299575)
        ·
          refine ⟨27131115385154923242449363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18087410256769948828299575 27131115385154923242449363)
          ·
            refine ⟨40696673077732384863674045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27131115385154923242449363 40696673077732384863674045)
            ·
              refine ⟨15261252404149644323877767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40696673077732384863674045 15261252404149644323877767)
              ·
                refine ⟨22891878606224466485816651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15261252404149644323877767 22891878606224466485816651)
                ·
                  refine ⟨34337817909336699728724977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22891878606224466485816651 34337817909336699728724977)
                  ·
                    refine ⟨25753363432002524796543733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34337817909336699728724977 25753363432002524796543733)
                    ·
                      refine ⟨2414377821750236699675975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25753363432002524796543733 2414377821750236699675975)
                      ·
                        rfl

theorem cell23_4701984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4701984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701984 prefixEnd_4701984 := by exact prefixLift 4701984
  have htrace : WordTrace (prefixWord ++ tailWord_4701984) baseStart_4701984 baseEnd_4701984 := by
    simpa [prefixWord, tailWord_4701984, baseEnd_4701984] using wordTrace_append hprefix tailTrace_4701984
  have hstable : (prefixWord ++ tailWord_4701984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701984).length < 2 ^ (prefixWord ++ tailWord_4701984).sum := by decide
  have hdescent : baseEnd_4701984 < baseStart_4701984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702141 : List Nat := [1, 4, 1, 2, 3, 3, 9]
def baseStart_4702141 : Nat := 118140960795 + 4702141 * 2 ^ 59
def prefixEnd_4702141 : Nat := 4983230072969 + 3 ^ 40 * 4702141 * 2
def baseEnd_4702141 : Nat := 29808128866827068955713

theorem tailTrace_4702141 : CollatzResearch.WordTrace tailWord_4702141 prefixEnd_4702141 29808128866827068955713 := by
  unfold tailWord_4702141
  simp only [CollatzResearch.WordTrace]
  refine ⟨171501171657953693592898277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114334114438635795728598851 171501171657953693592898277)
  ·
    refine ⟨32156469685866317548668427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171501171657953693592898277 32156469685866317548668427)
    ·
      refine ⟨48234704528799476323002641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32156469685866317548668427 48234704528799476323002641)
      ·
        refine ⟨36176028396599607242251981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48234704528799476323002641 36176028396599607242251981)
        ·
          refine ⟨13566010648724852715844493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36176028396599607242251981 13566010648724852715844493)
          ·
            refine ⟨5087253993271819768441685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13566010648724852715844493 5087253993271819768441685)
            ·
              refine ⟨29808128866827068955713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5087253993271819768441685 29808128866827068955713)
              ·
                rfl

theorem cell23_4702141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 9].length) (baseStart_4702141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702141 prefixEnd_4702141 := by exact prefixLift 4702141
  have htrace : WordTrace (prefixWord ++ tailWord_4702141) baseStart_4702141 baseEnd_4702141 := by
    simpa [prefixWord, tailWord_4702141, baseEnd_4702141] using wordTrace_append hprefix tailTrace_4702141
  have hstable : (prefixWord ++ tailWord_4702141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702141).length < 2 ^ (prefixWord ++ tailWord_4702141).sum := by decide
  have hdescent : baseEnd_4702141 < baseStart_4702141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702152 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_4702152 : Nat := 118140960795 + 4702152 * 2 ^ 59
def prefixEnd_4702152 : Nat := 4983230072969 + 3 ^ 40 * 4702152 * 2
def baseEnd_4702152 : Nat := 2414464086500192042375203

theorem tailTrace_4702152 : CollatzResearch.WordTrace tailWord_4702152 prefixEnd_4702152 2414464086500192042375203 := by
  unfold tailWord_4702152
  simp only [CollatzResearch.WordTrace]
  refine ⟨85750786430456921235774355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114334381907275894981032473 85750786430456921235774355)
  ·
    refine ⟨128626179645685381853661533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85750786430456921235774355 128626179645685381853661533)
    ·
      refine ⟨48234817367132018195123075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128626179645685381853661533 48234817367132018195123075)
      ·
        refine ⟨72352226050698027292684613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48234817367132018195123075 72352226050698027292684613)
        ·
          refine ⟨13566042384505880117378365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72352226050698027292684613 13566042384505880117378365)
          ·
            refine ⟨5087265894189705044016887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13566042384505880117378365 5087265894189705044016887)
            ·
              refine ⟨7630898841284557566025331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5087265894189705044016887 7630898841284557566025331)
              ·
                refine ⟨11446348261926836349037997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7630898841284557566025331 11446348261926836349037997)
                ·
                  refine ⟨4292380598222563630889249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11446348261926836349037997 4292380598222563630889249)
                  ·
                    refine ⟨3219285448666922723166937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292380598222563630889249 3219285448666922723166937)
                    ·
                      refine ⟨2414464086500192042375203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219285448666922723166937 2414464086500192042375203)
                      ·
                        rfl

theorem cell23_4702152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_4702152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702152 prefixEnd_4702152 := by exact prefixLift 4702152
  have htrace : WordTrace (prefixWord ++ tailWord_4702152) baseStart_4702152 baseEnd_4702152 := by
    simpa [prefixWord, tailWord_4702152, baseEnd_4702152] using wordTrace_append hprefix tailTrace_4702152
  have hstable : (prefixWord ++ tailWord_4702152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702152).length < 2 ^ (prefixWord ++ tailWord_4702152).sum := by decide
  have hdescent : baseEnd_4702152 < baseStart_4702152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702189 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4702189 : Nat := 118140960795 + 4702189 * 2 ^ 59
def prefixEnd_4702189 : Nat := 4983230072969 + 3 ^ 40 * 4702189 * 2
def baseEnd_4702189 : Nat := 2414483085284408397612533

theorem tailTrace_4702189 : CollatzResearch.WordTrace tailWord_4702189 prefixEnd_4702189 2414483085284408397612533 := by
  unfold tailWord_4702189
  simp only [CollatzResearch.WordTrace]
  refine ⟨171502922361779797790645621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114335281574519865193763747 171502922361779797790645621)
  ·
    refine ⟨16078398971416856042873027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171502922361779797790645621 16078398971416856042873027)
    ·
      refine ⟨24117598457125284064309541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16078398971416856042873027 24117598457125284064309541)
      ·
        refine ⟨4522049710710990762058039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24117598457125284064309541 4522049710710990762058039)
        ·
          refine ⟨6783074566066486143087059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522049710710990762058039 6783074566066486143087059)
          ·
            refine ⟨10174611849099729214630589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6783074566066486143087059 10174611849099729214630589)
            ·
              refine ⟨3815479443412398455486471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10174611849099729214630589 3815479443412398455486471)
              ·
                refine ⟨5723219165118597683229707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815479443412398455486471 5723219165118597683229707)
                ·
                  refine ⟨8584828747677896524844561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5723219165118597683229707 8584828747677896524844561)
                  ·
                    refine ⟨6438621560758422393633421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8584828747677896524844561 6438621560758422393633421)
                    ·
                      refine ⟨2414483085284408397612533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6438621560758422393633421 2414483085284408397612533)
                      ·
                        rfl

theorem cell23_4702189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4702189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702189 prefixEnd_4702189 := by exact prefixLift 4702189
  have htrace : WordTrace (prefixWord ++ tailWord_4702189) baseStart_4702189 baseEnd_4702189 := by
    simpa [prefixWord, tailWord_4702189, baseEnd_4702189] using wordTrace_append hprefix tailTrace_4702189
  have hstable : (prefixWord ++ tailWord_4702189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702189).length < 2 ^ (prefixWord ++ tailWord_4702189).sum := by decide
  have hdescent : baseEnd_4702189 < baseStart_4702189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702218 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_4702218 : Nat := 118140960795 + 4702218 * 2 ^ 59
def prefixEnd_4702218 : Nat := 4983230072969 + 3 ^ 40 * 4702218 * 2
def baseEnd_4702218 : Nat := 804832658741129594716633

theorem tailTrace_4702218 : CollatzResearch.WordTrace tailWord_4702218 prefixEnd_4702218 804832658741129594716633 := by
  unfold tailWord_4702218
  simp only [CollatzResearch.WordTrace]
  refine ⟨42875995019668683935862827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114335986719116490495634205 42875995019668683935862827)
  ·
    refine ⟨64313992529503025903794241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42875995019668683935862827 64313992529503025903794241)
    ·
      refine ⟨48235494397127269427845681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64313992529503025903794241 48235494397127269427845681)
      ·
        refine ⟨36176620797845452070884261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48235494397127269427845681 36176620797845452070884261)
        ·
          refine ⟨6783116399596022263290799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36176620797845452070884261 6783116399596022263290799)
          ·
            refine ⟨10174674599394033394936199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6783116399596022263290799 10174674599394033394936199)
            ·
              refine ⟨15262011899091050092404299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10174674599394033394936199 15262011899091050092404299)
              ·
                refine ⟨22893017848636575138606449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15262011899091050092404299 22893017848636575138606449)
                ·
                  refine ⟨17169763386477431353954837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22893017848636575138606449 17169763386477431353954837)
                  ·
                    refine ⟨804832658741129594716633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17169763386477431353954837 804832658741129594716633)
                    ·
                      rfl

theorem cell23_4702218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_4702218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702218 prefixEnd_4702218 := by exact prefixLift 4702218
  have htrace : WordTrace (prefixWord ++ tailWord_4702218) baseStart_4702218 baseEnd_4702218 := by
    simpa [prefixWord, tailWord_4702218, baseEnd_4702218] using wordTrace_append hprefix tailTrace_4702218
  have hstable : (prefixWord ++ tailWord_4702218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702218).length < 2 ^ (prefixWord ++ tailWord_4702218).sum := by decide
  have hdescent : baseEnd_4702218 < baseStart_4702218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702258 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_4702258 : Nat := 118140960795 + 4702258 * 2 ^ 59
def prefixEnd_4702258 : Nat := 4983230072969 + 3 ^ 40 * 4702258 * 2
def baseEnd_4702258 : Nat := 2414518515449568627649715

theorem tailTrace_4702258 : CollatzResearch.WordTrace tailWord_4702258 prefixEnd_4702258 2414518515449568627649715 := by
  unfold tailWord_4702258
  simp only [CollatzResearch.WordTrace]
  refine ⟨42876359749632455643726857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114336959332353215049938285 42876359749632455643726857)
  ·
    refine ⟨32157269812224341732795143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42876359749632455643726857 32157269812224341732795143)
    ·
      refine ⟨48235904718336512599192715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32157269812224341732795143 48235904718336512599192715)
      ·
        refine ⟨72353857077504768898789073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48235904718336512599192715 72353857077504768898789073)
        ·
          refine ⟨54265392808128576674091805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72353857077504768898789073 54265392808128576674091805)
          ·
            refine ⟨20349522303048216252784427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54265392808128576674091805 20349522303048216252784427)
            ·
              refine ⟨30524283454572324379176641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20349522303048216252784427 30524283454572324379176641)
              ·
                refine ⟨22893212590929243284382481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30524283454572324379176641 22893212590929243284382481)
                ·
                  refine ⟨17169909443196932463286861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22893212590929243284382481 17169909443196932463286861)
                  ·
                    refine ⟨6438716041198849673732573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17169909443196932463286861 6438716041198849673732573)
                    ·
                      refine ⟨2414518515449568627649715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6438716041198849673732573 2414518515449568627649715)
                      ·
                        rfl

theorem cell23_4702258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_4702258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702258 prefixEnd_4702258 := by exact prefixLift 4702258
  have htrace : WordTrace (prefixWord ++ tailWord_4702258) baseStart_4702258 baseEnd_4702258 := by
    simpa [prefixWord, tailWord_4702258, baseEnd_4702258] using wordTrace_append hprefix tailTrace_4702258
  have hstable : (prefixWord ++ tailWord_4702258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702258).length < 2 ^ (prefixWord ++ tailWord_4702258).sum := by decide
  have hdescent : baseEnd_4702258 < baseStart_4702258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702271 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_4702271 : Nat := 118140960795 + 4702271 * 2 ^ 59
def prefixEnd_4702271 : Nat := 4983230072969 + 3 ^ 40 * 4702271 * 2
def baseEnd_4702271 : Nat := 2414525190698077076787155

theorem tailTrace_4702271 : CollatzResearch.WordTrace tailWord_4702271 prefixEnd_4702271 2414525190698077076787155 := by
  unfold tailWord_4702271
  simp only [CollatzResearch.WordTrace]
  refine ⟨171505913147482725795130667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114337275431655150530087111 171505913147482725795130667)
  ·
    refine ⟨257258869721224088692696001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171505913147482725795130667 257258869721224088692696001)
    ·
      refine ⟨192944152290918066519522001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257258869721224088692696001 192944152290918066519522001)
      ·
        refine ⟨144708114218188549889641501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192944152290918066519522001 144708114218188549889641501)
        ·
          refine ⟨54265542831820706208615563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144708114218188549889641501 54265542831820706208615563)
          ·
            refine ⟨81398314247731059312923345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54265542831820706208615563 81398314247731059312923345)
            ·
              refine ⟨61048735685798294484692509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81398314247731059312923345 61048735685798294484692509)
              ·
                refine ⟨22893275882174360431759691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61048735685798294484692509 22893275882174360431759691)
                ·
                  refine ⟨34339913823261540647639537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22893275882174360431759691 34339913823261540647639537)
                  ·
                    refine ⟨25754935367446155485729653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34339913823261540647639537 25754935367446155485729653)
                    ·
                      refine ⟨2414525190698077076787155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25754935367446155485729653 2414525190698077076787155)
                      ·
                        rfl

theorem cell23_4702271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_4702271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702271 prefixEnd_4702271 := by exact prefixLift 4702271
  have htrace : WordTrace (prefixWord ++ tailWord_4702271) baseStart_4702271 baseEnd_4702271 := by
    simpa [prefixWord, tailWord_4702271, baseEnd_4702271] using wordTrace_append hprefix tailTrace_4702271
  have hstable : (prefixWord ++ tailWord_4702271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702271).length < 2 ^ (prefixWord ++ tailWord_4702271).sum := by decide
  have hdescent : baseEnd_4702271 < baseStart_4702271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702281 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_4702281 : Nat := 118140960795 + 4702281 * 2 ^ 59
def prefixEnd_4702281 : Nat := 4983230072969 + 3 ^ 40 * 4702281 * 2
def baseEnd_4702281 : Nat := 2414530325504622037662109

theorem tailTrace_4702281 : CollatzResearch.WordTrace tailWord_4702281 prefixEnd_4702281 2414530325504622037662109 := by
  unfold tailWord_4702281
  simp only [CollatzResearch.WordTrace]
  refine ⟨171506277877446497502994697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114337518584964331668663131 171506277877446497502994697)
  ·
    refine ⟨128629708408084873127246023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171506277877446497502994697 128629708408084873127246023)
    ·
      refine ⟨192944562612127309690869035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128629708408084873127246023 192944562612127309690869035)
      ·
        refine ⟨289416843918190964536303553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192944562612127309690869035 289416843918190964536303553)
        ·
          refine ⟨217062632938643223402227665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289416843918190964536303553 217062632938643223402227665)
          ·
            refine ⟨162796974703982417551670749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217062632938643223402227665 162796974703982417551670749)
            ·
              refine ⟨61048865513993406581876531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162796974703982417551670749 61048865513993406581876531)
              ·
                refine ⟨91573298270990109872814797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61048865513993406581876531 91573298270990109872814797)
                ·
                  refine ⟨34339986851621291202305549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91573298270990109872814797 34339986851621291202305549)
                  ·
                    refine ⟨12877495069357984200864581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34339986851621291202305549 12877495069357984200864581)
                    ·
                      refine ⟨2414530325504622037662109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12877495069357984200864581 2414530325504622037662109)
                      ·
                        rfl

theorem cell23_4702281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_4702281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702281 prefixEnd_4702281 := by exact prefixLift 4702281
  have htrace : WordTrace (prefixWord ++ tailWord_4702281) baseStart_4702281 baseEnd_4702281 := by
    simpa [prefixWord, tailWord_4702281, baseEnd_4702281] using wordTrace_append hprefix tailTrace_4702281
  have hstable : (prefixWord ++ tailWord_4702281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702281).length < 2 ^ (prefixWord ++ tailWord_4702281).sum := by decide
  have hdescent : baseEnd_4702281 < baseStart_4702281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702298 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_4702298 : Nat := 118140960795 + 4702298 * 2 ^ 59
def prefixEnd_4702298 : Nat := 4983230072969 + 3 ^ 40 * 4702298 * 2
def baseEnd_4702298 : Nat := 2414539054675748471149531

theorem tailTrace_4702298 : CollatzResearch.WordTrace tailWord_4702298 prefixEnd_4702298 2414539054675748471149531 := by
  unfold tailWord_4702298
  simp only [CollatzResearch.WordTrace]
  refine ⟨42876724479596227351590887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114337931945589939604242365 42876724479596227351590887)
  ·
    refine ⟨64315086719394341027386331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42876724479596227351590887 64315086719394341027386331)
    ·
      refine ⟨96472630079091511541079497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64315086719394341027386331 96472630079091511541079497)
      ·
        refine ⟨72354472559318633655809623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96472630079091511541079497 72354472559318633655809623)
        ·
          refine ⟨108531708838977950483714435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72354472559318633655809623 108531708838977950483714435)
          ·
            refine ⟨162797563258466925725571653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108531708838977950483714435 162797563258466925725571653)
            ·
              refine ⟨30524543110962548573544685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162797563258466925725571653 30524543110962548573544685)
              ·
                refine ⟨11446703666610955715079257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30524543110962548573544685 11446703666610955715079257)
                ·
                  refine ⟨8585027749958216786309443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11446703666610955715079257 8585027749958216786309443)
                  ·
                    refine ⟨12877541624937325179464165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8585027749958216786309443 12877541624937325179464165)
                    ·
                      refine ⟨2414539054675748471149531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12877541624937325179464165 2414539054675748471149531)
                      ·
                        rfl

theorem cell23_4702298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_4702298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702298 prefixEnd_4702298 := by exact prefixLift 4702298
  have htrace : WordTrace (prefixWord ++ tailWord_4702298) baseStart_4702298 baseEnd_4702298 := by
    simpa [prefixWord, tailWord_4702298, baseEnd_4702298] using wordTrace_append hprefix tailTrace_4702298
  have hstable : (prefixWord ++ tailWord_4702298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702298).length < 2 ^ (prefixWord ++ tailWord_4702298).sum := by decide
  have hdescent : baseEnd_4702298 < baseStart_4702298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702308 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_4702308 : Nat := 118140960795 + 4702308 * 2 ^ 59
def prefixEnd_4702308 : Nat := 4983230072969 + 3 ^ 40 * 4702308 * 2
def baseEnd_4702308 : Nat := 804848063160764477341495

theorem tailTrace_4702308 : CollatzResearch.WordTrace tailWord_4702308 prefixEnd_4702308 804848063160764477341495 := by
  unfold tailWord_4702308
  simp only [CollatzResearch.WordTrace]
  refine ⟨85753631324174340557113789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114338175098899120742818385 85753631324174340557113789)
  ·
    refine ⟨32157611746565377708917671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85753631324174340557113789 32157611746565377708917671)
    ·
      refine ⟨48236417619848066563376507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32157611746565377708917671 48236417619848066563376507)
      ·
        refine ⟨72354626429772099845064761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48236417619848066563376507 72354626429772099845064761)
        ·
          refine ⟨54265969822329074883798571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72354626429772099845064761 54265969822329074883798571)
          ·
            refine ⟨81398954733493612325697857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54265969822329074883798571 81398954733493612325697857)
            ·
              refine ⟨61049216050120209244273393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81398954733493612325697857 61049216050120209244273393)
              ·
                refine ⟨45786912037590156933205045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61049216050120209244273393 45786912037590156933205045)
                ·
                  refine ⟨4292523003524077212487973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45786912037590156933205045 4292523003524077212487973)
                  ·
                    refine ⟨804848063160764477341495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4292523003524077212487973 804848063160764477341495)
                    ·
                      rfl

theorem cell23_4702308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_4702308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702308 prefixEnd_4702308 := by exact prefixLift 4702308
  have htrace : WordTrace (prefixWord ++ tailWord_4702308) baseStart_4702308 baseEnd_4702308 := by
    simpa [prefixWord, tailWord_4702308, baseEnd_4702308] using wordTrace_append hprefix tailTrace_4702308
  have hstable : (prefixWord ++ tailWord_4702308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702308).length < 2 ^ (prefixWord ++ tailWord_4702308).sum := by decide
  have hdescent : baseEnd_4702308 < baseStart_4702308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702321 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 8]
def baseStart_4702321 : Nat := 118140960795 + 4702321 * 2 ^ 59
def prefixEnd_4702321 : Nat := 4983230072969 + 3 ^ 40 * 4702321 * 2
def baseEnd_4702321 : Nat := 268283429414533542351325

theorem tailTrace_4702321 : CollatzResearch.WordTrace tailWord_4702321 prefixEnd_4702321 268283429414533542351325 := by
  unfold tailWord_4702321
  simp only [CollatzResearch.WordTrace]
  refine ⟨171507736797301584334450817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114338491198201056222967211 171507736797301584334450817)
  ·
    refine ⟨128630802597976188250838113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171507736797301584334450817 128630802597976188250838113)
    ·
      refine ⟨96473101948482141188128585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128630802597976188250838113 96473101948482141188128585)
      ·
        refine ⟨72354826461361605891096439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96473101948482141188128585 72354826461361605891096439)
        ·
          refine ⟨108532239692042408836644659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72354826461361605891096439 108532239692042408836644659)
          ·
            refine ⟨162798359538063613254966989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108532239692042408836644659 162798359538063613254966989)
            ·
              refine ⟨61049384826773854970612621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162798359538063613254966989 61049384826773854970612621)
              ·
                refine ⟨22893519310040195613979733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61049384826773854970612621 22893519310040195613979733)
                ·
                  refine ⟨268283429414533542351325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22893519310040195613979733 268283429414533542351325)
                  ·
                    rfl

theorem cell23_4702321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 8].length) (baseStart_4702321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702321 prefixEnd_4702321 := by exact prefixLift 4702321
  have htrace : WordTrace (prefixWord ++ tailWord_4702321) baseStart_4702321 baseEnd_4702321 := by
    simpa [prefixWord, tailWord_4702321, baseEnd_4702321] using wordTrace_append hprefix tailTrace_4702321
  have hstable : (prefixWord ++ tailWord_4702321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702321).length < 2 ^ (prefixWord ++ tailWord_4702321).sum := by decide
  have hdescent : baseEnd_4702321 < baseStart_4702321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702361 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_4702361 : Nat := 118140960795 + 4702361 * 2 ^ 59
def prefixEnd_4702361 : Nat := 4983230072969 + 3 ^ 40 * 4702361 * 2
def baseEnd_4702361 : Nat := 2414571403956981724661741

theorem tailTrace_4702361 : CollatzResearch.WordTrace tailWord_4702361 prefixEnd_4702361 2414571403956981724661741 := by
  unfold tailWord_4702361
  simp only [CollatzResearch.WordTrace]
  refine ⟨171509195717156671165906937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114339463811437780777271291 171509195717156671165906937)
  ·
    refine ⟨128631896787867503374430203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171509195717156671165906937 128631896787867503374430203)
    ·
      refine ⟨192947845181801255061645305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128631896787867503374430203 192947845181801255061645305)
      ·
        refine ⟨144710883886350941296233979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192947845181801255061645305 144710883886350941296233979)
        ·
          refine ⟨217066325829526411944350969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144710883886350941296233979 217066325829526411944350969)
          ·
            refine ⟨162799744372144808958263227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217066325829526411944350969 162799744372144808958263227)
            ·
              refine ⟨244199616558217213437394841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162799744372144808958263227 244199616558217213437394841)
              ·
                refine ⟨183149712418662910078046131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244199616558217213437394841 183149712418662910078046131)
                ·
                  refine ⟨274724568627994365117069197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183149712418662910078046131 274724568627994365117069197)
                  ·
                    refine ⟨103021713235497886918900949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274724568627994365117069197 103021713235497886918900949)
                    ·
                      refine ⟨2414571403956981724661741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103021713235497886918900949 2414571403956981724661741)
                      ·
                        rfl

theorem cell23_4702361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_4702361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702361 prefixEnd_4702361 := by exact prefixLift 4702361
  have htrace : WordTrace (prefixWord ++ tailWord_4702361) baseStart_4702361 baseEnd_4702361 := by
    simpa [prefixWord, tailWord_4702361, baseEnd_4702361] using wordTrace_append hprefix tailTrace_4702361
  have hstable : (prefixWord ++ tailWord_4702361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702361).length < 2 ^ (prefixWord ++ tailWord_4702361).sum := by decide
  have hdescent : baseEnd_4702361 < baseStart_4702361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702439 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4702439 : Nat := 118140960795 + 4702439 * 2 ^ 59
def prefixEnd_4702439 : Nat := 4983230072969 + 3 ^ 40 * 4702439 * 2
def baseEnd_4702439 : Nat := 2414611455448032419486383

theorem tailTrace_4702439 : CollatzResearch.WordTrace tailWord_4702439 prefixEnd_4702439 2414611455448032419486383 := by
  unfold tailWord_4702439
  simp only [CollatzResearch.WordTrace]
  refine ⟨171512040610874090487246371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114341360407249393658164247 171512040610874090487246371)
  ·
    refine ⟨257268060916311135730869557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171512040610874090487246371 257268060916311135730869557)
    ·
      refine ⟨24118880710904168974769021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 257268060916311135730869557 24118880710904168974769021)
      ·
        refine ⟨9044580266589063365538383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24118880710904168974769021 9044580266589063365538383)
        ·
          refine ⟨13566870399883595048307575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9044580266589063365538383 13566870399883595048307575)
          ·
            refine ⟨20350305599825392572461363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13566870399883595048307575 20350305599825392572461363)
            ·
              refine ⟨30525458399738088858692045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20350305599825392572461363 30525458399738088858692045)
              ·
                refine ⟨11447046899901783322009517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30525458399738088858692045 11447046899901783322009517)
                ·
                  refine ⟨4292642587463168745753569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11447046899901783322009517 4292642587463168745753569)
                  ·
                    refine ⟨3219481940597376559315177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292642587463168745753569 3219481940597376559315177)
                    ·
                      refine ⟨2414611455448032419486383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219481940597376559315177 2414611455448032419486383)
                      ·
                        rfl

theorem cell23_4702439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4702439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702439 prefixEnd_4702439 := by exact prefixLift 4702439
  have htrace : WordTrace (prefixWord ++ tailWord_4702439) baseStart_4702439 baseEnd_4702439 := by
    simpa [prefixWord, tailWord_4702439, baseEnd_4702439] using wordTrace_append hprefix tailTrace_4702439
  have hstable : (prefixWord ++ tailWord_4702439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702439).length < 2 ^ (prefixWord ++ tailWord_4702439).sum := by decide
  have hdescent : baseEnd_4702439 < baseStart_4702439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702455 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_4702455 : Nat := 118140960795 + 4702455 * 2 ^ 59
def prefixEnd_4702455 : Nat := 4983230072969 + 3 ^ 40 * 4702455 * 2
def baseEnd_4702455 : Nat := 2414619671138504356886309

theorem tailTrace_4702455 : CollatzResearch.WordTrace tailWord_4702455 prefixEnd_4702455 2414619671138504356886309 := by
  unfold tailWord_4702455
  simp only [CollatzResearch.WordTrace]
  refine ⟨171512624178816125219828819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114341749452544083479885879 171512624178816125219828819)
  ·
    refine ⟨257268936268224187829743229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171512624178816125219828819 257268936268224187829743229)
    ·
      refine ⟨96475851100584070436153711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257268936268224187829743229 96475851100584070436153711)
      ·
        refine ⟨144713776650876105654230567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96475851100584070436153711 144713776650876105654230567)
        ·
          refine ⟨217070664976314158481345851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144713776650876105654230567 217070664976314158481345851)
          ·
            refine ⟨325605997464471237722018777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217070664976314158481345851 325605997464471237722018777)
            ·
              refine ⟨244204498098353428291514083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325605997464471237722018777 244204498098353428291514083)
              ·
                refine ⟨366306747147530142437271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244204498098353428291514083 366306747147530142437271125)
                ·
                  refine ⟨4292657193135118856686771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 366306747147530142437271125 4292657193135118856686771)
                  ·
                    refine ⟨6438985789702678285030157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4292657193135118856686771 6438985789702678285030157)
                    ·
                      refine ⟨2414619671138504356886309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6438985789702678285030157 2414619671138504356886309)
                      ·
                        rfl

theorem cell23_4702455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_4702455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702455 prefixEnd_4702455 := by exact prefixLift 4702455
  have htrace : WordTrace (prefixWord ++ tailWord_4702455) baseStart_4702455 baseEnd_4702455 := by
    simpa [prefixWord, tailWord_4702455, baseEnd_4702455] using wordTrace_append hprefix tailTrace_4702455
  have hstable : (prefixWord ++ tailWord_4702455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702455).length < 2 ^ (prefixWord ++ tailWord_4702455).sum := by decide
  have hdescent : baseEnd_4702455 < baseStart_4702455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702472 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_4702472 : Nat := 118140960795 + 4702472 * 2 ^ 59
def prefixEnd_4702472 : Nat := 4983230072969 + 3 ^ 40 * 4702472 * 2
def baseEnd_4702472 : Nat := 2414628400309630790373731

theorem tailTrace_4702472 : CollatzResearch.WordTrace tailWord_4702472 prefixEnd_4702472 2414628400309630790373731 := by
  unfold tailWord_4702472
  simp only [CollatzResearch.WordTrace]
  refine ⟨85756622109877268561598835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114342162813169691415465113 85756622109877268561598835)
  ·
    refine ⟨128634933164815902842398253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85756622109877268561598835 128634933164815902842398253)
    ·
      refine ⟨48238099936805963565899345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128634933164815902842398253 48238099936805963565899345)
      ·
        refine ⟨36178574952604472674424509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48238099936805963565899345 36178574952604472674424509)
        ·
          refine ⟨13566965607226677252909191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36178574952604472674424509 13566965607226677252909191)
          ·
            refine ⟨20350448410840015879363787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13566965607226677252909191 20350448410840015879363787)
            ·
              refine ⟨30525672616260023819045681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20350448410840015879363787 30525672616260023819045681)
              ·
                refine ⟨22894254462195017864284261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30525672616260023819045681 22894254462195017864284261)
                ·
                  refine ⟨4292672711661565849553299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22894254462195017864284261 4292672711661565849553299)
                  ·
                    refine ⟨6439009067492348774329949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4292672711661565849553299 6439009067492348774329949)
                    ·
                      refine ⟨2414628400309630790373731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6439009067492348774329949 2414628400309630790373731)
                      ·
                        rfl

theorem cell23_4702472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_4702472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702472 prefixEnd_4702472 := by exact prefixLift 4702472
  have htrace : WordTrace (prefixWord ++ tailWord_4702472) baseStart_4702472 baseEnd_4702472 := by
    simpa [prefixWord, tailWord_4702472, baseEnd_4702472] using wordTrace_append hprefix tailTrace_4702472
  have hstable : (prefixWord ++ tailWord_4702472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702472).length < 2 ^ (prefixWord ++ tailWord_4702472).sum := by decide
  have hdescent : baseEnd_4702472 < baseStart_4702472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702506 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4702506 : Nat := 118140960795 + 4702506 * 2 ^ 59
def prefixEnd_4702506 : Nat := 4983230072969 + 3 ^ 40 * 4702506 * 2
def baseEnd_4702506 : Nat := 2414645858651883657348575

theorem tailTrace_4702506 : CollatzResearch.WordTrace tailWord_4702506 prefixEnd_4702506 2414645858651883657348575 := by
  unfold tailWord_4702506
  simp only [CollatzResearch.WordTrace]
  refine ⟨42878621075407840232483843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114342989534420907286623581 42878621075407840232483843)
  ·
    refine ⟨64317931613111760348725765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42878621075407840232483843 64317931613111760348725765)
    ·
      refine ⟨12059612177458455065386081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64317931613111760348725765 12059612177458455065386081)
      ·
        refine ⟨9044709133093841299039561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12059612177458455065386081 9044709133093841299039561)
        ·
          refine ⟨6783531849820380974279671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9044709133093841299039561 6783531849820380974279671)
          ·
            refine ⟨10175297774730571461419507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6783531849820380974279671 10175297774730571461419507)
            ·
              refine ⟨15262946662095857192129261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10175297774730571461419507 15262946662095857192129261)
              ·
                refine ⟨5723604998285946447048473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15262946662095857192129261 5723604998285946447048473)
                ·
                  refine ⟨4292703748714459835286355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5723604998285946447048473 4292703748714459835286355)
                  ·
                    refine ⟨6439055623071689752929533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4292703748714459835286355 6439055623071689752929533)
                    ·
                      refine ⟨2414645858651883657348575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6439055623071689752929533 2414645858651883657348575)
                      ·
                        rfl

theorem cell23_4702506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4702506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702506 prefixEnd_4702506 := by exact prefixLift 4702506
  have htrace : WordTrace (prefixWord ++ tailWord_4702506) baseStart_4702506 baseEnd_4702506 := by
    simpa [prefixWord, tailWord_4702506, baseEnd_4702506] using wordTrace_append hprefix tailTrace_4702506
  have hstable : (prefixWord ++ tailWord_4702506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702506).length < 2 ^ (prefixWord ++ tailWord_4702506).sum := by decide
  have hdescent : baseEnd_4702506 < baseStart_4702506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702512 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 6, 2, 2]
def baseStart_4702512 : Nat := 118140960795 + 4702512 * 2 ^ 59
def prefixEnd_4702512 : Nat := 4983230072969 + 3 ^ 40 * 4702512 * 2
def baseEnd_4702512 : Nat := 2414648939535810633873547

theorem tailTrace_4702512 : CollatzResearch.WordTrace tailWord_4702512 prefixEnd_4702512 2414648939535810633873547 := by
  unfold tailWord_4702512
  simp only [CollatzResearch.WordTrace]
  refine ⟨85757351569804811977326895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114343135426406415969769193 85757351569804811977326895)
  ·
    refine ⟨128636027354707217965990343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85757351569804811977326895 128636027354707217965990343)
    ·
      refine ⟨192954041032060826948985515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128636027354707217965990343 192954041032060826948985515)
      ·
        refine ⟨289431061548091240423478273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192954041032060826948985515 289431061548091240423478273)
        ·
          refine ⟨217073296161068430317608705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289431061548091240423478273 217073296161068430317608705)
          ·
            refine ⟨162804972120801322738206529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217073296161068430317608705 162804972120801322738206529)
            ·
              refine ⟨122103729090600992053654897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162804972120801322738206529 122103729090600992053654897)
              ·
                refine ⟨91577796817950744040241173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122103729090600992053654897 91577796817950744040241173)
                ·
                  refine ⟨4292709225841441126886305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91577796817950744040241173 4292709225841441126886305)
                  ·
                    refine ⟨3219531919381080845164729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292709225841441126886305 3219531919381080845164729)
                    ·
                      refine ⟨2414648939535810633873547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219531919381080845164729 2414648939535810633873547)
                      ·
                        rfl

theorem cell23_4702512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 2, 2].length) (baseStart_4702512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702512 prefixEnd_4702512 := by exact prefixLift 4702512
  have htrace : WordTrace (prefixWord ++ tailWord_4702512) baseStart_4702512 baseEnd_4702512 := by
    simpa [prefixWord, tailWord_4702512, baseEnd_4702512] using wordTrace_append hprefix tailTrace_4702512
  have hstable : (prefixWord ++ tailWord_4702512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702512).length < 2 ^ (prefixWord ++ tailWord_4702512).sum := by decide
  have hdescent : baseEnd_4702512 < baseStart_4702512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702516 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_4702516 : Nat := 118140960795 + 4702516 * 2 ^ 59
def prefixEnd_4702516 : Nat := 4983230072969 + 3 ^ 40 * 4702516 * 2
def baseEnd_4702516 : Nat := 2414650993458428618223529

theorem tailTrace_4702516 : CollatzResearch.WordTrace tailWord_4702516 prefixEnd_4702516 2414650993458428618223529 := by
  unfold tailWord_4702516
  simp only [CollatzResearch.WordTrace]
  refine ⟨85757424515797566318899701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114343232687730088425199601 85757424515797566318899701)
  ·
    refine ⟨8039758548356021842396847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85757424515797566318899701 8039758548356021842396847)
    ·
      refine ⟨12059637822534032763595271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8039758548356021842396847 12059637822534032763595271)
      ·
        refine ⟨18089456733801049145392907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12059637822534032763595271 18089456733801049145392907)
        ·
          refine ⟨27134185100701573718089361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18089456733801049145392907 27134185100701573718089361)
          ·
            refine ⟨20350638825526180288567021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27134185100701573718089361 20350638825526180288567021)
            ·
              refine ⟨7631489559572317608212633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20350638825526180288567021 7631489559572317608212633)
              ·
                refine ⟨5723617169679238206159475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7631489559572317608212633 5723617169679238206159475)
                ·
                  refine ⟨8585425754518857309239213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5723617169679238206159475 8585425754518857309239213)
                  ·
                    refine ⟨3219534657944571490964705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8585425754518857309239213 3219534657944571490964705)
                    ·
                      refine ⟨2414650993458428618223529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219534657944571490964705 2414650993458428618223529)
                      ·
                        rfl

theorem cell23_4702516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_4702516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702516 prefixEnd_4702516 := by exact prefixLift 4702516
  have htrace : WordTrace (prefixWord ++ tailWord_4702516) baseStart_4702516 baseEnd_4702516 := by
    simpa [prefixWord, tailWord_4702516, baseEnd_4702516] using wordTrace_append hprefix tailTrace_4702516
  have hstable : (prefixWord ++ tailWord_4702516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702516).length < 2 ^ (prefixWord ++ tailWord_4702516).sum := by decide
  have hdescent : baseEnd_4702516 < baseStart_4702516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702528 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_4702528 : Nat := 118140960795 + 4702528 * 2 ^ 59
def prefixEnd_4702528 : Nat := 4983230072969 + 3 ^ 40 * 4702528 * 2
def baseEnd_4702528 : Nat := 2414657155226282571273473

theorem tailTrace_4702528 : CollatzResearch.WordTrace tailWord_4702528 prefixEnd_4702528 2414657155226282571273473 := by
  unfold tailWord_4702528
  simp only [CollatzResearch.WordTrace]
  refine ⟨85757643353775829343618119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114343524471701105791490825 85757643353775829343618119)
  ·
    refine ⟨128636465030663744015427179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85757643353775829343618119 128636465030663744015427179)
    ·
      refine ⟨192954697545995616023140769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128636465030663744015427179 192954697545995616023140769)
      ·
        refine ⟨144716023159496712017355577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192954697545995616023140769 144716023159496712017355577)
        ·
          refine ⟨108537017369622534013016683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144716023159496712017355577 108537017369622534013016683)
          ·
            refine ⟨162805526054433801019525025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108537017369622534013016683 162805526054433801019525025)
            ·
              refine ⟨122104144540825350764643769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162805526054433801019525025 122104144540825350764643769)
              ·
                refine ⟨91578108405619013073482827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122104144540825350764643769 91578108405619013073482827)
                ·
                  refine ⟨137367162608428519610224241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91578108405619013073482827 137367162608428519610224241)
                  ·
                    refine ⟨103025371956321389707668181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137367162608428519610224241 103025371956321389707668181)
                    ·
                      refine ⟨2414657155226282571273473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103025371956321389707668181 2414657155226282571273473)
                      ·
                        rfl

theorem cell23_4702528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_4702528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702528 prefixEnd_4702528 := by exact prefixLift 4702528
  have htrace : WordTrace (prefixWord ++ tailWord_4702528) baseStart_4702528 baseEnd_4702528 := by
    simpa [prefixWord, tailWord_4702528, baseEnd_4702528] using wordTrace_append hprefix tailTrace_4702528
  have hstable : (prefixWord ++ tailWord_4702528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702528).length < 2 ^ (prefixWord ++ tailWord_4702528).sum := by decide
  have hdescent : baseEnd_4702528 < baseStart_4702528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702562 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_4702562 : Nat := 118140960795 + 4702562 * 2 ^ 59
def prefixEnd_4702562 : Nat := 4983230072969 + 3 ^ 40 * 4702562 * 2
def baseEnd_4702562 : Nat := 2414674613568535438248317

theorem tailTrace_4702562 : CollatzResearch.WordTrace tailWord_4702562 prefixEnd_4702562 2414674613568535438248317 := by
  unfold tailWord_4702562
  simp only [CollatzResearch.WordTrace]
  refine ⟨42879131697357120623493485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114344351192952321662649293 42879131697357120623493485)
  ·
    refine ⟨16079674386508920233810057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42879131697357120623493485 16079674386508920233810057)
    ·
      refine ⟨12059755789881690175357543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16079674386508920233810057 12059755789881690175357543)
      ·
        refine ⟨18089633684822535263036315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12059755789881690175357543 18089633684822535263036315)
        ·
          refine ⟨27134450527233802894554473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18089633684822535263036315 27134450527233802894554473)
          ·
            refine ⟨20350837895425352170915855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27134450527233802894554473 20350837895425352170915855)
            ·
              refine ⟨30526256843138028256373783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20350837895425352170915855 30526256843138028256373783)
              ·
                refine ⟨45789385264707042384560675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30526256843138028256373783 45789385264707042384560675)
                ·
                  refine ⟨68684077897060563576841013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45789385264707042384560675 68684077897060563576841013)
                  ·
                    refine ⟨6439132302849427835328845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68684077897060563576841013 6439132302849427835328845)
                    ·
                      refine ⟨2414674613568535438248317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6439132302849427835328845 2414674613568535438248317)
                      ·
                        rfl

theorem cell23_4702562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_4702562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702562 prefixEnd_4702562 := by exact prefixLift 4702562
  have htrace : WordTrace (prefixWord ++ tailWord_4702562) baseStart_4702562 baseEnd_4702562 := by
    simpa [prefixWord, tailWord_4702562, baseEnd_4702562] using wordTrace_append hprefix tailTrace_4702562
  have hstable : (prefixWord ++ tailWord_4702562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702562).length < 2 ^ (prefixWord ++ tailWord_4702562).sum := by decide
  have hdescent : baseEnd_4702562 < baseStart_4702562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702614 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4702614 : Nat := 118140960795 + 4702614 * 2 ^ 59
def prefixEnd_4702614 : Nat := 4983230072969 + 3 ^ 40 * 4702614 * 2
def baseEnd_4702614 : Nat := 2414701314562569234798079

theorem tailTrace_4702614 : CollatzResearch.WordTrace tailWord_4702614 prefixEnd_4702614 2414701314562569234798079 := by
  unfold tailWord_4702614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10719901461577505960929181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114345615590160063583244597 10719901461577505960929181)
  ·
    refine ⟨4019963048091564735348443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10719901461577505960929181 4019963048091564735348443)
    ·
      refine ⟨6029944572137347103022665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019963048091564735348443 6029944572137347103022665)
      ·
        refine ⟨4522458429103010327266999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6029944572137347103022665 4522458429103010327266999)
        ·
          refine ⟨6783687643654515490900499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522458429103010327266999 6783687643654515490900499)
          ·
            refine ⟨10175531465481773236350749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6783687643654515490900499 10175531465481773236350749)
            ·
              refine ⟨3815824299555664963631531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10175531465481773236350749 3815824299555664963631531)
              ·
                refine ⟨5723736449333497445447297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815824299555664963631531 5723736449333497445447297)
                ·
                  refine ⟨4292802337000123084085473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5723736449333497445447297 4292802337000123084085473)
                  ·
                    refine ⟨3219601752750092313064105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292802337000123084085473 3219601752750092313064105)
                    ·
                      refine ⟨2414701314562569234798079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219601752750092313064105 2414701314562569234798079)
                      ·
                        rfl

theorem cell23_4702614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4702614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702614 prefixEnd_4702614 := by exact prefixLift 4702614
  have htrace : WordTrace (prefixWord ++ tailWord_4702614) baseStart_4702614 baseEnd_4702614 := by
    simpa [prefixWord, tailWord_4702614, baseEnd_4702614] using wordTrace_append hprefix tailTrace_4702614
  have hstable : (prefixWord ++ tailWord_4702614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702614).length < 2 ^ (prefixWord ++ tailWord_4702614).sum := by decide
  have hdescent : baseEnd_4702614 < baseStart_4702614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702655 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 7, 5]
def baseStart_4702655 : Nat := 118140960795 + 4702655 * 2 ^ 59
def prefixEnd_4702655 : Nat := 4983230072969 + 3 ^ 40 * 4702655 * 2
def baseEnd_4702655 : Nat := 804907455756467858128463

theorem tailTrace_4702655 : CollatzResearch.WordTrace tailWord_4702655 prefixEnd_4702655 804907455756467858128463 := by
  unfold tailWord_4702655
  simp only [CollatzResearch.WordTrace]
  refine ⟨171519918778091559377109419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114346612518727706251406279 171519918778091559377109419)
  ·
    refine ⟨257279878167137339065664129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171519918778091559377109419 257279878167137339065664129)
    ·
      refine ⟨192959908625353004299248097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257279878167137339065664129 192959908625353004299248097)
      ·
        refine ⟨144719931469014753224436073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192959908625353004299248097 144719931469014753224436073)
        ·
          refine ⟨108539948601761064918327055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144719931469014753224436073 108539948601761064918327055)
          ·
            refine ⟨162809922902641597377490583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108539948601761064918327055 162809922902641597377490583)
            ·
              refine ⟨244214884353962396066235875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162809922902641597377490583 244214884353962396066235875)
              ·
                refine ⟨366322326530943594099353813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244214884353962396066235875 366322326530943594099353813)
                ·
                  refine ⟨8585679528068990486703605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 366322326530943594099353813 8585679528068990486703605)
                  ·
                    refine ⟨804907455756467858128463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8585679528068990486703605 804907455756467858128463)
                    ·
                      rfl

theorem cell23_4702655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_4702655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702655 prefixEnd_4702655 := by exact prefixLift 4702655
  have htrace : WordTrace (prefixWord ++ tailWord_4702655) baseStart_4702655 baseEnd_4702655 := by
    simpa [prefixWord, tailWord_4702655, baseEnd_4702655] using wordTrace_append hprefix tailTrace_4702655
  have hstable : (prefixWord ++ tailWord_4702655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702655).length < 2 ^ (prefixWord ++ tailWord_4702655).sum := by decide
  have hdescent : baseEnd_4702655 < baseStart_4702655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702676 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 6]
def baseStart_4702676 : Nat := 118140960795 + 4702676 * 2 ^ 59
def prefixEnd_4702676 : Nat := 4983230072969 + 3 ^ 40 * 4702676 * 2
def baseEnd_4702676 : Nat := 268303683373683110246977

theorem tailTrace_4702676 : CollatzResearch.WordTrace tailWord_4702676 prefixEnd_4702676 268303683373683110246977 := by
  unfold tailWord_4702676
  simp only [CollatzResearch.WordTrace]
  refine ⟨85760342355507739981811941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114347123140676986642415921 85760342355507739981811941)
  ·
    refine ⟨16080064191657701246589739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85760342355507739981811941 16080064191657701246589739)
    ·
      refine ⟨24120096287486551869884609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16080064191657701246589739 24120096287486551869884609)
      ·
        refine ⟨18090072215614913902413457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24120096287486551869884609 18090072215614913902413457)
        ·
          refine ⟨13567554161711185426810093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18090072215614913902413457 13567554161711185426810093)
          ·
            refine ⟨5087832810641694535053785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13567554161711185426810093 5087832810641694535053785)
            ·
              refine ⟨3815874607981270901290339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5087832810641694535053785 3815874607981270901290339)
              ·
                refine ⟨5723811911971906351935509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815874607981270901290339 5723811911971906351935509)
                ·
                  refine ⟨268303683373683110246977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5723811911971906351935509 268303683373683110246977)
                  ·
                    rfl

theorem cell23_4702676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_4702676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702676 prefixEnd_4702676 := by exact prefixLift 4702676
  have htrace : WordTrace (prefixWord ++ tailWord_4702676) baseStart_4702676 baseEnd_4702676 := by
    simpa [prefixWord, tailWord_4702676, baseEnd_4702676] using wordTrace_append hprefix tailTrace_4702676
  have hstable : (prefixWord ++ tailWord_4702676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702676).length < 2 ^ (prefixWord ++ tailWord_4702676).sum := by decide
  have hdescent : baseEnd_4702676 < baseStart_4702676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702696 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_4702696 : Nat := 118140960795 + 4702696 * 2 ^ 59
def prefixEnd_4702696 : Nat := 4983230072969 + 3 ^ 40 * 4702696 * 2
def baseEnd_4702696 : Nat := 2414743419976237913972701

theorem tailTrace_4702696 : CollatzResearch.WordTrace tailWord_4702696 prefixEnd_4702696 2414743419976237913972701 := by
  unfold tailWord_4702696
  simp only [CollatzResearch.WordTrace]
  refine ⟨85760707085471511689675971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114347609447295348919567961 85760707085471511689675971)
  ·
    refine ⟨128641060628207267534513957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85760707085471511689675971 128641060628207267534513957)
    ·
      refine ⟨24120198867788862662721367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128641060628207267534513957 24120198867788862662721367)
      ·
        refine ⟨36180298301683293994082051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24120198867788862662721367 36180298301683293994082051)
        ·
          refine ⟨54270447452524940991123077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36180298301683293994082051 54270447452524940991123077)
          ·
            refine ⟨10175708897348426435835577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54270447452524940991123077 10175708897348426435835577)
            ·
              refine ⟨7631781673011319826876683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10175708897348426435835577 7631781673011319826876683)
              ·
                refine ⟨11447672509516979740315025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7631781673011319826876683 11447672509516979740315025)
                ·
                  refine ⟨8585754382137734805236269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11447672509516979740315025 8585754382137734805236269)
                  ·
                    refine ⟨3219657893301650551963601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8585754382137734805236269 3219657893301650551963601)
                    ·
                      refine ⟨2414743419976237913972701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219657893301650551963601 2414743419976237913972701)
                      ·
                        rfl

theorem cell23_4702696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_4702696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702696 prefixEnd_4702696 := by exact prefixLift 4702696
  have htrace : WordTrace (prefixWord ++ tailWord_4702696) baseStart_4702696 baseEnd_4702696 := by
    simpa [prefixWord, tailWord_4702696, baseEnd_4702696] using wordTrace_append hprefix tailTrace_4702696
  have hstable : (prefixWord ++ tailWord_4702696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702696).length < 2 ^ (prefixWord ++ tailWord_4702696).sum := by decide
  have hdescent : baseEnd_4702696 < baseStart_4702696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702702 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_4702702 : Nat := 118140960795 + 4702702 * 2 ^ 59
def prefixEnd_4702702 : Nat := 4983230072969 + 3 ^ 40 * 4702702 * 2
def baseEnd_4702702 : Nat := 804915500286721630165891

theorem tailTrace_4702702 : CollatzResearch.WordTrace tailWord_4702702 prefixEnd_4702702 804915500286721630165891 := by
  unfold tailWord_4702702
  simp only [CollatzResearch.WordTrace]
  refine ⟨21440204126115160800508795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114347755339280857602713573 21440204126115160800508795)
  ·
    refine ⟨32160306189172741200763193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21440204126115160800508795 32160306189172741200763193)
    ·
      refine ⟨24120229641879555900572395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32160306189172741200763193 24120229641879555900572395)
      ·
        refine ⟨36180344462819333850858593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24120229641879555900572395 36180344462819333850858593)
        ·
          refine ⟨27135258347114500388143945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36180344462819333850858593 27135258347114500388143945)
          ·
            refine ⟨20351443760335875291107959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27135258347114500388143945 20351443760335875291107959)
            ·
              refine ⟨30527165640503812936661939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20351443760335875291107959 30527165640503812936661939)
              ·
                refine ⟨45790748460755719404992909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30527165640503812936661939 45790748460755719404992909)
                ·
                  refine ⟨17171530672783394776872341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45790748460755719404992909 17171530672783394776872341)
                  ·
                    refine ⟨804915500286721630165891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17171530672783394776872341 804915500286721630165891)
                    ·
                      rfl

theorem cell23_4702702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_4702702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702702 prefixEnd_4702702 := by exact prefixLift 4702702
  have htrace : WordTrace (prefixWord ++ tailWord_4702702) baseStart_4702702 baseEnd_4702702 := by
    simpa [prefixWord, tailWord_4702702, baseEnd_4702702] using wordTrace_append hprefix tailTrace_4702702
  have hstable : (prefixWord ++ tailWord_4702702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702702).length < 2 ^ (prefixWord ++ tailWord_4702702).sum := by decide
  have hdescent : baseEnd_4702702 < baseStart_4702702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702719 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 2, 4]
def baseStart_4702719 : Nat := 118140960795 + 4702719 * 2 ^ 59
def prefixEnd_4702719 : Nat := 4983230072969 + 3 ^ 40 * 4702719 * 2
def baseEnd_4702719 : Nat := 804918410010430441328365

theorem tailTrace_4702719 : CollatzResearch.WordTrace tailWord_4702719 prefixEnd_4702719 804918410010430441328365 := by
  unfold tailWord_4702719
  simp only [CollatzResearch.WordTrace]
  refine ⟨171522253049859698307439211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114348168699906465538292807 171522253049859698307439211)
  ·
    refine ⟨257283379574789547461158817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171522253049859698307439211 257283379574789547461158817)
    ·
      refine ⟨192962534681092160595869113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257283379574789547461158817 192962534681092160595869113)
      ·
        refine ⟨144721901010819120446901835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192962534681092160595869113 144721901010819120446901835)
        ·
          refine ⟨217082851516228680670352753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144721901010819120446901835 217082851516228680670352753)
          ·
            refine ⟨162812138637171510502764565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217082851516228680670352753 162812138637171510502764565)
            ·
              refine ⟨7631818998617414554817089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 162812138637171510502764565 7631818998617414554817089)
              ·
                refine ⟨5723864248963060916112817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7631818998617414554817089 5723864248963060916112817)
                ·
                  refine ⟨4292898186722295687084613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5723864248963060916112817 4292898186722295687084613)
                  ·
                    refine ⟨804918410010430441328365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4292898186722295687084613 804918410010430441328365)
                    ·
                      rfl

theorem cell23_4702719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_4702719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702719 prefixEnd_4702719 := by exact prefixLift 4702719
  have htrace : WordTrace (prefixWord ++ tailWord_4702719) baseStart_4702719 baseEnd_4702719 := by
    simpa [prefixWord, tailWord_4702719, baseEnd_4702719] using wordTrace_append hprefix tailTrace_4702719
  have hstable : (prefixWord ++ tailWord_4702719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702719).length < 2 ^ (prefixWord ++ tailWord_4702719).sum := by decide
  have hdescent : baseEnd_4702719 < baseStart_4702719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702732 : List Nat := [2, 2, 1, 2, 4, 1, 3, 8]
def baseStart_4702732 : Nat := 118140960795 + 4702732 * 2 ^ 59
def prefixEnd_4702732 : Nat := 4983230072969 + 3 ^ 40 * 4702732 * 2
def baseEnd_4702732 : Nat := 89435626121474065671205

theorem tailTrace_4702732 : CollatzResearch.WordTrace tailWord_4702732 prefixEnd_4702732 89435626121474065671205 := by
  unfold tailWord_4702732
  simp only [CollatzResearch.WordTrace]
  refine ⟨85761363599406300763831225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114348484799208401018441633 85761363599406300763831225)
  ·
    refine ⟨64321022699554725572873419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85761363599406300763831225 64321022699554725572873419)
    ·
      refine ⟨96481534049332088359310129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64321022699554725572873419 96481534049332088359310129)
      ·
        refine ⟨72361150536999066269482597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96481534049332088359310129 72361150536999066269482597)
        ·
          refine ⟨13567715725687324925527987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72361150536999066269482597 13567715725687324925527987)
          ·
            refine ⟨20351573588530987388291981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13567715725687324925527987 20351573588530987388291981)
            ·
              refine ⟨7631840095699120270609493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20351573588530987388291981 7631840095699120270609493)
              ·
                refine ⟨89435626121474065671205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7631840095699120270609493 89435626121474065671205)
                ·
                  rfl

theorem cell23_4702732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 8].length) (baseStart_4702732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702732 prefixEnd_4702732 := by exact prefixLift 4702732
  have htrace : WordTrace (prefixWord ++ tailWord_4702732) baseStart_4702732 baseEnd_4702732 := by
    simpa [prefixWord, tailWord_4702732, baseEnd_4702732] using wordTrace_append hprefix tailTrace_4702732
  have hstable : (prefixWord ++ tailWord_4702732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702732).length < 2 ^ (prefixWord ++ tailWord_4702732).sum := by decide
  have hdescent : baseEnd_4702732 < baseStart_4702732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_4702735 : Nat := 118140960795 + 4702735 * 2 ^ 59
def prefixEnd_4702735 : Nat := 4983230072969 + 3 ^ 40 * 4702735 * 2
def baseEnd_4702735 : Nat := 2414763445721763261385021

theorem tailTrace_4702735 : CollatzResearch.WordTrace tailWord_4702735 prefixEnd_4702735 2414763445721763261385021 := by
  unfold tailWord_4702735
  simp only [CollatzResearch.WordTrace]
  refine ⟨171522836617801733040021659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114348557745201155360014439 171522836617801733040021659)
  ·
    refine ⟨257284254926702599560032489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171522836617801733040021659 257284254926702599560032489)
    ·
      refine ⟨192963191195026949670024367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257284254926702599560032489 192963191195026949670024367)
      ·
        refine ⟨289444786792540424505036551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192963191195026949670024367 289444786792540424505036551)
        ·
          refine ⟨434167180188810636757554827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289444786792540424505036551 434167180188810636757554827)
          ·
            refine ⟨651250770283215955136332241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434167180188810636757554827 651250770283215955136332241)
            ·
              refine ⟨488438077712411966352249181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651250770283215955136332241 488438077712411966352249181)
              ·
                refine ⟨183164279142154487382093443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488438077712411966352249181 183164279142154487382093443)
                ·
                  refine ⟨274746418713231731073140165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183164279142154487382093443 274746418713231731073140165)
                  ·
                    refine ⟨51514953508730949576213781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274746418713231731073140165 51514953508730949576213781)
                    ·
                      refine ⟨2414763445721763261385021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51514953508730949576213781 2414763445721763261385021)
                      ·
                        rfl

theorem cell23_4702735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_4702735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702735 prefixEnd_4702735 := by exact prefixLift 4702735
  have htrace : WordTrace (prefixWord ++ tailWord_4702735) baseStart_4702735 baseEnd_4702735 := by
    simpa [prefixWord, tailWord_4702735, baseEnd_4702735] using wordTrace_append hprefix tailTrace_4702735
  have hstable : (prefixWord ++ tailWord_4702735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702735).length < 2 ^ (prefixWord ++ tailWord_4702735).sum := by decide
  have hdescent : baseEnd_4702735 < baseStart_4702735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702749 : List Nat := [1, 4, 2, 2, 1, 3, 3, 7]
def baseStart_4702749 : Nat := 118140960795 + 4702749 * 2 ^ 59
def prefixEnd_4702749 : Nat := 4983230072969 + 3 ^ 40 * 4702749 * 2
def baseEnd_4702749 : Nat := 89435949424108378022591

theorem tailTrace_4702749 : CollatzResearch.WordTrace tailWord_4702749 prefixEnd_4702749 89435949424108378022591 := by
  unfold tailWord_4702749
  simp only [CollatzResearch.WordTrace]
  refine ⟨171523347239751013431031301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114348898159834008954020867 171523347239751013431031301)
  ·
    refine ⟨32160627607453315018318369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171523347239751013431031301 32160627607453315018318369)
    ·
      refine ⟨24120470705589986263738777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32160627607453315018318369 24120470705589986263738777)
      ·
        refine ⟨18090353029192489697804083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24120470705589986263738777 18090353029192489697804083)
        ·
          refine ⟨27135529543788734546706125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18090353029192489697804083 27135529543788734546706125)
          ·
            refine ⟨10175823578920775455014797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27135529543788734546706125 10175823578920775455014797)
            ·
              refine ⟨3815933842095290795630549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10175823578920775455014797 3815933842095290795630549)
              ·
                refine ⟨89435949424108378022591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3815933842095290795630549 89435949424108378022591)
                ·
                  rfl

theorem cell23_4702749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 7].length) (baseStart_4702749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702749 prefixEnd_4702749 := by exact prefixLift 4702749
  have htrace : WordTrace (prefixWord ++ tailWord_4702749) baseStart_4702749 baseEnd_4702749 := by
    simpa [prefixWord, tailWord_4702749, baseEnd_4702749] using wordTrace_append hprefix tailTrace_4702749
  have hstable : (prefixWord ++ tailWord_4702749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702749).length < 2 ^ (prefixWord ++ tailWord_4702749).sum := by decide
  have hdescent : baseEnd_4702749 < baseStart_4702749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702760 : List Nat := [2, 1, 5, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4702760 : Nat := 118140960795 + 4702760 * 2 ^ 59
def prefixEnd_4702760 : Nat := 4983230072969 + 3 ^ 40 * 4702760 * 2
def baseEnd_4702760 : Nat := 2414776282738125663572407

theorem tailTrace_4702760 : CollatzResearch.WordTrace tailWord_4702760 prefixEnd_4702760 2414776282738125663572407 := by
  unfold tailWord_4702760
  simp only [CollatzResearch.WordTrace]
  refine ⟨85761874221355581154840867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114349165628474108206454489 85761874221355581154840867)
  ·
    refine ⟨128642811332033371732261301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85761874221355581154840867 128642811332033371732261301)
    ·
      refine ⟨12060263562378128599899497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128642811332033371732261301 12060263562378128599899497)
      ·
        refine ⟨9045197671783596449924623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12060263562378128599899497 9045197671783596449924623)
        ·
          refine ⟨13567796507675394674886935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9045197671783596449924623 13567796507675394674886935)
          ·
            refine ⟨20351694761513092012330403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13567796507675394674886935 20351694761513092012330403)
            ·
              refine ⟨30527542142269638018495605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20351694761513092012330403 30527542142269638018495605)
              ·
                refine ⟨2861957075837778564233963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30527542142269638018495605 2861957075837778564233963)
                ·
                  refine ⟨4292935613756667846350945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861957075837778564233963 4292935613756667846350945)
                  ·
                    refine ⟨3219701710317500884763209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292935613756667846350945 3219701710317500884763209)
                    ·
                      refine ⟨2414776282738125663572407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219701710317500884763209 2414776282738125663572407)
                      ·
                        rfl

theorem cell23_4702760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4702760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702760 prefixEnd_4702760 := by exact prefixLift 4702760
  have htrace : WordTrace (prefixWord ++ tailWord_4702760) baseStart_4702760 baseEnd_4702760 := by
    simpa [prefixWord, tailWord_4702760, baseEnd_4702760] using wordTrace_append hprefix tailTrace_4702760
  have hstable : (prefixWord ++ tailWord_4702760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702760).length < 2 ^ (prefixWord ++ tailWord_4702760).sum := by decide
  have hdescent : baseEnd_4702760 < baseStart_4702760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702816 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 4, 2, 2]
def baseStart_4702816 : Nat := 118140960795 + 4702816 * 2 ^ 59
def prefixEnd_4702816 : Nat := 4983230072969 + 3 ^ 40 * 4702816 * 2
def baseEnd_4702816 : Nat := 2414805037654777444472149

theorem tailTrace_4702816 : CollatzResearch.WordTrace tailWord_4702816 prefixEnd_4702816 2414805037654777444472149 := by
  unfold tailWord_4702816
  simp only [CollatzResearch.WordTrace]
  refine ⟨85762895465254141936860151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114350527287005522582480201 85762895465254141936860151)
  ·
    refine ⟨128644343197881212905290227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85762895465254141936860151 128644343197881212905290227)
    ·
      refine ⟨192966514796821819357935341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128644343197881212905290227 192966514796821819357935341)
      ·
        refine ⟨72362443048808182259225753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192966514796821819357935341 72362443048808182259225753)
        ·
          refine ⟨54271832286606136694419315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72362443048808182259225753 54271832286606136694419315)
          ·
            refine ⟨81407748429909205041628973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54271832286606136694419315 81407748429909205041628973)
            ·
              refine ⟨30527905661215951890610865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81407748429909205041628973 30527905661215951890610865)
              ·
                refine ⟨22895929245911963917958149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30527905661215951890610865 22895929245911963917958149)
                ·
                  refine ⟨4292986733608493234617153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22895929245911963917958149 4292986733608493234617153)
                  ·
                    refine ⟨3219740050206369925962865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292986733608493234617153 3219740050206369925962865)
                    ·
                      refine ⟨2414805037654777444472149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219740050206369925962865 2414805037654777444472149)
                      ·
                        rfl

theorem cell23_4702816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_4702816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702816 prefixEnd_4702816 := by exact prefixLift 4702816
  have htrace : WordTrace (prefixWord ++ tailWord_4702816) baseStart_4702816 baseEnd_4702816 := by
    simpa [prefixWord, tailWord_4702816, baseEnd_4702816] using wordTrace_append hprefix tailTrace_4702816
  have hstable : (prefixWord ++ tailWord_4702816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702816).length < 2 ^ (prefixWord ++ tailWord_4702816).sum := by decide
  have hdescent : baseEnd_4702816 < baseStart_4702816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702839 : List Nat := [1, 1, 3, 1, 1, 3, 2, 6, 5]
def baseStart_4702839 : Nat := 118140960795 + 4702839 * 2 ^ 59
def prefixEnd_4702839 : Nat := 4983230072969 + 3 ^ 40 * 4702839 * 2
def baseEnd_4702839 : Nat := 268312983078870094942727

theorem tailTrace_4702839 : CollatzResearch.WordTrace tailWord_4702839 prefixEnd_4702839 268312983078870094942727 := by
  unfold tailWord_4702839
  simp only [CollatzResearch.WordTrace]
  refine ⟨171526629809424958801807571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114351086539616639201205047 171526629809424958801807571)
  ·
    refine ⟨257289944714137438202711357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171526629809424958801807571 257289944714137438202711357)
    ·
      refine ⟨96483729267801539326016759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257289944714137438202711357 96483729267801539326016759)
      ·
        refine ⟨144725593901702308989025139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96483729267801539326016759 144725593901702308989025139)
        ·
          refine ⟨217088390852553463483537709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144725593901702308989025139 217088390852553463483537709)
          ·
            refine ⟨81408146569707548806326641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217088390852553463483537709 81408146569707548806326641)
            ·
              refine ⟨61056109927280661604744981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81408146569707548806326641 61056109927280661604744981)
              ·
                refine ⟨2862005152841281012722421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61056109927280661604744981 2862005152841281012722421)
                ·
                  refine ⟨268312983078870094942727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862005152841281012722421 268312983078870094942727)
                  ·
                    rfl

theorem cell23_4702839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 5].length) (baseStart_4702839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702839 prefixEnd_4702839 := by exact prefixLift 4702839
  have htrace : WordTrace (prefixWord ++ tailWord_4702839) baseStart_4702839 baseEnd_4702839 := by
    simpa [prefixWord, tailWord_4702839, baseEnd_4702839] using wordTrace_append hprefix tailTrace_4702839
  have hstable : (prefixWord ++ tailWord_4702839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702839).length < 2 ^ (prefixWord ++ tailWord_4702839).sum := by decide
  have hdescent : baseEnd_4702839 < baseStart_4702839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702849 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_4702849 : Nat := 118140960795 + 4702849 * 2 ^ 59
def prefixEnd_4702849 : Nat := 4983230072969 + 3 ^ 40 * 4702849 * 2
def baseEnd_4702849 : Nat := 2414821982516375815359497

theorem tailTrace_4702849 : CollatzResearch.WordTrace tailWord_4702849 prefixEnd_4702849 2414821982516375815359497 := by
  unfold tailWord_4702849
  simp only [CollatzResearch.WordTrace]
  refine ⟨171526994539388730509671601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114351329692925820339781067 171526994539388730509671601)
  ·
    refine ⟨128645245904541547882253701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171526994539388730509671601 128645245904541547882253701)
    ·
      refine ⟨24120983607101540227922569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128645245904541547882253701 24120983607101540227922569)
      ·
        refine ⟨18090737705326155170941927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24120983607101540227922569 18090737705326155170941927)
        ·
          refine ⟨27136106557989232756412891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18090737705326155170941927 27136106557989232756412891)
          ·
            refine ⟨40704159836983849134619337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27136106557989232756412891 40704159836983849134619337)
            ·
              refine ⟨30528119877737886850964503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40704159836983849134619337 30528119877737886850964503)
              ·
                refine ⟨45792179816606830276446755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30528119877737886850964503 45792179816606830276446755)
                ·
                  refine ⟨68688269724910245414670133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45792179816606830276446755 68688269724910245414670133)
                  ·
                    refine ⟨6439525286710335507625325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68688269724910245414670133 6439525286710335507625325)
                    ·
                      refine ⟨2414821982516375815359497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6439525286710335507625325 2414821982516375815359497)
                      ·
                        rfl

theorem cell23_4702849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_4702849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702849 prefixEnd_4702849 := by exact prefixLift 4702849
  have htrace : WordTrace (prefixWord ++ tailWord_4702849) baseStart_4702849 baseEnd_4702849 := by
    simpa [prefixWord, tailWord_4702849, baseEnd_4702849] using wordTrace_append hprefix tailTrace_4702849
  have hstable : (prefixWord ++ tailWord_4702849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702849).length < 2 ^ (prefixWord ++ tailWord_4702849).sum := by decide
  have hdescent : baseEnd_4702849 < baseStart_4702849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702859 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 4, 5, 2]
def baseStart_4702859 : Nat := 118140960795 + 4702859 * 2 ^ 59
def prefixEnd_4702859 : Nat := 4983230072969 + 3 ^ 40 * 4702859 * 2
def baseEnd_4702859 : Nat := 2414827117322920776234451

theorem tailTrace_4702859 : CollatzResearch.WordTrace tailWord_4702859 prefixEnd_4702859 2414827117322920776234451 := by
  unfold tailWord_4702859
  simp only [CollatzResearch.WordTrace]
  refine ⟨171527359269352502217535631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114351572846235001478357087 171527359269352502217535631)
  ·
    refine ⟨257291038904028753326303447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171527359269352502217535631 257291038904028753326303447)
    ·
      refine ⟨385936558356043129989455171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257291038904028753326303447 385936558356043129989455171)
      ·
        refine ⟨578904837534064694984182757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385936558356043129989455171 578904837534064694984182757)
        ·
          refine ⟨108544657037637130309534267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 578904837534064694984182757 108544657037637130309534267)
          ·
            refine ⟨162816985556455695464301401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108544657037637130309534267 162816985556455695464301401)
            ·
              refine ⟨122112739167341771598226051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162816985556455695464301401 122112739167341771598226051)
              ·
                refine ⟨183169108751012657397339077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122112739167341771598226051 183169108751012657397339077)
                ·
                  refine ⟨34344207890814873262001077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183169108751012657397339077 34344207890814873262001077)
                  ·
                    refine ⟨3219769489763894368312601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34344207890814873262001077 3219769489763894368312601)
                    ·
                      refine ⟨2414827117322920776234451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219769489763894368312601 2414827117322920776234451)
                      ·
                        rfl

theorem cell23_4702859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5, 2].length) (baseStart_4702859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702859 prefixEnd_4702859 := by exact prefixLift 4702859
  have htrace : WordTrace (prefixWord ++ tailWord_4702859) baseStart_4702859 baseEnd_4702859 := by
    simpa [prefixWord, tailWord_4702859, baseEnd_4702859] using wordTrace_append hprefix tailTrace_4702859
  have hstable : (prefixWord ++ tailWord_4702859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702859).length < 2 ^ (prefixWord ++ tailWord_4702859).sum := by decide
  have hdescent : baseEnd_4702859 < baseStart_4702859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702890 : List Nat := [3, 1, 5, 2, 1, 1, 1, 4, 5]
def baseStart_4702890 : Nat := 118140960795 + 4702890 * 2 ^ 59
def prefixEnd_4702890 : Nat := 4983230072969 + 3 ^ 40 * 4702890 * 2
def baseEnd_4702890 : Nat := 268315892802578906105201

theorem tailTrace_4702890 : CollatzResearch.WordTrace tailWord_4702890 prefixEnd_4702890 268315892802578906105201 := by
  unfold tailWord_4702890
  simp only [CollatzResearch.WordTrace]
  refine ⟨42882122483060048627978531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114352326621493463007942749 42882122483060048627978531)
  ·
    refine ⟨64323183724590072941967797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42882122483060048627978531 64323183724590072941967797)
    ·
      refine ⟨6030298474180319338309481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64323183724590072941967797 6030298474180319338309481)
      ·
        refine ⟨4522723855635239503732111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6030298474180319338309481 4522723855635239503732111)
        ·
          refine ⟨6784085783452859255598167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522723855635239503732111 6784085783452859255598167)
          ·
            refine ⟨10176128675179288883397251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6784085783452859255598167 10176128675179288883397251)
            ·
              refine ⟨15264193012768933325095877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10176128675179288883397251 15264193012768933325095877)
              ·
                refine ⟨2862036189894174998455477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15264193012768933325095877 2862036189894174998455477)
                ·
                  refine ⟨268315892802578906105201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862036189894174998455477 268315892802578906105201)
                  ·
                    rfl

theorem cell23_4702890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_4702890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702890 prefixEnd_4702890 := by exact prefixLift 4702890
  have htrace : WordTrace (prefixWord ++ tailWord_4702890) baseStart_4702890 baseEnd_4702890 := by
    simpa [prefixWord, tailWord_4702890, baseEnd_4702890] using wordTrace_append hprefix tailTrace_4702890
  have hstable : (prefixWord ++ tailWord_4702890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702890).length < 2 ^ (prefixWord ++ tailWord_4702890).sum := by decide
  have hdescent : baseEnd_4702890 < baseStart_4702890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702906 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2]
def baseStart_4702906 : Nat := 118140960795 + 4702906 * 2 ^ 59
def prefixEnd_4702906 : Nat := 4983230072969 + 3 ^ 40 * 4702906 * 2
def baseEnd_4702906 : Nat := 2414851250913682092346735

theorem tailTrace_4702906 : CollatzResearch.WordTrace tailWord_4702906 prefixEnd_4702906 2414851250913682092346735 := by
  unfold tailWord_4702906
  simp only [CollatzResearch.WordTrace]
  refine ⟨42882268375045557311124143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114352715666788152829664381 42882268375045557311124143)
  ·
    refine ⟨64323402562568335966686215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42882268375045557311124143 64323402562568335966686215)
    ·
      refine ⟨96485103843852503950029323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64323402562568335966686215 96485103843852503950029323)
      ·
        refine ⟨144727655765778755925043985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96485103843852503950029323 144727655765778755925043985)
        ·
          refine ⟨108545741824334066943782989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144727655765778755925043985 108545741824334066943782989)
          ·
            refine ⟨40704653184125275103918621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108545741824334066943782989 40704653184125275103918621)
            ·
              refine ⟨15264244944046978163969483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40704653184125275103918621 15264244944046978163969483)
              ·
                refine ⟨22896367416070467245954225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15264244944046978163969483 22896367416070467245954225)
                ·
                  refine ⟨17172275562052850434465669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22896367416070467245954225 17172275562052850434465669)
                  ·
                    refine ⟨3219801667884909456462313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17172275562052850434465669 3219801667884909456462313)
                    ·
                      refine ⟨2414851250913682092346735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219801667884909456462313 2414851250913682092346735)
                      ·
                        rfl

theorem cell23_4702906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_4702906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702906 prefixEnd_4702906 := by exact prefixLift 4702906
  have htrace : WordTrace (prefixWord ++ tailWord_4702906) baseStart_4702906 baseEnd_4702906 := by
    simpa [prefixWord, tailWord_4702906, baseEnd_4702906] using wordTrace_append hprefix tailTrace_4702906
  have hstable : (prefixWord ++ tailWord_4702906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702906).length < 2 ^ (prefixWord ++ tailWord_4702906).sum := by decide
  have hdescent : baseEnd_4702906 < baseStart_4702906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702916 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4702916 : Nat := 118140960795 + 4702916 * 2 ^ 59
def prefixEnd_4702916 : Nat := 4983230072969 + 3 ^ 40 * 4702916 * 2
def baseEnd_4702916 : Nat := 804952128573409017740563

theorem tailTrace_4702916 : CollatzResearch.WordTrace tailWord_4702916 prefixEnd_4702916 804952128573409017740563 := by
  unfold tailWord_4702916
  simp only [CollatzResearch.WordTrace]
  refine ⟨85764719115073000476180301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114352958820097333968240401 85764719115073000476180301)
  ·
    refine ⟨32161769668152375178567613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85764719115073000476180301 32161769668152375178567613)
    ·
      refine ⟨12060663625557140691962855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32161769668152375178567613 12060663625557140691962855)
      ·
        refine ⟨18090995438335711037944283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12060663625557140691962855 18090995438335711037944283)
        ·
          refine ⟨27136493157503566556916425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18090995438335711037944283 27136493157503566556916425)
          ·
            refine ⟨20352369868127674917687319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27136493157503566556916425 20352369868127674917687319)
            ·
              refine ⟨30528554802191512376530979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20352369868127674917687319 30528554802191512376530979)
              ·
                refine ⟨45792832203287268564796469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30528554802191512376530979 45792832203287268564796469)
                ·
                  refine ⟨4293078019058181427949669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45792832203287268564796469 4293078019058181427949669)
                  ·
                    refine ⟨804952128573409017740563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293078019058181427949669 804952128573409017740563)
                    ·
                      rfl

theorem cell23_4702916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4702916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702916 prefixEnd_4702916 := by exact prefixLift 4702916
  have htrace : WordTrace (prefixWord ++ tailWord_4702916) baseStart_4702916 baseEnd_4702916 := by
    simpa [prefixWord, tailWord_4702916, baseEnd_4702916] using wordTrace_append hprefix tailTrace_4702916
  have hstable : (prefixWord ++ tailWord_4702916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702916).length < 2 ^ (prefixWord ++ tailWord_4702916).sum := by decide
  have hdescent : baseEnd_4702916 < baseStart_4702916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702926 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_4702926 : Nat := 118140960795 + 4702926 * 2 ^ 59
def prefixEnd_4702926 : Nat := 4983230072969 + 3 ^ 40 * 4702926 * 2
def baseEnd_4702926 : Nat := 2414861520526772014096643

theorem tailTrace_4702926 : CollatzResearch.WordTrace tailWord_4702926 prefixEnd_4702926 2414861520526772014096643 := by
  unfold tailWord_4702926
  simp only [CollatzResearch.WordTrace]
  refine ⟨21441225370013721582528079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114353201973406515106816421 21441225370013721582528079)
  ·
    refine ⟨32161838055020582373792119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21441225370013721582528079 32161838055020582373792119)
    ·
      refine ⟨48242757082530873560688179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32161838055020582373792119 48242757082530873560688179)
      ·
        refine ⟨72364135623796310341032269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48242757082530873560688179 72364135623796310341032269)
        ·
          refine ⟨27136550858923616377887101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72364135623796310341032269 27136550858923616377887101)
          ·
            refine ⟨10176206572096356141707663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27136550858923616377887101 10176206572096356141707663)
            ·
              refine ⟨15264309858144534212561495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10176206572096356141707663 15264309858144534212561495)
              ·
                refine ⟨22896464787216801318842243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15264309858144534212561495 22896464787216801318842243)
                ·
                  refine ⟨34344697180825201978263365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22896464787216801318842243 34344697180825201978263365)
                  ·
                    refine ⟨6439630721404725370924381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34344697180825201978263365 6439630721404725370924381)
                    ·
                      refine ⟨2414861520526772014096643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6439630721404725370924381 2414861520526772014096643)
                      ·
                        rfl

theorem cell23_4702926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_4702926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702926 prefixEnd_4702926 := by exact prefixLift 4702926
  have htrace : WordTrace (prefixWord ++ tailWord_4702926) baseStart_4702926 baseEnd_4702926 := by
    simpa [prefixWord, tailWord_4702926, baseEnd_4702926] using wordTrace_append hprefix tailTrace_4702926
  have hstable : (prefixWord ++ tailWord_4702926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702926).length < 2 ^ (prefixWord ++ tailWord_4702926).sum := by decide
  have hdescent : baseEnd_4702926 < baseStart_4702926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702949 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4702949 : Nat := 118140960795 + 4702949 * 2 ^ 59
def prefixEnd_4702949 : Nat := 4983230072969 + 3 ^ 40 * 4702949 * 2
def baseEnd_4702949 : Nat := 2414873330581825424109037

theorem tailTrace_4702949 : CollatzResearch.WordTrace tailWord_4702949 prefixEnd_4702949 2414873330581825424109037 := by
  unfold tailWord_4702949
  simp only [CollatzResearch.WordTrace]
  refine ⟨171530641839026447588311901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114353761226017631725541267 171530641839026447588311901)
  ·
    refine ⟨64323990689634917845616963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171530641839026447588311901 64323990689634917845616963)
    ·
      refine ⟨96485986034452376768425445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64323990689634917845616963 96485986034452376768425445)
      ·
        refine ⟨18091122381459820644079771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96485986034452376768425445 18091122381459820644079771)
        ·
          refine ⟨27136683572189730966119657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18091122381459820644079771 27136683572189730966119657)
          ·
            refine ⟨20352512679142298224589743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27136683572189730966119657 20352512679142298224589743)
            ·
              refine ⟨30528769018713447336884615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20352512679142298224589743 30528769018713447336884615)
              ·
                refine ⟨45793153528070171005326923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30528769018713447336884615 45793153528070171005326923)
                ·
                  refine ⟨68689730292105256507990385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45793153528070171005326923 68689730292105256507990385)
                  ·
                    refine ⟨51517297719078942380992789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68689730292105256507990385 51517297719078942380992789)
                    ·
                      refine ⟨2414873330581825424109037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51517297719078942380992789 2414873330581825424109037)
                      ·
                        rfl

theorem cell23_4702949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4702949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702949 prefixEnd_4702949 := by exact prefixLift 4702949
  have htrace : WordTrace (prefixWord ++ tailWord_4702949) baseStart_4702949 baseEnd_4702949 := by
    simpa [prefixWord, tailWord_4702949, baseEnd_4702949] using wordTrace_append hprefix tailTrace_4702949
  have hstable : (prefixWord ++ tailWord_4702949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702949).length < 2 ^ (prefixWord ++ tailWord_4702949).sum := by decide
  have hdescent : baseEnd_4702949 < baseStart_4702949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4702983 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4702983 : Nat := 118140960795 + 4702983 * 2 ^ 59
def prefixEnd_4702983 : Nat := 4983230072969 + 3 ^ 40 * 4702983 * 2
def baseEnd_4702983 : Nat := 2414890788924078291083881

theorem tailTrace_4702983 : CollatzResearch.WordTrace tailWord_4702983 prefixEnd_4702983 2414890788924078291083881 := by
  unfold tailWord_4702983
  simp only [CollatzResearch.WordTrace]
  refine ⟨171531881920903271395049603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114354587947268847596699735 171531881920903271395049603)
  ·
    refine ⟨257297822881354907092574405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171531881920903271395049603 257297822881354907092574405)
    ·
      refine ⟨48243341790254045079857701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257297822881354907092574405 48243341790254045079857701)
      ·
        refine ⟨9045626585672633452473319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48243341790254045079857701 9045626585672633452473319)
        ·
          refine ⟨13568439878508950178709979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9045626585672633452473319 13568439878508950178709979)
          ·
            refine ⟨20352659817763425268064969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13568439878508950178709979 20352659817763425268064969)
            ·
              refine ⟨15264494863322568951048727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20352659817763425268064969 15264494863322568951048727)
              ·
                refine ⟨22896742294983853426573091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15264494863322568951048727 22896742294983853426573091)
                ·
                  refine ⟨34345113442475780139859637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22896742294983853426573091 34345113442475780139859637)
                  ·
                    refine ⟨3219854385232104388111841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34345113442475780139859637 3219854385232104388111841)
                    ·
                      refine ⟨2414890788924078291083881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219854385232104388111841 2414890788924078291083881)
                      ·
                        rfl

theorem cell23_4702983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4702983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4702983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4702983 prefixEnd_4702983 := by exact prefixLift 4702983
  have htrace : WordTrace (prefixWord ++ tailWord_4702983) baseStart_4702983 baseEnd_4702983 := by
    simpa [prefixWord, tailWord_4702983, baseEnd_4702983] using wordTrace_append hprefix tailTrace_4702983
  have hstable : (prefixWord ++ tailWord_4702983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4702983).length < 2 ^ (prefixWord ++ tailWord_4702983).sum := by decide
  have hdescent : baseEnd_4702983 < baseStart_4702983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4702983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703007 : List Nat := [1, 1, 2, 4, 2, 3, 3, 2, 1, 1, 3]
def baseStart_4703007 : Nat := 118140960795 + 4703007 * 2 ^ 59
def prefixEnd_4703007 : Nat := 4983230072969 + 3 ^ 40 * 4703007 * 2
def baseEnd_4703007 : Nat := 2414903112459786197183771

theorem tailTrace_4703007 : CollatzResearch.WordTrace tailWord_4703007 prefixEnd_4703007 2414903112459786197183771 := by
  unfold tailWord_4703007
  simp only [CollatzResearch.WordTrace]
  refine ⟨171532757272816323493923275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114355171515210882329282183 171532757272816323493923275)
  ·
    refine ⟨257299135909224485240884913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171532757272816323493923275 257299135909224485240884913)
    ·
      refine ⟨192974351931918363930663685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257299135909224485240884913 192974351931918363930663685)
      ·
        refine ⟨36182690987234693236999441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192974351931918363930663685 36182690987234693236999441)
        ·
          refine ⟨27137018240426019927749581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36182690987234693236999441 27137018240426019927749581)
          ·
            refine ⟨10176381840159757472906093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27137018240426019927749581 10176381840159757472906093)
            ·
              refine ⟨3816143190059909052339785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10176381840159757472906093 3816143190059909052339785)
              ·
                refine ⟨2862107392544931789254839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816143190059909052339785 2862107392544931789254839)
                ·
                  refine ⟨4293161088817397683882259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862107392544931789254839 4293161088817397683882259)
                  ·
                    refine ⟨6439741633226096525823389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4293161088817397683882259 6439741633226096525823389)
                    ·
                      refine ⟨2414903112459786197183771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6439741633226096525823389 2414903112459786197183771)
                      ·
                        rfl

theorem cell23_4703007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_4703007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703007 prefixEnd_4703007 := by exact prefixLift 4703007
  have htrace : WordTrace (prefixWord ++ tailWord_4703007) baseStart_4703007 baseEnd_4703007 := by
    simpa [prefixWord, tailWord_4703007, baseEnd_4703007] using wordTrace_append hprefix tailTrace_4703007
  have hstable : (prefixWord ++ tailWord_4703007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703007).length < 2 ^ (prefixWord ++ tailWord_4703007).sum := by decide
  have hdescent : baseEnd_4703007 < baseStart_4703007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703009 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4703009 : Nat := 118140960795 + 4703009 * 2 ^ 59
def prefixEnd_4703009 : Nat := 4983230072969 + 3 ^ 40 * 4703009 * 2
def baseEnd_4703009 : Nat := 2414904139421095189358761

theorem tailTrace_4703009 : CollatzResearch.WordTrace tailWord_4703009 prefixEnd_4703009 2414904139421095189358761 := by
  unfold tailWord_4703009
  simp only [CollatzResearch.WordTrace]
  refine ⟨171532830218809077835496081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114355220145872718556997387 171532830218809077835496081)
  ·
    refine ⟨128649622664106808376622061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171532830218809077835496081 128649622664106808376622061)
    ·
      refine ⟨48243608499040053141233273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128649622664106808376622061 48243608499040053141233273)
      ·
        refine ⟨36182706374280039855924955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48243608499040053141233273 36182706374280039855924955)
        ·
          refine ⟨54274059561420059783887433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36182706374280039855924955 54274059561420059783887433)
          ·
            refine ⟨40705544671065044837915575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54274059561420059783887433 40705544671065044837915575)
            ·
              refine ⟨61058317006597567256873363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40705544671065044837915575 61058317006597567256873363)
              ·
                refine ⟨91587475509896350885310045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61058317006597567256873363 91587475509896350885310045)
                ·
                  refine ⟨34345303316211131581991267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91587475509896350885310045 34345303316211131581991267)
                  ·
                    refine ⟨51517954974316697372986901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34345303316211131581991267 51517954974316697372986901)
                    ·
                      refine ⟨2414904139421095189358761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51517954974316697372986901 2414904139421095189358761)
                      ·
                        rfl

theorem cell23_4703009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4703009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703009 prefixEnd_4703009 := by exact prefixLift 4703009
  have htrace : WordTrace (prefixWord ++ tailWord_4703009) baseStart_4703009 baseEnd_4703009 := by
    simpa [prefixWord, tailWord_4703009, baseEnd_4703009] using wordTrace_append hprefix tailTrace_4703009
  have hstable : (prefixWord ++ tailWord_4703009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703009).length < 2 ^ (prefixWord ++ tailWord_4703009).sum := by decide
  have hdescent : baseEnd_4703009 < baseStart_4703009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703016 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4703016 : Nat := 118140960795 + 4703016 * 2 ^ 59
def prefixEnd_4703016 : Nat := 4983230072969 + 3 ^ 40 * 4703016 * 2
def baseEnd_4703016 : Nat := 2414907733785676661971229

theorem tailTrace_4703016 : CollatzResearch.WordTrace tailWord_4703016 prefixEnd_4703016 2414907733785676661971229 := by
  unfold tailWord_4703016
  simp only [CollatzResearch.WordTrace]
  refine ⟨85766542764891859015500451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114355390353189145354000601 85766542764891859015500451)
  ·
    refine ⟨128649814147337788523250677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85766542764891859015500451 128649814147337788523250677)
    ·
      refine ⟨12060920076312917674054751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128649814147337788523250677 12060920076312917674054751)
      ·
        refine ⟨18091380114469376511082127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12060920076312917674054751 18091380114469376511082127)
        ·
          refine ⟨27137070171704064766623191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18091380114469376511082127 27137070171704064766623191)
          ·
            refine ⟨40705605257556097149934787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27137070171704064766623191 40705605257556097149934787)
            ·
              refine ⟨61058407886334145724902181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40705605257556097149934787 61058407886334145724902181)
              ·
                refine ⟨11448451478687652323419159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61058407886334145724902181 11448451478687652323419159)
                ·
                  refine ⟨17172677218031478485128739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11448451478687652323419159 17172677218031478485128739)
                  ·
                    refine ⟨25759015827047217727693109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17172677218031478485128739 25759015827047217727693109)
                    ·
                      refine ⟨2414907733785676661971229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25759015827047217727693109 2414907733785676661971229)
                      ·
                        rfl

theorem cell23_4703016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4703016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703016 prefixEnd_4703016 := by exact prefixLift 4703016
  have htrace : WordTrace (prefixWord ++ tailWord_4703016) baseStart_4703016 baseEnd_4703016 := by
    simpa [prefixWord, tailWord_4703016, baseEnd_4703016] using wordTrace_append hprefix tailTrace_4703016
  have hstable : (prefixWord ++ tailWord_4703016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703016).length < 2 ^ (prefixWord ++ tailWord_4703016).sum := by decide
  have hdescent : baseEnd_4703016 < baseStart_4703016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703026 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_4703026 : Nat := 118140960795 + 4703026 * 2 ^ 59
def prefixEnd_4703026 : Nat := 4983230072969 + 3 ^ 40 * 4703026 * 2
def baseEnd_4703026 : Nat := 2414912868592221622846183

theorem tailTrace_4703026 : CollatzResearch.WordTrace tailWord_4703026 prefixEnd_4703026 2414912868592221622846183 := by
  unfold tailWord_4703026
  simp only [CollatzResearch.WordTrace]
  refine ⟨42883362564936872434716233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114355633506498326492576621 42883362564936872434716233)
  ·
    refine ⟨32162521923702654326037175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42883362564936872434716233 32162521923702654326037175)
    ·
      refine ⟨48243782885553981489055763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32162521923702654326037175 48243782885553981489055763)
      ·
        refine ⟨72365674328330972233583645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48243782885553981489055763 72365674328330972233583645)
        ·
          refine ⟨27137127873124114587593867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72365674328330972233583645 27137127873124114587593867)
          ·
            refine ⟨40705691809686171881390801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27137127873124114587593867 40705691809686171881390801)
            ·
              refine ⟨30529268857264628911043101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40705691809686171881390801 30529268857264628911043101)
              ·
                refine ⟨11448475821474235841641163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30529268857264628911043101 11448475821474235841641163)
                ·
                  refine ⟨17172713732211353762461745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11448475821474235841641163 17172713732211353762461745)
                  ·
                    refine ⟨12879535299158515321846309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17172713732211353762461745 12879535299158515321846309)
                    ·
                      refine ⟨2414912868592221622846183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12879535299158515321846309 2414912868592221622846183)
                      ·
                        rfl

theorem cell23_4703026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_4703026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703026 prefixEnd_4703026 := by exact prefixLift 4703026
  have htrace : WordTrace (prefixWord ++ tailWord_4703026) baseStart_4703026 baseEnd_4703026 := by
    simpa [prefixWord, tailWord_4703026, baseEnd_4703026] using wordTrace_append hprefix tailTrace_4703026
  have hstable : (prefixWord ++ tailWord_4703026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703026).length < 2 ^ (prefixWord ++ tailWord_4703026).sum := by decide
  have hdescent : baseEnd_4703026 < baseStart_4703026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703030 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4703030 : Nat := 118140960795 + 4703030 * 2 ^ 59
def prefixEnd_4703030 : Nat := 4983230072969 + 3 ^ 40 * 4703030 * 2
def baseEnd_4703030 : Nat := 2414914922514839607196165

theorem tailTrace_4703030 : CollatzResearch.WordTrace tailWord_4703030 prefixEnd_4703030 2414914922514839607196165 := by
  unfold tailWord_4703030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10720849759483312401375659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114355730767821998948007029 10720849759483312401375659)
  ·
    refine ⟨16081274639224968602063489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10720849759483312401375659 16081274639224968602063489)
    ·
      refine ⟨12060955979418726451547617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16081274639224968602063489 12060955979418726451547617)
      ·
        refine ⟨9045716984564044838660713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12060955979418726451547617 9045716984564044838660713)
        ·
          refine ⟨6784287738423033628995535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9045716984564044838660713 6784287738423033628995535)
          ·
            refine ⟨10176431607634550443493303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6784287738423033628995535 10176431607634550443493303)
            ·
              refine ⟨15264647411451825665239955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10176431607634550443493303 15264647411451825665239955)
              ·
                refine ⟨22896971117177738497859933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15264647411451825665239955 22896971117177738497859933)
                ·
                  refine ⟨8586364168941651936697475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22896971117177738497859933 8586364168941651936697475)
                  ·
                    refine ⟨12879546253412477905046213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8586364168941651936697475 12879546253412477905046213)
                    ·
                      refine ⟨2414914922514839607196165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12879546253412477905046213 2414914922514839607196165)
                      ·
                        rfl

theorem cell23_4703030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4703030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703030 prefixEnd_4703030 := by exact prefixLift 4703030
  have htrace : WordTrace (prefixWord ++ tailWord_4703030) baseStart_4703030 baseEnd_4703030 := by
    simpa [prefixWord, tailWord_4703030, baseEnd_4703030] using wordTrace_append hprefix tailTrace_4703030
  have hstable : (prefixWord ++ tailWord_4703030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703030).length < 2 ^ (prefixWord ++ tailWord_4703030).sum := by decide
  have hdescent : baseEnd_4703030 < baseStart_4703030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703053 : List Nat := [1, 6, 1, 2, 3, 10]
def baseStart_4703053 : Nat := 118140960795 + 4703053 * 2 ^ 59
def prefixEnd_4703053 : Nat := 4983230072969 + 3 ^ 40 * 4703053 * 2
def baseEnd_4703053 : Nat := 9937970092880218177813

theorem tailTrace_4703053 : CollatzResearch.WordTrace tailWord_4703053 prefixEnd_4703053 9937970092880218177813 := by
  unfold tailWord_4703053
  simp only [CollatzResearch.WordTrace]
  refine ⟨171534435030649673350097813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114356290020433115566731875 171534435030649673350097813)
  ·
    refine ⟨8040676642061703438285835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 171534435030649673350097813 8040676642061703438285835)
    ·
      refine ⟨12061014963092555157428753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8040676642061703438285835 12061014963092555157428753)
      ·
        refine ⟨9045761222319416368071565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12061014963092555157428753 9045761222319416368071565)
        ·
          refine ⟨3392160458369781138026837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9045761222319416368071565 3392160458369781138026837)
          ·
            refine ⟨9937970092880218177813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3392160458369781138026837 9937970092880218177813)
            ·
              rfl

theorem cell23_4703053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 10].length) (baseStart_4703053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703053 prefixEnd_4703053 := by exact prefixLift 4703053
  have htrace : WordTrace (prefixWord ++ tailWord_4703053) baseStart_4703053 baseEnd_4703053 := by
    simpa [prefixWord, tailWord_4703053, baseEnd_4703053] using wordTrace_append hprefix tailTrace_4703053
  have hstable : (prefixWord ++ tailWord_4703053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703053).length < 2 ^ (prefixWord ++ tailWord_4703053).sum := by decide
  have hdescent : baseEnd_4703053 < baseStart_4703053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703059 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5]
def baseStart_4703059 : Nat := 118140960795 + 4703059 * 2 ^ 59
def prefixEnd_4703059 : Nat := 4983230072969 + 3 ^ 40 * 4703059 * 2
def baseEnd_4703059 : Nat := 2414929813453819993733531

theorem tailTrace_4703059 : CollatzResearch.WordTrace tailWord_4703059 prefixEnd_4703059 2414929813453819993733531 := by
  unfold tailWord_4703059
  simp only [CollatzResearch.WordTrace]
  refine ⟨171534653868627936374816231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114356435912418624249877487 171534653868627936374816231)
  ·
    refine ⟨257301980802941904562224347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171534653868627936374816231 257301980802941904562224347)
    ·
      refine ⟨385952971204412856843336521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257301980802941904562224347 385952971204412856843336521)
      ·
        refine ⟨289464728403309642632502391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385952971204412856843336521 289464728403309642632502391)
        ·
          refine ⟨434197092604964463948753587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289464728403309642632502391 434197092604964463948753587)
          ·
            refine ⟨651295638907446695923130381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434197092604964463948753587 651295638907446695923130381)
            ·
              refine ⟨244235864590292510971173893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 651295638907446695923130381 244235864590292510971173893)
              ·
                refine ⟨45794224610679845807095105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244235864590292510971173893 45794224610679845807095105)
                ·
                  refine ⟨34345668458009884355321329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45794224610679845807095105 34345668458009884355321329)
                  ·
                    refine ⟨25759251343507413266490997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34345668458009884355321329 25759251343507413266490997)
                    ·
                      refine ⟨2414929813453819993733531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25759251343507413266490997 2414929813453819993733531)
                      ·
                        rfl

theorem cell23_4703059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_4703059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703059 prefixEnd_4703059 := by exact prefixLift 4703059
  have htrace : WordTrace (prefixWord ++ tailWord_4703059) baseStart_4703059 baseEnd_4703059 := by
    simpa [prefixWord, tailWord_4703059, baseEnd_4703059] using wordTrace_append hprefix tailTrace_4703059
  have hstable : (prefixWord ++ tailWord_4703059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703059).length < 2 ^ (prefixWord ++ tailWord_4703059).sum := by decide
  have hdescent : baseEnd_4703059 < baseStart_4703059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703080 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4703080 : Nat := 118140960795 + 4703080 * 2 ^ 59
def prefixEnd_4703080 : Nat := 4983230072969 + 3 ^ 40 * 4703080 * 2
def baseEnd_4703080 : Nat := 2414940596547564411570935

theorem tailTrace_4703080 : CollatzResearch.WordTrace tailWord_4703080 prefixEnd_4703080 2414940596547564411570935 := by
  unfold tailWord_4703080
  simp only [CollatzResearch.WordTrace]
  refine ⟨85767709900775928480665347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114356946534367904640887129 85767709900775928480665347)
  ·
    refine ⟨128651564851163892720998021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85767709900775928480665347 128651564851163892720998021)
    ·
      refine ⟨24122168409593229885187129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128651564851163892720998021 24122168409593229885187129)
      ·
        refine ⟨18091626307194922413890347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24122168409593229885187129 18091626307194922413890347)
        ·
          refine ⟨27137439460792383620835521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18091626307194922413890347 27137439460792383620835521)
          ·
            refine ⟨20353079595594287715626641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27137439460792383620835521 20353079595594287715626641)
            ·
              refine ⟨15264809696695715786719981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20353079595594287715626641 15264809696695715786719981)
              ·
                refine ⟨5724303636260893420019993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15264809696695715786719981 5724303636260893420019993)
                ·
                  refine ⟨4293227727195670065014995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5724303636260893420019993 4293227727195670065014995)
                  ·
                    refine ⟨6439841590793505097522493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4293227727195670065014995 6439841590793505097522493)
                    ·
                      refine ⟨2414940596547564411570935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6439841590793505097522493 2414940596547564411570935)
                      ·
                        rfl

theorem cell23_4703080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4703080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703080 prefixEnd_4703080 := by exact prefixLift 4703080
  have htrace : WordTrace (prefixWord ++ tailWord_4703080) baseStart_4703080 baseEnd_4703080 := by
    simpa [prefixWord, tailWord_4703080, baseEnd_4703080] using wordTrace_append hprefix tailTrace_4703080
  have hstable : (prefixWord ++ tailWord_4703080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703080).length < 2 ^ (prefixWord ++ tailWord_4703080).sum := by decide
  have hdescent : baseEnd_4703080 < baseStart_4703080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703103 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 1, 4, 2]
def baseStart_4703103 : Nat := 118140960795 + 4703103 * 2 ^ 59
def prefixEnd_4703103 : Nat := 4983230072969 + 3 ^ 40 * 4703103 * 2
def baseEnd_4703103 : Nat := 2414952406602617821583329

theorem tailTrace_4703103 : CollatzResearch.WordTrace tailWord_4703103 prefixEnd_4703103 2414952406602617821583329 := by
  unfold tailWord_4703103
  simp only [CollatzResearch.WordTrace]
  refine ⟨171536258680468531889417963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114357505786979021259611975 171536258680468531889417963)
  ·
    refine ⟨257304388020702797834126945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171536258680468531889417963 257304388020702797834126945)
    ·
      refine ⟨192978291015527098375595209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257304388020702797834126945 192978291015527098375595209)
      ·
        refine ⟨144733718261645323781696407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192978291015527098375595209 144733718261645323781696407)
        ·
          refine ⟨217100577392467985672544611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144733718261645323781696407 217100577392467985672544611)
          ·
            refine ⟨325650866088701978508816917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217100577392467985672544611 325650866088701978508816917)
            ·
              refine ⟨15264884347907905242600793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 325650866088701978508816917 15264884347907905242600793)
              ·
                refine ⟨11448663260930928931950595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15264884347907905242600793 11448663260930928931950595)
                ·
                  refine ⟨17172994891396393397925893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11448663260930928931950595 17172994891396393397925893)
                  ·
                    refine ⟨3219936542136823762111105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17172994891396393397925893 3219936542136823762111105)
                    ·
                      refine ⟨2414952406602617821583329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219936542136823762111105 2414952406602617821583329)
                      ·
                        rfl

theorem cell23_4703103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_4703103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703103 prefixEnd_4703103 := by exact prefixLift 4703103
  have htrace : WordTrace (prefixWord ++ tailWord_4703103) baseStart_4703103 baseEnd_4703103 := by
    simpa [prefixWord, tailWord_4703103, baseEnd_4703103] using wordTrace_append hprefix tailTrace_4703103
  have hstable : (prefixWord ++ tailWord_4703103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703103).length < 2 ^ (prefixWord ++ tailWord_4703103).sum := by decide
  have hdescent : baseEnd_4703103 < baseStart_4703103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703116 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_4703116 : Nat := 118140960795 + 4703116 * 2 ^ 59
def prefixEnd_4703116 : Nat := 4983230072969 + 3 ^ 40 * 4703116 * 2
def baseEnd_4703116 : Nat := 2414959081851126270720769

theorem tailTrace_4703116 : CollatzResearch.WordTrace tailWord_4703116 prefixEnd_4703116 2414959081851126270720769 := by
  unfold tailWord_4703116
  simp only [CollatzResearch.WordTrace]
  refine ⟨85768366414710717554820601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114357821886280956739760801 85768366414710717554820601)
  ·
    refine ⟨64326274811033038166115451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85768366414710717554820601 64326274811033038166115451)
    ·
      refine ⟨96489412216549557249173177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64326274811033038166115451 96489412216549557249173177)
      ·
        refine ⟨72367059162412167936879883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96489412216549557249173177 72367059162412167936879883)
        ·
          refine ⟨108550588743618251905319825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72367059162412167936879883 108550588743618251905319825)
          ·
            refine ⟨81412941557713688928989869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108550588743618251905319825 81412941557713688928989869)
            ·
              refine ⟨30529853084142633348371201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81412941557713688928989869 30529853084142633348371201)
              ·
                refine ⟨22897389813106975011278401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30529853084142633348371201 22897389813106975011278401)
                ·
                  refine ⟨17173042359830231258458801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22897389813106975011278401 17173042359830231258458801)
                  ·
                    refine ⟨12879781769872673443844101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17173042359830231258458801 12879781769872673443844101)
                    ·
                      refine ⟨2414959081851126270720769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12879781769872673443844101 2414959081851126270720769)
                      ·
                        rfl

theorem cell23_4703116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_4703116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703116 prefixEnd_4703116 := by exact prefixLift 4703116
  have htrace : WordTrace (prefixWord ++ tailWord_4703116) baseStart_4703116 baseEnd_4703116 := by
    simpa [prefixWord, tailWord_4703116, baseEnd_4703116] using wordTrace_append hprefix tailTrace_4703116
  have hstable : (prefixWord ++ tailWord_4703116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703116).length < 2 ^ (prefixWord ++ tailWord_4703116).sum := by decide
  have hdescent : baseEnd_4703116 < baseStart_4703116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703137 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4703137 : Nat := 118140960795 + 4703137 * 2 ^ 59
def prefixEnd_4703137 : Nat := 4983230072969 + 3 ^ 40 * 4703137 * 2
def baseEnd_4703137 : Nat := 2414969864944870688558173

theorem tailTrace_4703137 : CollatzResearch.WordTrace tailWord_4703137 prefixEnd_4703137 2414969864944870688558173 := by
  unfold tailWord_4703137
  simp only [CollatzResearch.WordTrace]
  refine ⟨171537498762345355696155665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114358332508230237130770443 171537498762345355696155665)
  ·
    refine ⟨128653124071759016772116749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171537498762345355696155665 128653124071759016772116749)
    ·
      refine ⟨48244921526909631289543781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128653124071759016772116749 48244921526909631289543781)
      ·
        refine ⟨9045922786295555866789459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48244921526909631289543781 9045922786295555866789459)
        ·
          refine ⟨13568884179443333800184189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9045922786295555866789459 13568884179443333800184189)
          ·
            refine ⟨5088331567291250175069071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13568884179443333800184189 5088331567291250175069071)
            ·
              refine ⟨7632497350936875262603607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088331567291250175069071 7632497350936875262603607)
              ·
                refine ⟨11448746026405312893905411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7632497350936875262603607 11448746026405312893905411)
                ·
                  refine ⟨17173119039607969340858117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11448746026405312893905411 17173119039607969340858117)
                  ·
                    refine ⟨3219959819926494251410897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17173119039607969340858117 3219959819926494251410897)
                    ·
                      refine ⟨2414969864944870688558173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3219959819926494251410897 2414969864944870688558173)
                      ·
                        rfl

theorem cell23_4703137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4703137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703137 prefixEnd_4703137 := by exact prefixLift 4703137
  have htrace : WordTrace (prefixWord ++ tailWord_4703137) baseStart_4703137 baseEnd_4703137 := by
    simpa [prefixWord, tailWord_4703137, baseEnd_4703137] using wordTrace_append hprefix tailTrace_4703137
  have hstable : (prefixWord ++ tailWord_4703137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703137).length < 2 ^ (prefixWord ++ tailWord_4703137).sum := by decide
  have hdescent : baseEnd_4703137 < baseStart_4703137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703160 : List Nat := [2, 1, 2, 1, 2, 6, 1, 3, 5]
def baseStart_4703160 : Nat := 118140960795 + 4703160 * 2 ^ 59
def prefixEnd_4703160 : Nat := 4983230072969 + 3 ^ 40 * 4703160 * 2
def baseEnd_4703160 : Nat := 268331297222213788730063

theorem tailTrace_4703160 : CollatzResearch.WordTrace tailWord_4703160 prefixEnd_4703160 268331297222213788730063 := by
  unfold tailWord_4703160
  simp only [CollatzResearch.WordTrace]
  refine ⟨85769168820631015312121467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114358891760841353749495289 85769168820631015312121467)
  ·
    refine ⟨128653753230946522968182201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85769168820631015312121467 128653753230946522968182201)
    ·
      refine ⟨96490314923209892226136651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128653753230946522968182201 96490314923209892226136651)
      ·
        refine ⟨144735472384814838339204977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96490314923209892226136651 144735472384814838339204977)
        ·
          refine ⟨108551604288611128754403733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144735472384814838339204977 108551604288611128754403733)
          ·
            refine ⟨5088356451028646660362675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108551604288611128754403733 5088356451028646660362675)
            ·
              refine ⟨7632534676542969990544013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088356451028646660362675 7632534676542969990544013)
              ·
                refine ⟨2862200503703613746454005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7632534676542969990544013 2862200503703613746454005)
                ·
                  refine ⟨268331297222213788730063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862200503703613746454005 268331297222213788730063)
                  ·
                    rfl

theorem cell23_4703160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 5].length) (baseStart_4703160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703160 prefixEnd_4703160 := by exact prefixLift 4703160
  have htrace : WordTrace (prefixWord ++ tailWord_4703160) baseStart_4703160 baseEnd_4703160 := by
    simpa [prefixWord, tailWord_4703160, baseEnd_4703160] using wordTrace_append hprefix tailTrace_4703160
  have hstable : (prefixWord ++ tailWord_4703160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703160).length < 2 ^ (prefixWord ++ tailWord_4703160).sum := by decide
  have hdescent : baseEnd_4703160 < baseStart_4703160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703203 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 5, 4]
def baseStart_4703203 : Nat := 118140960795 + 4703203 * 2 ^ 59
def prefixEnd_4703203 : Nat := 4983230072969 + 3 ^ 40 * 4703203 * 2
def baseEnd_4703203 : Nat := 805001251556022476777623

theorem tailTrace_4703203 : CollatzResearch.WordTrace tailWord_4703203 prefixEnd_4703203 805001251556022476777623 := by
  unfold tailWord_4703203
  simp only [CollatzResearch.WordTrace]
  refine ⟨171539905980106248968058263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114359937320070832645372175 171539905980106248968058263)
  ·
    refine ⟨257309858970159373452087395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171539905980106248968058263 257309858970159373452087395)
    ·
      refine ⟨385964788455239060178131093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257309858970159373452087395 385964788455239060178131093)
      ·
        refine ⟨18092099458839330945849895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 385964788455239060178131093 18092099458839330945849895)
        ·
          refine ⟨27138149188258996418774843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18092099458839330945849895 27138149188258996418774843)
          ·
            refine ⟨40707223782388494628162265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27138149188258996418774843 40707223782388494628162265)
            ·
              refine ⟨30530417836791370971121699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40707223782388494628162265 30530417836791370971121699)
              ·
                refine ⟨45795626755187056456682549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30530417836791370971121699 45795626755187056456682549)
                ·
                  refine ⟨4293340008298786542813989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45795626755187056456682549 4293340008298786542813989)
                  ·
                    refine ⟨805001251556022476777623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293340008298786542813989 805001251556022476777623)
                    ·
                      rfl

theorem cell23_4703203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 4].length) (baseStart_4703203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703203 prefixEnd_4703203 := by exact prefixLift 4703203
  have htrace : WordTrace (prefixWord ++ tailWord_4703203) baseStart_4703203 baseEnd_4703203 := by
    simpa [prefixWord, tailWord_4703203, baseEnd_4703203] using wordTrace_append hprefix tailTrace_4703203
  have hstable : (prefixWord ++ tailWord_4703203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703203).length < 2 ^ (prefixWord ++ tailWord_4703203).sum := by decide
  have hdescent : baseEnd_4703203 < baseStart_4703203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703210 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_4703210 : Nat := 118140960795 + 4703210 * 2 ^ 59
def prefixEnd_4703210 : Nat := 4983230072969 + 3 ^ 40 * 4703210 * 2
def baseEnd_4703210 : Nat := 2415007349032648902945337

theorem tailTrace_4703210 : CollatzResearch.WordTrace tailWord_4703210 prefixEnd_4703210 2415007349032648902945337 := by
  unfold tailWord_4703210
  simp only [CollatzResearch.WordTrace]
  refine ⟨42885040322770222290890771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114360107527387259442375389 42885040322770222290890771)
  ·
    refine ⟨64327560484155333436336157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42885040322770222290890771 64327560484155333436336157)
    ·
      refine ⟨24122835181558250038626059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64327560484155333436336157 24122835181558250038626059)
      ·
        refine ⟨36184252772337375057939089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24122835181558250038626059 36184252772337375057939089)
        ·
          refine ⟨27138189579253031293454317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36184252772337375057939089 27138189579253031293454317)
          ·
            refine ⟨10176821092219886735045369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27138189579253031293454317 10176821092219886735045369)
            ·
              refine ⟨7632615819164915051284027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10176821092219886735045369 7632615819164915051284027)
              ·
                refine ⟨11448923728747372576926041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7632615819164915051284027 11448923728747372576926041)
                ·
                  refine ⟨8586692796560529432694531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11448923728747372576926041 8586692796560529432694531)
                  ·
                    refine ⟨12880039194840794149041797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8586692796560529432694531 12880039194840794149041797)
                    ·
                      refine ⟨2415007349032648902945337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12880039194840794149041797 2415007349032648902945337)
                      ·
                        rfl

theorem cell23_4703210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_4703210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703210 prefixEnd_4703210 := by exact prefixLift 4703210
  have htrace : WordTrace (prefixWord ++ tailWord_4703210) baseStart_4703210 baseEnd_4703210 := by
    simpa [prefixWord, tailWord_4703210, baseEnd_4703210] using wordTrace_append hprefix tailTrace_4703210
  have hstable : (prefixWord ++ tailWord_4703210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703210).length < 2 ^ (prefixWord ++ tailWord_4703210).sum := by decide
  have hdescent : baseEnd_4703210 < baseStart_4703210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703233 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 6]
def baseStart_4703233 : Nat := 118140960795 + 4703233 * 2 ^ 59
def prefixEnd_4703233 : Nat := 4983230072969 + 3 ^ 40 * 4703233 * 2
def baseEnd_4703233 : Nat := 268335462120855812550859

theorem tailTrace_4703233 : CollatzResearch.WordTrace tailWord_4703233 prefixEnd_4703233 268335462120855812550859 := by
  unfold tailWord_4703233
  simp only [CollatzResearch.WordTrace]
  refine ⟨171541000169997564091650353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114360666779998376061100235 171541000169997564091650353)
  ·
    refine ⟨128655750127498173068737765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171541000169997564091650353 128655750127498173068737765)
    ·
      refine ⟨24122953148905907450388331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128655750127498173068737765 24122953148905907450388331)
      ·
        refine ⟨36184429723358861175582497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24122953148905907450388331 36184429723358861175582497)
        ·
          refine ⟨27138322292519145881686873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36184429723358861175582497 27138322292519145881686873)
          ·
            refine ⟨20353741719389359411265155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27138322292519145881686873 20353741719389359411265155)
            ·
              refine ⟨30530612579084039116897733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20353741719389359411265155 30530612579084039116897733)
              ·
                refine ⟨5724489858578257334418325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30530612579084039116897733 5724489858578257334418325)
                ·
                  refine ⟨268335462120855812550859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5724489858578257334418325 268335462120855812550859)
                  ·
                    rfl

theorem cell23_4703233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 6].length) (baseStart_4703233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703233 prefixEnd_4703233 := by exact prefixLift 4703233
  have htrace : WordTrace (prefixWord ++ tailWord_4703233) baseStart_4703233 baseEnd_4703233 := by
    simpa [prefixWord, tailWord_4703233, baseEnd_4703233] using wordTrace_append hprefix tailTrace_4703233
  have hstable : (prefixWord ++ tailWord_4703233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703233).length < 2 ^ (prefixWord ++ tailWord_4703233).sum := by decide
  have hdescent : baseEnd_4703233 < baseStart_4703233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703263 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 3, 5]
def baseStart_4703263 : Nat := 118140960795 + 4703263 * 2 ^ 59
def prefixEnd_4703263 : Nat := 4983230072969 + 3 ^ 40 * 4703263 * 2
def baseEnd_4703263 : Nat := 805011521169112398527531

theorem tailTrace_4703263 : CollatzResearch.WordTrace tailWord_4703263 prefixEnd_4703263 805011521169112398527531 := by
  unfold tailWord_4703263
  simp only [CollatzResearch.WordTrace]
  refine ⟨171542094359888879215242443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114361396239925919476828295 171542094359888879215242443)
  ·
    refine ⟨257313141539833318822863665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171542094359888879215242443 257313141539833318822863665)
    ·
      refine ⟨192984856154874989117147749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257313141539833318822863665 192984856154874989117147749)
      ·
        refine ⟨36184660529039060459465203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192984856154874989117147749 36184660529039060459465203)
        ·
          refine ⟨54276990793558590689197805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36184660529039060459465203 54276990793558590689197805)
          ·
            refine ⟨20353871547584471508449177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54276990793558590689197805 20353871547584471508449177)
            ·
              refine ⟨15265403660688353631336883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20353871547584471508449177 15265403660688353631336883)
              ·
                refine ⟨22898105491032530447005325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15265403660688353631336883 22898105491032530447005325)
                ·
                  refine ⟨8586789559137198917626997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22898105491032530447005325 8586789559137198917626997)
                  ·
                    refine ⟨805011521169112398527531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8586789559137198917626997 805011521169112398527531)
                    ·
                      rfl

theorem cell23_4703263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_4703263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703263 prefixEnd_4703263 := by exact prefixLift 4703263
  have htrace : WordTrace (prefixWord ++ tailWord_4703263) baseStart_4703263 baseEnd_4703263 := by
    simpa [prefixWord, tailWord_4703263, baseEnd_4703263] using wordTrace_append hprefix tailTrace_4703263
  have hstable : (prefixWord ++ tailWord_4703263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703263).length < 2 ^ (prefixWord ++ tailWord_4703263).sum := by decide
  have hdescent : baseEnd_4703263 < baseStart_4703263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703264 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4703264 : Nat := 118140960795 + 4703264 * 2 ^ 59
def prefixEnd_4703264 : Nat := 4983230072969 + 3 ^ 40 * 4703264 * 2
def baseEnd_4703264 : Nat := 2415035076987991691670089

theorem tailTrace_4703264 : CollatzResearch.WordTrace tailWord_4703264 prefixEnd_4703264 2415035076987991691670089 := by
  unfold tailWord_4703264
  simp only [CollatzResearch.WordTrace]
  refine ⟨85771065416442628193014423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114361420555256837590685897 85771065416442628193014423)
  ·
    refine ⟨128656598124663942289521635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85771065416442628193014423 128656598124663942289521635)
    ·
      refine ⟨192984897186995913434282453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128656598124663942289521635 192984897186995913434282453)
      ·
        refine ⟨4523083527820216721115995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 192984897186995913434282453 4523083527820216721115995)
        ·
          refine ⟨6784625291730325081673993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523083527820216721115995 6784625291730325081673993)
          ·
            refine ⟨5088468968797743811255495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6784625291730325081673993 5088468968797743811255495)
            ·
              refine ⟨7632703453196615716883243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088468968797743811255495 7632703453196615716883243)
              ·
                refine ⟨11449055179794923575324865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7632703453196615716883243 11449055179794923575324865)
                ·
                  refine ⟨8586791384846192681493649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11449055179794923575324865 8586791384846192681493649)
                  ·
                    refine ⟨6440093538634644511120237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8586791384846192681493649 6440093538634644511120237)
                    ·
                      refine ⟨2415035076987991691670089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6440093538634644511120237 2415035076987991691670089)
                      ·
                        rfl

theorem cell23_4703264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4703264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703264 prefixEnd_4703264 := by exact prefixLift 4703264
  have htrace : WordTrace (prefixWord ++ tailWord_4703264) baseStart_4703264 baseEnd_4703264 := by
    simpa [prefixWord, tailWord_4703264, baseEnd_4703264] using wordTrace_append hprefix tailTrace_4703264
  have hstable : (prefixWord ++ tailWord_4703264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703264).length < 2 ^ (prefixWord ++ tailWord_4703264).sum := by decide
  have hdescent : baseEnd_4703264 < baseStart_4703264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703294 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_4703294 : Nat := 118140960795 + 4703294 * 2 ^ 59
def prefixEnd_4703294 : Nat := 4983230072969 + 3 ^ 40 * 4703294 * 2
def baseEnd_4703294 : Nat := 2415050481407626574294951

theorem tailTrace_4703294 : CollatzResearch.WordTrace tailWord_4703294 prefixEnd_4703294 2415050481407626574294951 := by
  unfold tailWord_4703294
  simp only [CollatzResearch.WordTrace]
  refine ⟨21442903127847071438702617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114362150015184381006413957 21442903127847071438702617)
  ·
    refine ⟨16082177345885303579026963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21442903127847071438702617 16082177345885303579026963)
    ·
      refine ⟨24123266018827955368540445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16082177345885303579026963 24123266018827955368540445)
      ·
        refine ⟨9046224757060483263202667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24123266018827955368540445 9046224757060483263202667)
        ·
          refine ⟨13569337135590724894804001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9046224757060483263202667 13569337135590724894804001)
          ·
            refine ⟨10177002851693043671103001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13569337135590724894804001 10177002851693043671103001)
            ·
              refine ⟨7632752138769782753327251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10177002851693043671103001 7632752138769782753327251)
              ·
                refine ⟨11449128208154674129990877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7632752138769782753327251 11449128208154674129990877)
                ·
                  refine ⟨4293423078058002798746579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11449128208154674129990877 4293423078058002798746579)
                  ·
                    refine ⟨6440134617087004198119869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4293423078058002798746579 6440134617087004198119869)
                    ·
                      refine ⟨2415050481407626574294951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6440134617087004198119869 2415050481407626574294951)
                      ·
                        rfl

theorem cell23_4703294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_4703294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703294 prefixEnd_4703294 := by exact prefixLift 4703294
  have htrace : WordTrace (prefixWord ++ tailWord_4703294) baseStart_4703294 baseEnd_4703294 := by
    simpa [prefixWord, tailWord_4703294, baseEnd_4703294] using wordTrace_append hprefix tailTrace_4703294
  have hstable : (prefixWord ++ tailWord_4703294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703294).length < 2 ^ (prefixWord ++ tailWord_4703294).sum := by decide
  have hdescent : baseEnd_4703294 < baseStart_4703294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703303 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_4703303 : Nat := 118140960795 + 4703303 * 2 ^ 59
def prefixEnd_4703303 : Nat := 4983230072969 + 3 ^ 40 * 4703303 * 2
def baseEnd_4703303 : Nat := 2415055102733517039082409

theorem tailTrace_4703303 : CollatzResearch.WordTrace tailWord_4703303 prefixEnd_4703303 2415055102733517039082409 := by
  unfold tailWord_4703303
  simp only [CollatzResearch.WordTrace]
  refine ⟨171543553279743966046698563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114362368853162644031132375 171543553279743966046698563)
  ·
    refine ⟨257315329919615949070047845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171543553279743966046698563 257315329919615949070047845)
    ·
      refine ⟨48246624359927990450633971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257315329919615949070047845 48246624359927990450633971)
      ·
        refine ⟨72369936539891985675950957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48246624359927990450633971 72369936539891985675950957)
        ·
          refine ⟨27138726202459494628481609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72369936539891985675950957 27138726202459494628481609)
          ·
            refine ⟨20354044651844620971361207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27138726202459494628481609 20354044651844620971361207)
            ·
              refine ⟨30531066977766931457041811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20354044651844620971361207 30531066977766931457041811)
              ·
                refine ⟨45796600466650397185562717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30531066977766931457041811 45796600466650397185562717)
                ·
                  refine ⟨17173725174993898944586019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45796600466650397185562717 17173725174993898944586019)
                  ·
                    refine ⟨25760587762490848416879029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17173725174993898944586019 25760587762490848416879029)
                    ·
                      refine ⟨2415055102733517039082409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25760587762490848416879029 2415055102733517039082409)
                      ·
                        rfl

theorem cell23_4703303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_4703303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703303 prefixEnd_4703303 := by exact prefixLift 4703303
  have htrace : WordTrace (prefixWord ++ tailWord_4703303) baseStart_4703303 baseEnd_4703303 := by
    simpa [prefixWord, tailWord_4703303, baseEnd_4703303] using wordTrace_append hprefix tailTrace_4703303
  have hstable : (prefixWord ++ tailWord_4703303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703303).length < 2 ^ (prefixWord ++ tailWord_4703303).sum := by decide
  have hdescent : baseEnd_4703303 < baseStart_4703303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703317 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_4703317 : Nat := 118140960795 + 4703317 * 2 ^ 59
def prefixEnd_4703317 : Nat := 4983230072969 + 3 ^ 40 * 4703317 * 2
def baseEnd_4703317 : Nat := 2415062291462679984307345

theorem tailTrace_4703317 : CollatzResearch.WordTrace tailWord_4703317 prefixEnd_4703317 2415062291462679984307345 := by
  unfold tailWord_4703317
  simp only [CollatzResearch.WordTrace]
  refine ⟨171544063901693246437708205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114362709267795497625138803 171544063901693246437708205)
  ·
    refine ⟨64329023963134967414140577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171544063901693246437708205 64329023963134967414140577)
    ·
      refine ⟨48246767972351225560605433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64329023963134967414140577 48246767972351225560605433)
      ·
        refine ⟨36185075979263419170454075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48246767972351225560605433 36185075979263419170454075)
        ·
          refine ⟨54277613968895128755681113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36185075979263419170454075 54277613968895128755681113)
          ·
            refine ⟨40708210476671346566760835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54277613968895128755681113 40708210476671346566760835)
            ·
              refine ⟨61062315715007019850141253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40708210476671346566760835 61062315715007019850141253)
              ·
                refine ⟨11449184196563816221901485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61062315715007019850141253 11449184196563816221901485)
                ·
                  refine ⟨4293444073711431083213057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11449184196563816221901485 4293444073711431083213057)
                  ·
                    refine ⟨3220083055283573312409793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4293444073711431083213057 3220083055283573312409793)
                    ·
                      refine ⟨2415062291462679984307345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220083055283573312409793 2415062291462679984307345)
                      ·
                        rfl

theorem cell23_4703317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_4703317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703317 prefixEnd_4703317 := by exact prefixLift 4703317
  have htrace : WordTrace (prefixWord ++ tailWord_4703317) baseStart_4703317 baseEnd_4703317 := by
    simpa [prefixWord, tailWord_4703317, baseEnd_4703317] using wordTrace_append hprefix tailTrace_4703317
  have hstable : (prefixWord ++ tailWord_4703317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703317).length < 2 ^ (prefixWord ++ tailWord_4703317).sum := by decide
  have hdescent : baseEnd_4703317 < baseStart_4703317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703351 : List Nat := [1, 1, 3, 1, 1, 4, 5, 2, 1, 2, 2]
def baseStart_4703351 : Nat := 118140960795 + 4703351 * 2 ^ 59
def prefixEnd_4703351 : Nat := 4983230072969 + 3 ^ 40 * 4703351 * 2
def baseEnd_4703351 : Nat := 2415079749804932851282189

theorem tailTrace_4703351 : CollatzResearch.WordTrace tailWord_4703351 prefixEnd_4703351 2415079749804932851282189 := by
  unfold tailWord_4703351
  simp only [CollatzResearch.WordTrace]
  refine ⟨171545303983570070244445907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114363535989046713496297271 171545303983570070244445907)
  ·
    refine ⟨257317955975355105366668861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171545303983570070244445907 257317955975355105366668861)
    ·
      refine ⟨96494233490758164512500823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257317955975355105366668861 96494233490758164512500823)
      ·
        refine ⟨144741350236137246768751235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96494233490758164512500823 144741350236137246768751235)
        ·
          refine ⟨217112025354205870153126853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144741350236137246768751235 217112025354205870153126853)
          ·
            refine ⟨40708504753913600653711285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217112025354205870153126853 40708504753913600653711285)
            ·
              refine ⟨3816422320679400061285433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40708504753913600653711285 3816422320679400061285433)
              ·
                refine ⟨2862316740509550045964075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816422320679400061285433 2862316740509550045964075)
                ·
                  refine ⟨4293475110764325068946113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862316740509550045964075 4293475110764325068946113)
                  ·
                    refine ⟨3220106333073243801709585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4293475110764325068946113 3220106333073243801709585)
                    ·
                      refine ⟨2415079749804932851282189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220106333073243801709585 2415079749804932851282189)
                      ·
                        rfl

theorem cell23_4703351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_4703351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703351 prefixEnd_4703351 := by exact prefixLift 4703351
  have htrace : WordTrace (prefixWord ++ tailWord_4703351) baseStart_4703351 baseEnd_4703351 := by
    simpa [prefixWord, tailWord_4703351, baseEnd_4703351] using wordTrace_append hprefix tailTrace_4703351
  have hstable : (prefixWord ++ tailWord_4703351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703351).length < 2 ^ (prefixWord ++ tailWord_4703351).sum := by decide
  have hdescent : baseEnd_4703351 < baseStart_4703351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703407 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 4, 2, 2]
def baseStart_4703407 : Nat := 118140960795 + 4703407 * 2 ^ 59
def prefixEnd_4703407 : Nat := 4983230072969 + 3 ^ 40 * 4703407 * 2
def baseEnd_4703407 : Nat := 2415108504721584632181931

theorem tailTrace_4703407 : CollatzResearch.WordTrace tailWord_4703407 prefixEnd_4703407 2415108504721584632181931 := by
  unfold tailWord_4703407
  simp only [CollatzResearch.WordTrace]
  refine ⟨171547346471367191808484475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114364897647578127872322983 171547346471367191808484475)
  ·
    refine ⟨257321019707050787712726713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171547346471367191808484475 257321019707050787712726713)
    ·
      refine ⟨192990764780288090784545035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257321019707050787712726713 192990764780288090784545035)
      ·
        refine ⟨289486147170432136176817553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192990764780288090784545035 289486147170432136176817553)
        ·
          refine ⟨217114610377824102132613165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289486147170432136176817553 217114610377824102132613165)
          ·
            refine ⟨81417978891684038299729937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217114610377824102132613165 81417978891684038299729937)
            ·
              refine ⟨61063484168763028724797453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81417978891684038299729937 61063484168763028724797453)
              ·
                refine ⟨22898806563286135771799045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61063484168763028724797453 22898806563286135771799045)
                ·
                  refine ⟨4293526230616150457212321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22898806563286135771799045 4293526230616150457212321)
                  ·
                    refine ⟨3220144672962112842909241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4293526230616150457212321 3220144672962112842909241)
                    ·
                      refine ⟨2415108504721584632181931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220144672962112842909241 2415108504721584632181931)
                      ·
                        rfl

theorem cell23_4703407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 2, 2].length) (baseStart_4703407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703407 prefixEnd_4703407 := by exact prefixLift 4703407
  have htrace : WordTrace (prefixWord ++ tailWord_4703407) baseStart_4703407 baseEnd_4703407 := by
    simpa [prefixWord, tailWord_4703407, baseEnd_4703407] using wordTrace_append hprefix tailTrace_4703407
  have hstable : (prefixWord ++ tailWord_4703407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703407).length < 2 ^ (prefixWord ++ tailWord_4703407).sum := by decide
  have hdescent : baseEnd_4703407 < baseStart_4703407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703410 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_4703410 : Nat := 118140960795 + 4703410 * 2 ^ 59
def prefixEnd_4703410 : Nat := 4983230072969 + 3 ^ 40 * 4703410 * 2
def baseEnd_4703410 : Nat := 2415110045163548120444417

theorem tailTrace_4703410 : CollatzResearch.WordTrace tailWord_4703410 prefixEnd_4703410 2415110045163548120444417 := by
  unfold tailWord_4703410
  simp only [CollatzResearch.WordTrace]
  refine ⟨42886863972589080830210921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114364970593570882213895789 42886863972589080830210921)
  ·
    refine ⟨32165147979441810622658191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42886863972589080830210921 32165147979441810622658191)
    ·
      refine ⟨48247721969162715933987287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32165147979441810622658191 48247721969162715933987287)
      ·
        refine ⟨72371582953744073900980931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48247721969162715933987287 72371582953744073900980931)
        ·
          refine ⟨108557374430616110851471397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72371582953744073900980931 108557374430616110851471397)
          ·
            refine ⟨20354507705740520784650887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108557374430616110851471397 20354507705740520784650887)
            ·
              refine ⟨30531761558610781176976331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20354507705740520784650887 30531761558610781176976331)
              ·
                refine ⟨45797642337916171765464497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30531761558610781176976331 45797642337916171765464497)
                ·
                  refine ⟨34348231753437128824098373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45797642337916171765464497 34348231753437128824098373)
                  ·
                    refine ⟨6440293453769461654518445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34348231753437128824098373 6440293453769461654518445)
                    ·
                      refine ⟨2415110045163548120444417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6440293453769461654518445 2415110045163548120444417)
                      ·
                        rfl

theorem cell23_4703410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_4703410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703410 prefixEnd_4703410 := by exact prefixLift 4703410
  have htrace : WordTrace (prefixWord ++ tailWord_4703410) baseStart_4703410 baseEnd_4703410 := by
    simpa [prefixWord, tailWord_4703410, baseEnd_4703410] using wordTrace_append hprefix tailTrace_4703410
  have hstable : (prefixWord ++ tailWord_4703410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703410).length < 2 ^ (prefixWord ++ tailWord_4703410).sum := by decide
  have hdescent : baseEnd_4703410 < baseStart_4703410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703420 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4703420 : Nat := 118140960795 + 4703420 * 2 ^ 59
def prefixEnd_4703420 : Nat := 4983230072969 + 3 ^ 40 * 4703420 * 2
def baseEnd_4703420 : Nat := 2415115179970093081319371

theorem tailTrace_4703420 : CollatzResearch.WordTrace tailWord_4703420 prefixEnd_4703420 2415115179970093081319371 := by
  unfold tailWord_4703420
  simp only [CollatzResearch.WordTrace]
  refine ⟨85773910310160047514353857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114365213746880063352471809 85773910310160047514353857)
  ·
    refine ⟨64330432732620035635765393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85773910310160047514353857 64330432732620035635765393)
    ·
      refine ⟨48247824549465026726824045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64330432732620035635765393 48247824549465026726824045)
      ·
        refine ⟨18092934206049385022559017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48247824549465026726824045 18092934206049385022559017)
        ·
          refine ⟨13569700654537038766919263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18092934206049385022559017 13569700654537038766919263)
          ·
            refine ⟨20354550981805558150378895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13569700654537038766919263 20354550981805558150378895)
            ·
              refine ⟨30531826472708337225568343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20354550981805558150378895 30531826472708337225568343)
              ·
                refine ⟨45797739709062505838352515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30531826472708337225568343 45797739709062505838352515)
                ·
                  refine ⟨68696609563593758757528773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45797739709062505838352515 68696609563593758757528773)
                  ·
                    refine ⟨12880614293173829767036645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68696609563593758757528773 12880614293173829767036645)
                    ·
                      refine ⟨2415115179970093081319371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12880614293173829767036645 2415115179970093081319371)
                      ·
                        rfl

theorem cell23_4703420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4703420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703420 prefixEnd_4703420 := by exact prefixLift 4703420
  have htrace : WordTrace (prefixWord ++ tailWord_4703420) baseStart_4703420 baseEnd_4703420 := by
    simpa [prefixWord, tailWord_4703420, baseEnd_4703420] using wordTrace_append hprefix tailTrace_4703420
  have hstable : (prefixWord ++ tailWord_4703420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703420).length < 2 ^ (prefixWord ++ tailWord_4703420).sum := by decide
  have hdescent : baseEnd_4703420 < baseStart_4703420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703424 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 1, 4, 2]
def baseStart_4703424 : Nat := 118140960795 + 4703424 * 2 ^ 59
def prefixEnd_4703424 : Nat := 4983230072969 + 3 ^ 40 * 4703424 * 2
def baseEnd_4703424 : Nat := 2415117233892711065669353

theorem tailTrace_4703424 : CollatzResearch.WordTrace tailWord_4703424 prefixEnd_4703424 2415117233892711065669353 := by
  unfold tailWord_4703424
  simp only [CollatzResearch.WordTrace]
  refine ⟨85773983256152801855926663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114365311008203735807902217 85773983256152801855926663)
  ·
    refine ⟨128660974884229202783889995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85773983256152801855926663 128660974884229202783889995)
    ·
      refine ⟨192991462326343804175834993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128660974884229202783889995 192991462326343804175834993)
      ·
        refine ⟨144743596744757853131876245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192991462326343804175834993 144743596744757853131876245)
        ·
          refine ⟨6784856097410524365556699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144743596744757853131876245 6784856097410524365556699)
          ·
            refine ⟨10177284146115786548335049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6784856097410524365556699 10177284146115786548335049)
            ·
              refine ⟨7632963109586839911251287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10177284146115786548335049 7632963109586839911251287)
              ·
                refine ⟨11449444664380259866876931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7632963109586839911251287 11449444664380259866876931)
                ·
                  refine ⟨17174166996570389800315397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11449444664380259866876931 17174166996570389800315397)
                  ·
                    refine ⟨3220156311856948087559137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17174166996570389800315397 3220156311856948087559137)
                    ·
                      refine ⟨2415117233892711065669353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220156311856948087559137 2415117233892711065669353)
                      ·
                        rfl

theorem cell23_4703424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_4703424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703424 prefixEnd_4703424 := by exact prefixLift 4703424
  have htrace : WordTrace (prefixWord ++ tailWord_4703424) baseStart_4703424 baseEnd_4703424 := by
    simpa [prefixWord, tailWord_4703424, baseEnd_4703424] using wordTrace_append hprefix tailTrace_4703424
  have hstable : (prefixWord ++ tailWord_4703424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703424).length < 2 ^ (prefixWord ++ tailWord_4703424).sum := by decide
  have hdescent : baseEnd_4703424 < baseStart_4703424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703443 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 1, 7]
def baseStart_4703443 : Nat := 118140960795 + 4703443 * 2 ^ 59
def prefixEnd_4703443 : Nat := 4983230072969 + 3 ^ 40 * 4703443 * 2
def baseEnd_4703443 : Nat := 805042330008382163777255

theorem tailTrace_4703443 : CollatzResearch.WordTrace tailWord_4703443 prefixEnd_4703443 805042330008382163777255 := by
  unfold tailWord_4703443
  simp only [CollatzResearch.WordTrace]
  refine ⟨171548659499236769956794983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114365772999491179971196655 171548659499236769956794983)
  ·
    refine ⟨257322989248855154935192475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171548659499236769956794983 257322989248855154935192475)
    ·
      refine ⟨385984483873282732402788713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257322989248855154935192475 385984483873282732402788713)
      ·
        refine ⟨289488362904962049302091535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385984483873282732402788713 289488362904962049302091535)
        ·
          refine ⟨434232544357443073953137303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289488362904962049302091535 434232544357443073953137303)
          ·
            refine ⟨651348816536164610929705955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434232544357443073953137303 651348816536164610929705955)
            ·
              refine ⟨977023224804246916394558933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651348816536164610929705955 977023224804246916394558933)
              ·
                refine ⟨22898981831349537102997475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 977023224804246916394558933 22898981831349537102997475)
                ·
                  refine ⟨34348472747024305654496213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22898981831349537102997475 34348472747024305654496213)
                  ·
                    refine ⟨805042330008382163777255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34348472747024305654496213 805042330008382163777255)
                    ·
                      rfl

theorem cell23_4703443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 7].length) (baseStart_4703443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703443 prefixEnd_4703443 := by exact prefixLift 4703443
  have htrace : WordTrace (prefixWord ++ tailWord_4703443) baseStart_4703443 baseEnd_4703443 := by
    simpa [prefixWord, tailWord_4703443, baseEnd_4703443] using wordTrace_append hprefix tailTrace_4703443
  have hstable : (prefixWord ++ tailWord_4703443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703443).length < 2 ^ (prefixWord ++ tailWord_4703443).sum := by decide
  have hdescent : baseEnd_4703443 < baseStart_4703443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703460 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_4703460 : Nat := 118140960795 + 4703460 * 2 ^ 59
def prefixEnd_4703460 : Nat := 4983230072969 + 3 ^ 40 * 4703460 * 2
def baseEnd_4703460 : Nat := 805045239732090974939729

theorem tailTrace_4703460 : CollatzResearch.WordTrace tailWord_4703460 prefixEnd_4703460 805045239732090974939729 := by
  unfold tailWord_4703460
  simp only [CollatzResearch.WordTrace]
  refine ⟨85774639770087590930081917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114366186360116787906775889 85774639770087590930081917)
  ·
    refine ⟨32165489913782846598780719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85774639770087590930081917 32165489913782846598780719)
    ·
      refine ⟨48248234870674269898171079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32165489913782846598780719 48248234870674269898171079)
      ·
        refine ⟨72372352306011404847256619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48248234870674269898171079 72372352306011404847256619)
        ·
          refine ⟨108558528459017107270884929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72372352306011404847256619 108558528459017107270884929)
          ·
            refine ⟨81418896344262830453163697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108558528459017107270884929 81418896344262830453163697)
            ·
              refine ⟨61064172258197122839872773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81418896344262830453163697 61064172258197122839872773)
              ·
                refine ⟨11449532298411960532476145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61064172258197122839872773 11449532298411960532476145)
                ·
                  refine ⟨8587149223808970399357109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11449532298411960532476145 8587149223808970399357109)
                  ·
                    refine ⟨805045239732090974939729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8587149223808970399357109 805045239732090974939729)
                    ·
                      rfl

theorem cell23_4703460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_4703460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703460 prefixEnd_4703460 := by exact prefixLift 4703460
  have htrace : WordTrace (prefixWord ++ tailWord_4703460) baseStart_4703460 baseEnd_4703460 := by
    simpa [prefixWord, tailWord_4703460, baseEnd_4703460] using wordTrace_append hprefix tailTrace_4703460
  have hstable : (prefixWord ++ tailWord_4703460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703460).length < 2 ^ (prefixWord ++ tailWord_4703460).sum := by decide
  have hdescent : baseEnd_4703460 < baseStart_4703460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703470 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_4703470 : Nat := 118140960795 + 4703470 * 2 ^ 59
def prefixEnd_4703470 : Nat := 4983230072969 + 3 ^ 40 * 4703470 * 2
def baseEnd_4703470 : Nat := 2415140854002817885694141

theorem tailTrace_4703470 : CollatzResearch.WordTrace tailWord_4703470 prefixEnd_4703470 2415140854002817885694141 := by
  unfold tailWord_4703470
  simp only [CollatzResearch.WordTrace]
  refine ⟨21443705533767369196003483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114366429513425969045351909 21443705533767369196003483)
  ·
    refine ⟨32165558300651053794005225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21443705533767369196003483 32165558300651053794005225)
    ·
      refine ⟨24124168725488290345503919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32165558300651053794005225 24124168725488290345503919)
      ·
        refine ⟨36186253088232435518255879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24124168725488290345503919 36186253088232435518255879)
        ·
          refine ⟨54279379632348653277383819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36186253088232435518255879 54279379632348653277383819)
          ·
            refine ⟨81419069448522979916075729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54279379632348653277383819 81419069448522979916075729)
            ·
              refine ⟨61064302086392234937056797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81419069448522979916075729 61064302086392234937056797)
              ·
                refine ⟨22899113282397088101396299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61064302086392234937056797 22899113282397088101396299)
                ·
                  refine ⟨34348669923595632152094449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22899113282397088101396299 34348669923595632152094449)
                  ·
                    refine ⟨25761502442696724114070837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34348669923595632152094449 25761502442696724114070837)
                    ·
                      refine ⟨2415140854002817885694141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25761502442696724114070837 2415140854002817885694141)
                      ·
                        rfl

theorem cell23_4703470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_4703470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703470 prefixEnd_4703470 := by exact prefixLift 4703470
  have htrace : WordTrace (prefixWord ++ tailWord_4703470) baseStart_4703470 baseEnd_4703470 := by
    simpa [prefixWord, tailWord_4703470, baseEnd_4703470] using wordTrace_append hprefix tailTrace_4703470
  have hstable : (prefixWord ++ tailWord_4703470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703470).length < 2 ^ (prefixWord ++ tailWord_4703470).sum := by decide
  have hdescent : baseEnd_4703470 < baseStart_4703470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703537 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 6]
def baseStart_4703537 : Nat := 118140960795 + 4703537 * 2 ^ 59
def prefixEnd_4703537 : Nat := 4983230072969 + 3 ^ 40 * 4703537 * 2
def baseEnd_4703537 : Nat := 268352806356296569284037

theorem tailTrace_4703537 : CollatzResearch.WordTrace tailWord_4703537 prefixEnd_4703537 268352806356296569284037 := by
  unfold tailWord_4703537
  simp only [CollatzResearch.WordTrace]
  refine ⟨171552087960896224010716865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114368058640597482673811243 171552087960896224010716865)
  ·
    refine ⟨128664065970672168008037649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171552087960896224010716865 128664065970672168008037649)
    ·
      refine ⟨96498049478004126006028237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128664065970672168008037649 96498049478004126006028237)
      ·
        refine ⟨36186768554251547252260589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96498049478004126006028237 36186768554251547252260589)
        ·
          refine ⟨13570038207844330219597721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36186768554251547252260589 13570038207844330219597721)
          ·
            refine ⟨10177528655883247664698291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13570038207844330219597721 10177528655883247664698291)
            ·
              refine ⟨15266292983824871497047437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10177528655883247664698291 15266292983824871497047437)
              ·
                refine ⟨5724859868934326811392789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15266292983824871497047437 5724859868934326811392789)
                ·
                  refine ⟨268352806356296569284037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5724859868934326811392789 268352806356296569284037)
                  ·
                    rfl

theorem cell23_4703537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 6].length) (baseStart_4703537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703537 prefixEnd_4703537 := by exact prefixLift 4703537
  have htrace : WordTrace (prefixWord ++ tailWord_4703537) baseStart_4703537 baseEnd_4703537 := by
    simpa [prefixWord, tailWord_4703537, baseEnd_4703537] using wordTrace_append hprefix tailTrace_4703537
  have hstable : (prefixWord ++ tailWord_4703537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703537).length < 2 ^ (prefixWord ++ tailWord_4703537).sum := by decide
  have hdescent : baseEnd_4703537 < baseStart_4703537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703557 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 1, 5, 2]
def baseStart_4703557 : Nat := 118140960795 + 4703557 * 2 ^ 59
def prefixEnd_4703557 : Nat := 4983230072969 + 3 ^ 40 * 4703557 * 2
def baseEnd_4703557 : Nat := 2415185526819759045306241

theorem tailTrace_4703557 : CollatzResearch.WordTrace tailWord_4703557 prefixEnd_4703557 2415185526819759045306241 := by
  unfold tailWord_4703557
  simp only [CollatzResearch.WordTrace]
  refine ⟨171552817420823767426444925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114368544947215844950963283 171552817420823767426444925)
  ·
    refine ⟨64332306532808912784916847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171552817420823767426444925 64332306532808912784916847)
    ·
      refine ⟨96498459799213369177375271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64332306532808912784916847 96498459799213369177375271)
      ·
        refine ⟨144747689698820053766062907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96498459799213369177375271 144747689698820053766062907)
        ·
          refine ⟨217121534548230080649094361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144747689698820053766062907 217121534548230080649094361)
          ·
            refine ⟨162841150911172560486820771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217121534548230080649094361 162841150911172560486820771)
            ·
              refine ⟨244261726366758840730231157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162841150911172560486820771 244261726366758840730231157)
              ·
                refine ⟨22899536846883641318459171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244261726366758840730231157 22899536846883641318459171)
                ·
                  refine ⟨34349305270325461977688757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22899536846883641318459171 34349305270325461977688757)
                  ·
                    refine ⟨3220247369093012060408321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34349305270325461977688757 3220247369093012060408321)
                    ·
                      refine ⟨2415185526819759045306241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220247369093012060408321 2415185526819759045306241)
                      ·
                        rfl

theorem cell23_4703557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_4703557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703557 prefixEnd_4703557 := by exact prefixLift 4703557
  have htrace : WordTrace (prefixWord ++ tailWord_4703557) baseStart_4703557 baseEnd_4703557 := by
    simpa [prefixWord, tailWord_4703557, baseEnd_4703557] using wordTrace_append hprefix tailTrace_4703557
  have hstable : (prefixWord ++ tailWord_4703557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703557).length < 2 ^ (prefixWord ++ tailWord_4703557).sum := by decide
  have hdescent : baseEnd_4703557 < baseStart_4703557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703587 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4703587 : Nat := 118140960795 + 4703587 * 2 ^ 59
def prefixEnd_4703587 : Nat := 4983230072969 + 3 ^ 40 * 4703587 * 2
def baseEnd_4703587 : Nat := 2415200931239393927931103

theorem tailTrace_4703587 : CollatzResearch.WordTrace tailWord_4703587 prefixEnd_4703587 2415200931239393927931103 := by
  unfold tailWord_4703587
  simp only [CollatzResearch.WordTrace]
  refine ⟨171553911610715082550037015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114369274407143388366691343 171553911610715082550037015)
  ·
    refine ⟨257330867416072623825055523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171553911610715082550037015 257330867416072623825055523)
    ·
      refine ⟨385996301124108935737583285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257330867416072623825055523 385996301124108935737583285)
      ·
        refine ⟨36187153230385212725398433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 385996301124108935737583285 36187153230385212725398433)
        ·
          refine ⟨27140364922788909544048825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36187153230385212725398433 27140364922788909544048825)
          ·
            refine ⟨20355273692091682158036619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27140364922788909544048825 20355273692091682158036619)
            ·
              refine ⟨30532910538137523237054929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20355273692091682158036619 30532910538137523237054929)
              ·
                refine ⟨22899682903603142427791197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30532910538137523237054929 22899682903603142427791197)
                ·
                  refine ⟨8587381088851178410421699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22899682903603142427791197 8587381088851178410421699)
                  ·
                    refine ⟨12881071633276767615632549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8587381088851178410421699 12881071633276767615632549)
                    ·
                      refine ⟨2415200931239393927931103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12881071633276767615632549 2415200931239393927931103)
                      ·
                        rfl

theorem cell23_4703587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4703587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703587 prefixEnd_4703587 := by exact prefixLift 4703587
  have htrace : WordTrace (prefixWord ++ tailWord_4703587) baseStart_4703587 baseEnd_4703587 := by
    simpa [prefixWord, tailWord_4703587, baseEnd_4703587] using wordTrace_append hprefix tailTrace_4703587
  have hstable : (prefixWord ++ tailWord_4703587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703587).length < 2 ^ (prefixWord ++ tailWord_4703587).sum := by decide
  have hdescent : baseEnd_4703587 < baseStart_4703587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703597 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_4703597 : Nat := 118140960795 + 4703597 * 2 ^ 59
def prefixEnd_4703597 : Nat := 4983230072969 + 3 ^ 40 * 4703597 * 2
def baseEnd_4703597 : Nat := 805068688681979629602019

theorem tailTrace_4703597 : CollatzResearch.WordTrace tailWord_4703597 prefixEnd_4703597 805068688681979629602019 := by
  unfold tailWord_4703597
  simp only [CollatzResearch.WordTrace]
  refine ⟨171554276340678854257901045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114369517560452569505267363 171554276340678854257901045)
  ·
    refine ⟨16083213406938642586678223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171554276340678854257901045 16083213406938642586678223)
    ·
      refine ⟨24124820110407963880017335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16083213406938642586678223 24124820110407963880017335)
      ·
        refine ⟨36187230165611945820026003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24124820110407963880017335 36187230165611945820026003)
        ·
          refine ⟨54280845248417918730039005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36187230165611945820026003 54280845248417918730039005)
          ·
            refine ⟨20355316968156719523764627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54280845248417918730039005 20355316968156719523764627)
            ·
              refine ⟨30532975452235079285646941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20355316968156719523764627 30532975452235079285646941)
              ·
                refine ⟨11449865794588154732117603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30532975452235079285646941 11449865794588154732117603)
                ·
                  refine ⟨17174798691882232098176405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11449865794588154732117603 17174798691882232098176405)
                  ·
                    refine ⟨805068688681979629602019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17174798691882232098176405 805068688681979629602019)
                    ·
                      rfl

theorem cell23_4703597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_4703597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703597 prefixEnd_4703597 := by exact prefixLift 4703597
  have htrace : WordTrace (prefixWord ++ tailWord_4703597) baseStart_4703597 baseEnd_4703597 := by
    simpa [prefixWord, tailWord_4703597, baseEnd_4703597] using wordTrace_append hprefix tailTrace_4703597
  have hstable : (prefixWord ++ tailWord_4703597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703597).length < 2 ^ (prefixWord ++ tailWord_4703597).sum := by decide
  have hdescent : baseEnd_4703597 < baseStart_4703597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703598 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4703598 : Nat := 118140960795 + 4703598 * 2 ^ 59
def prefixEnd_4703598 : Nat := 4983230072969 + 3 ^ 40 * 4703598 * 2
def baseEnd_4703598 : Nat := 2415206579526593384893553

theorem tailTrace_4703598 : CollatzResearch.WordTrace tailWord_4703598 prefixEnd_4703598 2415206579526593384893553 := by
  unfold tailWord_4703598
  simp only [CollatzResearch.WordTrace]
  refine ⟨21444289101709403928585931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114369541875783487619124965 21444289101709403928585931)
  ·
    refine ⟨32166433652564105892878897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21444289101709403928585931 32166433652564105892878897)
    ·
      refine ⟨24124825239423079419659173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32166433652564105892878897 24124825239423079419659173)
      ·
        refine ⟨4523404732391827391186095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24124825239423079419659173 4523404732391827391186095)
        ·
          refine ⟨6785107098587741086779143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523404732391827391186095 6785107098587741086779143)
          ·
            refine ⟨10177660647881611630168715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785107098587741086779143 10177660647881611630168715)
            ·
              refine ⟨15266490971822417445253073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10177660647881611630168715 15266490971822417445253073)
              ·
                refine ⟨11449868228866813083939805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15266490971822417445253073 11449868228866813083939805)
                ·
                  refine ⟨4293700585825054906477427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11449868228866813083939805 4293700585825054906477427)
                  ·
                    refine ⟨6440550878737582359716141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4293700585825054906477427 6440550878737582359716141)
                    ·
                      refine ⟨2415206579526593384893553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6440550878737582359716141 2415206579526593384893553)
                      ·
                        rfl

theorem cell23_4703598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4703598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703598 prefixEnd_4703598 := by exact prefixLift 4703598
  have htrace : WordTrace (prefixWord ++ tailWord_4703598) baseStart_4703598 baseEnd_4703598 := by
    simpa [prefixWord, tailWord_4703598, baseEnd_4703598] using wordTrace_append hprefix tailTrace_4703598
  have hstable : (prefixWord ++ tailWord_4703598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703598).length < 2 ^ (prefixWord ++ tailWord_4703598).sum := by decide
  have hdescent : baseEnd_4703598 < baseStart_4703598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703607 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_4703607 : Nat := 118140960795 + 4703607 * 2 ^ 59
def prefixEnd_4703607 : Nat := 4983230072969 + 3 ^ 40 * 4703607 * 2
def baseEnd_4703607 : Nat := 2415211200852483849681011

theorem tailTrace_4703607 : CollatzResearch.WordTrace tailWord_4703607 prefixEnd_4703607 2415211200852483849681011 := by
  unfold tailWord_4703607
  simp only [CollatzResearch.WordTrace]
  refine ⟨171554641070642625965765075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114369760713761750643843383 171554641070642625965765075)
  ·
    refine ⟨257331961605963938948647613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171554641070642625965765075 257331961605963938948647613)
    ·
      refine ⟨96499485602236477105742855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257331961605963938948647613 96499485602236477105742855)
      ·
        refine ⟨144749228403354715658614283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96499485602236477105742855 144749228403354715658614283)
        ·
          refine ⟨217123842605032073487921425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144749228403354715658614283 217123842605032073487921425)
          ·
            refine ⟨162842881953774055115941069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217123842605032073487921425 162842881953774055115941069)
            ·
              refine ⟨61066080732665270668477901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162842881953774055115941069 61066080732665270668477901)
              ·
                refine ⟨22899780274749476500679213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61066080732665270668477901 22899780274749476500679213)
                ·
                  refine ⟨8587417603031053687754705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22899780274749476500679213 8587417603031053687754705)
                  ·
                    refine ⟨6440563202273290265816029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8587417603031053687754705 6440563202273290265816029)
                    ·
                      refine ⟨2415211200852483849681011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6440563202273290265816029 2415211200852483849681011)
                      ·
                        rfl

theorem cell23_4703607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_4703607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703607 prefixEnd_4703607 := by exact prefixLift 4703607
  have htrace : WordTrace (prefixWord ++ tailWord_4703607) baseStart_4703607 baseEnd_4703607 := by
    simpa [prefixWord, tailWord_4703607, baseEnd_4703607] using wordTrace_append hprefix tailTrace_4703607
  have hstable : (prefixWord ++ tailWord_4703607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703607).length < 2 ^ (prefixWord ++ tailWord_4703607).sum := by decide
  have hdescent : baseEnd_4703607 < baseStart_4703607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703618 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4703618 : Nat := 118140960795 + 4703618 * 2 ^ 59
def prefixEnd_4703618 : Nat := 4983230072969 + 3 ^ 40 * 4703618 * 2
def baseEnd_4703618 : Nat := 805072283046561102214487

theorem tailTrace_4703618 : CollatzResearch.WordTrace tailWord_4703618 prefixEnd_4703618 805072283046561102214487 := by
  unfold tailWord_4703618
  simp only [CollatzResearch.WordTrace]
  refine ⟨42888760568400693711103877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114370028182401849896277005 42888760568400693711103877)
  ·
    refine ⟨8041642606575130070831977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42888760568400693711103877 8041642606575130070831977)
    ·
      refine ⟨6031231954931347553123983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8041642606575130070831977 6031231954931347553123983)
      ·
        refine ⟨9046847932397021329685975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6031231954931347553123983 9046847932397021329685975)
        ·
          refine ⟨13570271898595531994528963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9046847932397021329685975 13570271898595531994528963)
          ·
            refine ⟨20355407847893297991793445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13570271898595531994528963 20355407847893297991793445)
            ·
              refine ⟨3816638971479993373461271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20355407847893297991793445 3816638971479993373461271)
              ·
                refine ⟨5724958457219990060191907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816638971479993373461271 5724958457219990060191907)
                ·
                  refine ⟨8587437685829985090287861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5724958457219990060191907 8587437685829985090287861)
                  ·
                    refine ⟨805072283046561102214487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8587437685829985090287861 805072283046561102214487)
                    ·
                      rfl

theorem cell23_4703618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4703618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703618 prefixEnd_4703618 := by exact prefixLift 4703618
  have htrace : WordTrace (prefixWord ++ tailWord_4703618) baseStart_4703618 baseEnd_4703618 := by
    simpa [prefixWord, tailWord_4703618, baseEnd_4703618] using wordTrace_append hprefix tailTrace_4703618
  have hstable : (prefixWord ++ tailWord_4703618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703618).length < 2 ^ (prefixWord ++ tailWord_4703618).sum := by decide
  have hdescent : baseEnd_4703618 < baseStart_4703618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703637 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_4703637 : Nat := 118140960795 + 4703637 * 2 ^ 59
def prefixEnd_4703637 : Nat := 4983230072969 + 3 ^ 40 * 4703637 * 2
def baseEnd_4703637 : Nat := 2415226605272118732305873

theorem tailTrace_4703637 : CollatzResearch.WordTrace tailWord_4703637 prefixEnd_4703637 2415226605272118732305873 := by
  unfold tailWord_4703637
  simp only [CollatzResearch.WordTrace]
  refine ⟨171555735260533941089357165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114370490173689294059571443 171555735260533941089357165)
  ·
    refine ⟨64333400722700227908508937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171555735260533941089357165 64333400722700227908508937)
    ·
      refine ⟨48250050542025170931381703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64333400722700227908508937 48250050542025170931381703)
      ·
        refine ⟨72375075813037756397072555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48250050542025170931381703 72375075813037756397072555)
        ·
          refine ⟨108562613719556634595608833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72375075813037756397072555 108562613719556634595608833)
          ·
            refine ⟨81421960289667475946706625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108562613719556634595608833 81421960289667475946706625)
            ·
              refine ⟨61066470217250606960029969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81421960289667475946706625 61066470217250606960029969)
              ·
                refine ⟨45799852662937955220022477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61066470217250606960029969 45799852662937955220022477)
                ·
                  refine ⟨17174944748601733207508429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45799852662937955220022477 17174944748601733207508429)
                  ·
                    refine ⟨6440604280725649952815661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17174944748601733207508429 6440604280725649952815661)
                    ·
                      refine ⟨2415226605272118732305873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6440604280725649952815661 2415226605272118732305873)
                      ·
                        rfl

theorem cell23_4703637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_4703637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703637 prefixEnd_4703637 := by exact prefixLift 4703637
  have htrace : WordTrace (prefixWord ++ tailWord_4703637) baseStart_4703637 baseEnd_4703637 := by
    simpa [prefixWord, tailWord_4703637, baseEnd_4703637] using wordTrace_append hprefix tailTrace_4703637
  have hstable : (prefixWord ++ tailWord_4703637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703637).length < 2 ^ (prefixWord ++ tailWord_4703637).sum := by decide
  have hdescent : baseEnd_4703637 < baseStart_4703637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703661 : List Nat := [1, 5, 2, 2, 1, 3, 2, 7]
def baseStart_4703661 : Nat := 118140960795 + 4703661 * 2 ^ 59
def prefixEnd_4703661 : Nat := 4983230072969 + 3 ^ 40 * 4703661 * 2
def baseEnd_4703661 : Nat := 89453293659549134755769

theorem tailTrace_4703661 : CollatzResearch.WordTrace tailWord_4703661 prefixEnd_4703661 89453293659549134755769 := by
  unfold tailWord_4703661
  simp only [CollatzResearch.WordTrace]
  refine ⟨171556610612446993188230837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114371073741631328792153891 171556610612446993188230837)
  ·
    refine ⟨16083432244916905611396641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171556610612446993188230837 16083432244916905611396641)
    ·
      refine ⟨12062574183687679208547481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16083432244916905611396641 12062574183687679208547481)
      ·
        refine ⟨9046930637765759406410611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12062574183687679208547481 9046930637765759406410611)
        ·
          refine ⟨13570395956648639109615917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9046930637765759406410611 13570395956648639109615917)
          ·
            refine ⟨5088898483743239666105969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13570395956648639109615917 5088898483743239666105969)
            ·
              refine ⟨3816673862807429749579477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5088898483743239666105969 3816673862807429749579477)
              ·
                refine ⟨89453293659549134755769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3816673862807429749579477 89453293659549134755769)
                ·
                  rfl

theorem cell23_4703661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 7].length) (baseStart_4703661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703661 prefixEnd_4703661 := by exact prefixLift 4703661
  have htrace : WordTrace (prefixWord ++ tailWord_4703661) baseStart_4703661 baseEnd_4703661 := by
    simpa [prefixWord, tailWord_4703661, baseEnd_4703661] using wordTrace_append hprefix tailTrace_4703661
  have hstable : (prefixWord ++ tailWord_4703661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703661).length < 2 ^ (prefixWord ++ tailWord_4703661).sum := by decide
  have hdescent : baseEnd_4703661 < baseStart_4703661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703745 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_4703745 : Nat := 118140960795 + 4703745 * 2 ^ 59
def prefixEnd_4703745 : Nat := 4983230072969 + 3 ^ 40 * 4703745 * 2
def baseEnd_4703745 : Nat := 2415282061182804309755377

theorem tailTrace_4703745 : CollatzResearch.WordTrace tailWord_4703745 prefixEnd_4703745 2415282061182804309755377 := by
  unfold tailWord_4703745
  simp only [CollatzResearch.WordTrace]
  refine ⟨171559674344142675534288689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114373116229428450356192459 171559674344142675534288689)
  ·
    refine ⟨128669755758107006650716517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171559674344142675534288689 128669755758107006650716517)
    ·
      refine ⟨24125579204645063747009347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128669755758107006650716517 24125579204645063747009347)
      ·
        refine ⟨36188368806967595620514021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24125579204645063747009347 36188368806967595620514021)
        ·
          refine ⟨6785319151306424178846379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36188368806967595620514021 6785319151306424178846379)
          ·
            refine ⟨10177978726959636268269569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785319151306424178846379 10177978726959636268269569)
            ·
              refine ⟨7633484045219727201202177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10177978726959636268269569 7633484045219727201202177)
              ·
                refine ⟨5725113033914795400901633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7633484045219727201202177 5725113033914795400901633)
                ·
                  refine ⟨4293834775436096550676225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5725113033914795400901633 4293834775436096550676225)
                  ·
                    refine ⟨3220376081577072413007169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4293834775436096550676225 3220376081577072413007169)
                    ·
                      refine ⟨2415282061182804309755377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220376081577072413007169 2415282061182804309755377)
                      ·
                        rfl

theorem cell23_4703745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_4703745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703745 prefixEnd_4703745 := by exact prefixLift 4703745
  have htrace : WordTrace (prefixWord ++ tailWord_4703745) baseStart_4703745 baseEnd_4703745 := by
    simpa [prefixWord, tailWord_4703745, baseEnd_4703745] using wordTrace_append hprefix tailTrace_4703745
  have hstable : (prefixWord ++ tailWord_4703745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703745).length < 2 ^ (prefixWord ++ tailWord_4703745).sum := by decide
  have hdescent : baseEnd_4703745 < baseStart_4703745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703747 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 4, 5]
def baseStart_4703747 : Nat := 118140960795 + 4703747 * 2 ^ 59
def prefixEnd_4703747 : Nat := 4983230072969 + 3 ^ 40 * 4703747 * 2
def baseEnd_4703747 : Nat := 805094362714704433976789

theorem tailTrace_4703747 : CollatzResearch.WordTrace tailWord_4703747 prefixEnd_4703747 805094362714704433976789 := by
  unfold tailWord_4703747
  simp only [CollatzResearch.WordTrace]
  refine ⟨171559747290135429875861495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114373164860090286583907663 171559747290135429875861495)
  ·
    refine ⟨257339620935203144813792243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171559747290135429875861495 257339620935203144813792243)
    ·
      refine ⟨386009431402804717220688365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257339620935203144813792243 386009431402804717220688365)
      ·
        refine ⟨144753536776051768957758137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386009431402804717220688365 144753536776051768957758137)
        ·
          refine ⟨108565152582038826718318603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144753536776051768957758137 108565152582038826718318603)
          ·
            refine ⟨162847728873058240077477905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108565152582038826718318603 162847728873058240077477905)
            ·
              refine ⟨122135796654793680058108429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162847728873058240077477905 122135796654793680058108429)
              ·
                refine ⟨45800923745547630021790661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122135796654793680058108429 45800923745547630021790661)
                ·
                  refine ⟨8587673202290180629085749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45800923745547630021790661 8587673202290180629085749)
                  ·
                    refine ⟨805094362714704433976789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8587673202290180629085749 805094362714704433976789)
                    ·
                      rfl

theorem cell23_4703747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 5].length) (baseStart_4703747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703747 prefixEnd_4703747 := by exact prefixLift 4703747
  have htrace : WordTrace (prefixWord ++ tailWord_4703747) baseStart_4703747 baseEnd_4703747 := by
    simpa [prefixWord, tailWord_4703747, baseEnd_4703747] using wordTrace_append hprefix tailTrace_4703747
  have hstable : (prefixWord ++ tailWord_4703747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703747).length < 2 ^ (prefixWord ++ tailWord_4703747).sum := by decide
  have hdescent : baseEnd_4703747 < baseStart_4703747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703751 : List Nat := [1, 1, 4, 3, 2, 2, 1, 4, 5]
def baseStart_4703751 : Nat := 118140960795 + 4703751 * 2 ^ 59
def prefixEnd_4703751 : Nat := 4983230072969 + 3 ^ 40 * 4703751 * 2
def baseEnd_4703751 : Nat := 268365015785192365142261

theorem tailTrace_4703751 : CollatzResearch.WordTrace tailWord_4703751 prefixEnd_4703751 268365015785192365142261 := by
  unfold tailWord_4703751
  simp only [CollatzResearch.WordTrace]
  refine ⟨171559893182120938559007107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114373262121413959039338071 171559893182120938559007107)
  ·
    refine ⟨257339839773181407838510661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171559893182120938559007107 257339839773181407838510661)
    ·
      refine ⟨48251219957471513969720749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257339839773181407838510661 48251219957471513969720749)
      ·
        refine ⟨18094207484051817738645281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48251219957471513969720749 18094207484051817738645281)
        ·
          refine ⟨13570655613038863303983961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18094207484051817738645281 13570655613038863303983961)
          ·
            refine ⟨10177991709779147477987971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13570655613038863303983961 10177991709779147477987971)
            ·
              refine ⟨15266987564668721216981957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10177991709779147477987971 15266987564668721216981957)
              ·
                refine ⟨2862560168375385228184117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15266987564668721216981957 2862560168375385228184117)
                ·
                  refine ⟨268365015785192365142261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862560168375385228184117 268365015785192365142261)
                  ·
                    rfl

theorem cell23_4703751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 5].length) (baseStart_4703751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703751 prefixEnd_4703751 := by exact prefixLift 4703751
  have htrace : WordTrace (prefixWord ++ tailWord_4703751) baseStart_4703751 baseEnd_4703751 := by
    simpa [prefixWord, tailWord_4703751, baseEnd_4703751] using wordTrace_append hprefix tailTrace_4703751
  have hstable : (prefixWord ++ tailWord_4703751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703751).length < 2 ^ (prefixWord ++ tailWord_4703751).sum := by decide
  have hdescent : baseEnd_4703751 < baseStart_4703751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703794 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_4703794 : Nat := 118140960795 + 4703794 * 2 ^ 59
def prefixEnd_4703794 : Nat := 4983230072969 + 3 ^ 40 * 4703794 * 2
def baseEnd_4703794 : Nat := 805102407244958206014217

theorem tailTrace_4703794 : CollatzResearch.WordTrace tailWord_4703794 prefixEnd_4703794 805102407244958206014217 := by
  unfold tailWord_4703794
  simp only [CollatzResearch.WordTrace]
  refine ⟨42890365380241289225705609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114374307680643437935214957 42890365380241289225705609)
  ·
    refine ⟨32167774035180966919279207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42890365380241289225705609 32167774035180966919279207)
    ·
      refine ⟨48251661052771450378918811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32167774035180966919279207 48251661052771450378918811)
      ·
        refine ⟨72377491579157175568378217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48251661052771450378918811 72377491579157175568378217)
        ·
          refine ⟨54283118684367881676283663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72377491579157175568378217 54283118684367881676283663)
          ·
            refine ⟨81424678026551822514425495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54283118684367881676283663 81424678026551822514425495)
            ·
              refine ⟨122137017039827733771638243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81424678026551822514425495 122137017039827733771638243)
              ·
                refine ⟨183205525559741600657457365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122137017039827733771638243 183205525559741600657457365)
                ·
                  refine ⟨4293879505306443765409157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 183205525559741600657457365 4293879505306443765409157)
                  ·
                    refine ⟨805102407244958206014217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293879505306443765409157 805102407244958206014217)
                    ·
                      rfl

theorem cell23_4703794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_4703794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703794 prefixEnd_4703794 := by exact prefixLift 4703794
  have htrace : WordTrace (prefixWord ++ tailWord_4703794) baseStart_4703794 baseEnd_4703794 := by
    simpa [prefixWord, tailWord_4703794, baseEnd_4703794] using wordTrace_append hprefix tailTrace_4703794
  have hstable : (prefixWord ++ tailWord_4703794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703794).length < 2 ^ (prefixWord ++ tailWord_4703794).sum := by decide
  have hdescent : baseEnd_4703794 < baseStart_4703794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703801 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4703801 : Nat := 118140960795 + 4703801 * 2 ^ 59
def prefixEnd_4703801 : Nat := 4983230072969 + 3 ^ 40 * 4703801 * 2
def baseEnd_4703801 : Nat := 2415310816099456090655119

theorem tailTrace_4703801 : CollatzResearch.WordTrace tailWord_4703801 prefixEnd_4703801 2415310816099456090655119 := by
  unfold tailWord_4703801
  simp only [CollatzResearch.WordTrace]
  refine ⟨171561716831939797098327257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114374477887959864732218171 171561716831939797098327257)
  ·
    refine ⟨128671287623954847823745443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171561716831939797098327257 128671287623954847823745443)
    ·
      refine ⟨193006931435932271735618165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128671287623954847823745443 193006931435932271735618165)
      ·
        refine ⟨18094399822118650475214203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193006931435932271735618165 18094399822118650475214203)
        ·
          refine ⟨27141599733177975712821305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18094399822118650475214203 27141599733177975712821305)
          ·
            refine ⟨20356199799883481784615979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27141599733177975712821305 20356199799883481784615979)
            ·
              refine ⟨30534299699825222676923969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20356199799883481784615979 30534299699825222676923969)
              ·
                refine ⟨22900724774868917007692977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30534299699825222676923969 22900724774868917007692977)
                ·
                  refine ⟨17175543581151687755769733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22900724774868917007692977 17175543581151687755769733)
                  ·
                    refine ⟨3220414421465941454206825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17175543581151687755769733 3220414421465941454206825)
                    ·
                      refine ⟨2415310816099456090655119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220414421465941454206825 2415310816099456090655119)
                      ·
                        rfl

theorem cell23_4703801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4703801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703801 prefixEnd_4703801 := by exact prefixLift 4703801
  have htrace : WordTrace (prefixWord ++ tailWord_4703801) baseStart_4703801 baseEnd_4703801 := by
    simpa [prefixWord, tailWord_4703801, baseEnd_4703801] using wordTrace_append hprefix tailTrace_4703801
  have hstable : (prefixWord ++ tailWord_4703801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703801).length < 2 ^ (prefixWord ++ tailWord_4703801).sum := by decide
  have hdescent : baseEnd_4703801 < baseStart_4703801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703845 : List Nat := [1, 3, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_4703845 : Nat := 118140960795 + 4703845 * 2 ^ 59
def prefixEnd_4703845 : Nat := 4983230072969 + 3 ^ 40 * 4703845 * 2
def baseEnd_4703845 : Nat := 805111136416084639501639

theorem tailTrace_4703845 : CollatzResearch.WordTrace tailWord_4703845 prefixEnd_4703845 805111136416084639501639 := by
  unfold tailWord_4703845
  simp only [CollatzResearch.WordTrace]
  refine ⟨171563321643780392612928989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114375547762520261741952659 171563321643780392612928989)
  ·
    refine ⟨64336245616417647229848371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171563321643780392612928989 64336245616417647229848371)
    ·
      refine ⟨96504368424626470844772557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64336245616417647229848371 96504368424626470844772557)
      ·
        refine ⟨36189138159234926566789709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96504368424626470844772557 36189138159234926566789709)
        ·
          refine ⟨13570926809713097462546141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36189138159234926566789709 13570926809713097462546141)
          ·
            refine ⟨5089097553642411548454803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13570926809713097462546141 5089097553642411548454803)
            ·
              refine ⟨7633646330463617322682205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5089097553642411548454803 7633646330463617322682205)
              ·
                refine ⟨2862617373923856496005827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7633646330463617322682205 2862617373923856496005827)
                ·
                  refine ⟨4293926060885784744008741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862617373923856496005827 4293926060885784744008741)
                  ·
                    refine ⟨805111136416084639501639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293926060885784744008741 805111136416084639501639)
                    ·
                      rfl

theorem cell23_4703845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_4703845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703845 prefixEnd_4703845 := by exact prefixLift 4703845
  have htrace : WordTrace (prefixWord ++ tailWord_4703845) baseStart_4703845 baseEnd_4703845 := by
    simpa [prefixWord, tailWord_4703845, baseEnd_4703845] using wordTrace_append hprefix tailTrace_4703845
  have hstable : (prefixWord ++ tailWord_4703845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703845).length < 2 ^ (prefixWord ++ tailWord_4703845).sum := by decide
  have hdescent : baseEnd_4703845 < baseStart_4703845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703862 : List Nat := [5, 1, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_4703862 : Nat := 118140960795 + 4703862 * 2 ^ 59
def prefixEnd_4703862 : Nat := 4983230072969 + 3 ^ 40 * 4703862 * 2
def baseEnd_4703862 : Nat := 805114046139793450664113

theorem tailTrace_4703862 : CollatzResearch.WordTrace tailWord_4703862 prefixEnd_4703862 805114046139793450664113 := by
  unfold tailWord_4703862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722746355294925282268615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114375961123145869677531893 10722746355294925282268615)
  ·
    refine ⟨16084119532942387923402923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10722746355294925282268615 16084119532942387923402923)
    ·
      refine ⟨24126179299413581885104385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16084119532942387923402923 24126179299413581885104385)
      ·
        refine ⟨18094634474560186413828289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24126179299413581885104385 18094634474560186413828289)
        ·
          refine ⟨13570975855920139810371217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18094634474560186413828289 13570975855920139810371217)
          ·
            refine ⟨10178231891940104857778413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13570975855920139810371217 10178231891940104857778413)
            ·
              refine ⟨3816836959477539321666905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10178231891940104857778413 3816836959477539321666905)
              ·
                refine ⟨2862627719608154491250179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816836959477539321666905 2862627719608154491250179)
                ·
                  refine ⟨4293941579412231736875269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862627719608154491250179 4293941579412231736875269)
                  ·
                    refine ⟨805114046139793450664113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293941579412231736875269 805114046139793450664113)
                    ·
                      rfl

theorem cell23_4703862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_4703862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703862 prefixEnd_4703862 := by exact prefixLift 4703862
  have htrace : WordTrace (prefixWord ++ tailWord_4703862) baseStart_4703862 baseEnd_4703862 := by
    simpa [prefixWord, tailWord_4703862, baseEnd_4703862] using wordTrace_append hprefix tailTrace_4703862
  have hstable : (prefixWord ++ tailWord_4703862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703862).length < 2 ^ (prefixWord ++ tailWord_4703862).sum := by decide
  have hdescent : baseEnd_4703862 < baseStart_4703862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703884 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_4703884 : Nat := 118140960795 + 4703884 * 2 ^ 59
def prefixEnd_4703884 : Nat := 4983230072969 + 3 ^ 40 * 4703884 * 2
def baseEnd_4703884 : Nat := 805117811664593088639079

theorem tailTrace_4703884 : CollatzResearch.WordTrace tailWord_4703884 prefixEnd_4703884 805117811664593088639079 := by
  unfold tailWord_4703884
  simp only [CollatzResearch.WordTrace]
  refine ⟨85782372045319551136799353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114376496060426068182399137 85782372045319551136799353)
  ·
    refine ⟨64336779033989663352599515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85782372045319551136799353 64336779033989663352599515)
    ·
      refine ⟨96505168550984495028899273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64336779033989663352599515 96505168550984495028899273)
      ·
        refine ⟨72378876413238371271674455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96505168550984495028899273 72378876413238371271674455)
        ·
          refine ⟨108568314619857556907511683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72378876413238371271674455 108568314619857556907511683)
          ·
            refine ⟨162852471929786335361267525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108568314619857556907511683 162852471929786335361267525)
            ·
              refine ⟨30534838486834937880237661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162852471929786335361267525 30534838486834937880237661)
              ·
                refine ⟨11450564432563101705089123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30534838486834937880237661 11450564432563101705089123)
                ·
                  refine ⟨17175846648844652557633685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11450564432563101705089123 17175846648844652557633685)
                  ·
                    refine ⟨805117811664593088639079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17175846648844652557633685 805117811664593088639079)
                    ·
                      rfl

theorem cell23_4703884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_4703884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703884 prefixEnd_4703884 := by exact prefixLift 4703884
  have htrace : WordTrace (prefixWord ++ tailWord_4703884) baseStart_4703884 baseEnd_4703884 := by
    simpa [prefixWord, tailWord_4703884, baseEnd_4703884] using wordTrace_append hprefix tailTrace_4703884
  have hstable : (prefixWord ++ tailWord_4703884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703884).length < 2 ^ (prefixWord ++ tailWord_4703884).sum := by decide
  have hdescent : baseEnd_4703884 < baseStart_4703884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703914 : List Nat := [3, 1, 5, 14]
def baseStart_4703914 : Nat := 118140960795 + 4703914 * 2 ^ 59
def prefixEnd_4703914 : Nat := 4983230072969 + 3 ^ 40 * 4703914 * 2
def baseEnd_4703914 : Nat := 1104421051400738065177

theorem tailTrace_4703914 : CollatzResearch.WordTrace tailWord_4703914 prefixEnd_4703914 1104421051400738065177 := by
  unfold tailWord_4703914
  simp only [CollatzResearch.WordTrace]
  refine ⟨42891459570132604349297699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114377225520353611598127197 42891459570132604349297699)
  ·
    refine ⟨64337189355198906523946549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42891459570132604349297699 64337189355198906523946549)
    ·
      refine ⟨6031611502049897486619989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64337189355198906523946549 6031611502049897486619989)
      ·
        refine ⟨1104421051400738065177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 6031611502049897486619989 1104421051400738065177)
        ·
          rfl

theorem cell23_4703914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 14].length) (baseStart_4703914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703914 prefixEnd_4703914 := by exact prefixLift 4703914
  have htrace : WordTrace (prefixWord ++ tailWord_4703914) baseStart_4703914 baseEnd_4703914 := by
    simpa [prefixWord, tailWord_4703914, baseEnd_4703914] using wordTrace_append hprefix tailTrace_4703914
  have hstable : (prefixWord ++ tailWord_4703914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703914).length < 2 ^ (prefixWord ++ tailWord_4703914).sum := by decide
  have hdescent : baseEnd_4703914 < baseStart_4703914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703944 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 2, 7]
def baseStart_4703944 : Nat := 118140960795 + 4703944 * 2 ^ 59
def prefixEnd_4703944 : Nat := 4983230072969 + 3 ^ 40 * 4703944 * 2
def baseEnd_4703944 : Nat := 805128081277683010388987

theorem tailTrace_4703944 : CollatzResearch.WordTrace tailWord_4703944 prefixEnd_4703944 805128081277683010388987 := by
  unfold tailWord_4703944
  simp only [CollatzResearch.WordTrace]
  refine ⟨85783466235210866260391443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114377954980281155013855257 85783466235210866260391443)
  ·
    refine ⟨128675199352816299390587165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85783466235210866260391443 128675199352816299390587165)
    ·
      refine ⟨48253199757306112271470187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128675199352816299390587165 48253199757306112271470187)
      ·
        refine ⟨72379799635959168407205281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48253199757306112271470187 72379799635959168407205281)
        ·
          refine ⟨54284849726969376305403961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72379799635959168407205281 54284849726969376305403961)
          ·
            refine ⟨40713637295227032229052971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54284849726969376305403961 40713637295227032229052971)
            ·
              refine ⟨61070455942840548343579457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40713637295227032229052971 61070455942840548343579457)
              ·
                refine ⟨45802841957130411257684593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61070455942840548343579457 45802841957130411257684593)
                ·
                  refine ⟨34352131467847808443263445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45802841957130411257684593 34352131467847808443263445)
                  ·
                    refine ⟨805128081277683010388987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34352131467847808443263445 805128081277683010388987)
                    ·
                      rfl

theorem cell23_4703944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_4703944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703944 prefixEnd_4703944 := by exact prefixLift 4703944
  have htrace : WordTrace (prefixWord ++ tailWord_4703944) baseStart_4703944 baseEnd_4703944 := by
    simpa [prefixWord, tailWord_4703944, baseEnd_4703944] using wordTrace_append hprefix tailTrace_4703944
  have hstable : (prefixWord ++ tailWord_4703944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703944).length < 2 ^ (prefixWord ++ tailWord_4703944).sum := by decide
  have hdescent : baseEnd_4703944 < baseStart_4703944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703948 : List Nat := [2, 2, 1, 5, 2, 1, 3, 7]
def baseStart_4703948 : Nat := 118140960795 + 4703948 * 2 ^ 59
def prefixEnd_4703948 : Nat := 4983230072969 + 3 ^ 40 * 4703948 * 2
def baseEnd_4703948 : Nat := 89458751768728407982109

theorem tailTrace_4703948 : CollatzResearch.WordTrace tailWord_4703948 prefixEnd_4703948 89458751768728407982109 := by
  unfold tailWord_4703948
  simp only [CollatzResearch.WordTrace]
  refine ⟨85783539181203620601964249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114378052241604827469285665 85783539181203620601964249)
  ·
    refine ⟨64337654385902715451473187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85783539181203620601964249 64337654385902715451473187)
    ·
      refine ⟨96506481578854073177209781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64337654385902715451473187 96506481578854073177209781)
      ·
        refine ⟨9047482648017569360363417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96506481578854073177209781 9047482648017569360363417)
        ·
          refine ⟨6785611986013177020272563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9047482648017569360363417 6785611986013177020272563)
          ·
            refine ⟨10178417979019765530408845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785611986013177020272563 10178417979019765530408845)
            ·
              refine ⟨3816906742132412073903317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10178417979019765530408845 3816906742132412073903317)
              ·
                refine ⟨89458751768728407982109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3816906742132412073903317 89458751768728407982109)
                ·
                  rfl

theorem cell23_4703948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 7].length) (baseStart_4703948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703948 prefixEnd_4703948 := by exact prefixLift 4703948
  have htrace : WordTrace (prefixWord ++ tailWord_4703948) baseStart_4703948 baseEnd_4703948 := by
    simpa [prefixWord, tailWord_4703948, baseEnd_4703948] using wordTrace_append hprefix tailTrace_4703948
  have hstable : (prefixWord ++ tailWord_4703948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703948).length < 2 ^ (prefixWord ++ tailWord_4703948).sum := by decide
  have hdescent : baseEnd_4703948 < baseStart_4703948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4703984 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_4703984 : Nat := 118140960795 + 4703984 * 2 ^ 59
def prefixEnd_4703984 : Nat := 4983230072969 + 3 ^ 40 * 4703984 * 2
def baseEnd_4703984 : Nat := 2415404783059228874666777

theorem tailTrace_4703984 : CollatzResearch.WordTrace tailWord_4703984 prefixEnd_4703984 2415404783059228874666777 := by
  unfold tailWord_4703984
  simp only [CollatzResearch.WordTrace]
  refine ⟨85784195695138409676119503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114378927593517879568159337 85784195695138409676119503)
  ·
    refine ⟨128676293542707614514179255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85784195695138409676119503 128676293542707614514179255)
    ·
      refine ⟨193014440314061421771268883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128676293542707614514179255 193014440314061421771268883)
      ·
        refine ⟨289521660471092132656903325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193014440314061421771268883 289521660471092132656903325)
        ·
          refine ⟨108570622676659549746338747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289521660471092132656903325 108570622676659549746338747)
          ·
            refine ⟨162855934014989324619508121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108570622676659549746338747 162855934014989324619508121)
            ·
              refine ⟨122141950511241993464631091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162855934014989324619508121 122141950511241993464631091)
              ·
                refine ⟨183212925766862990196946637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122141950511241993464631091 183212925766862990196946637)
                ·
                  refine ⟨68704847162573621323854989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183212925766862990196946637 68704847162573621323854989)
                  ·
                    refine ⟨25764317685965107996445621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68704847162573621323854989 25764317685965107996445621)
                    ·
                      refine ⟨2415404783059228874666777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25764317685965107996445621 2415404783059228874666777)
                      ·
                        rfl

theorem cell23_4703984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_4703984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4703984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4703984 prefixEnd_4703984 := by exact prefixLift 4703984
  have htrace : WordTrace (prefixWord ++ tailWord_4703984) baseStart_4703984 baseEnd_4703984 := by
    simpa [prefixWord, tailWord_4703984, baseEnd_4703984] using wordTrace_append hprefix tailTrace_4703984
  have hstable : (prefixWord ++ tailWord_4703984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4703984).length < 2 ^ (prefixWord ++ tailWord_4703984).sum := by decide
  have hdescent : baseEnd_4703984 < baseStart_4703984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4703984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704001 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_4704001 : Nat := 118140960795 + 4704001 * 2 ^ 59
def prefixEnd_4704001 : Nat := 4983230072969 + 3 ^ 40 * 4704001 * 2
def baseEnd_4704001 : Nat := 2415413512230355308154199

theorem tailTrace_4704001 : CollatzResearch.WordTrace tailWord_4704001 prefixEnd_4704001 2415413512230355308154199 := by
  unfold tailWord_4704001
  simp only [CollatzResearch.WordTrace]
  refine ⟨171569011431215231255607857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114379340954143487503738571 171569011431215231255607857)
  ·
    refine ⟨128676758573411423441705893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171569011431215231255607857 128676758573411423441705893)
    ·
      refine ⟨24126892232514641895319855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128676758573411423441705893 24126892232514641895319855)
      ·
        refine ⟨36190338348771962842979783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24126892232514641895319855 36190338348771962842979783)
        ·
          refine ⟨54285507523157944264469675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36190338348771962842979783 54285507523157944264469675)
          ·
            refine ⟨81428261284736916396704513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54285507523157944264469675 81428261284736916396704513)
            ·
              refine ⟨61071195963552687297528385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81428261284736916396704513 61071195963552687297528385)
              ·
                refine ⟨45803396972664515473146289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61071195963552687297528385 45803396972664515473146289)
                ·
                  refine ⟨34352547729498386604859717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45803396972664515473146289 34352547729498386604859717)
                  ·
                    refine ⟨6441102699280947488411197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34352547729498386604859717 6441102699280947488411197)
                    ·
                      refine ⟨2415413512230355308154199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6441102699280947488411197 2415413512230355308154199)
                      ·
                        rfl

theorem cell23_4704001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_4704001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704001 prefixEnd_4704001 := by exact prefixLift 4704001
  have htrace : WordTrace (prefixWord ++ tailWord_4704001) baseStart_4704001 baseEnd_4704001 := by
    simpa [prefixWord, tailWord_4704001, baseEnd_4704001] using wordTrace_append hprefix tailTrace_4704001
  have hstable : (prefixWord ++ tailWord_4704001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704001).length < 2 ^ (prefixWord ++ tailWord_4704001).sum := by decide
  have hdescent : baseEnd_4704001 < baseStart_4704001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704002 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_4704002 : Nat := 118140960795 + 4704002 * 2 ^ 59
def prefixEnd_4704002 : Nat := 4983230072969 + 3 ^ 40 * 4704002 * 2
def baseEnd_4704002 : Nat := 2415414025711009804241695

theorem tailTrace_4704002 : CollatzResearch.WordTrace tailWord_4704002 prefixEnd_4704002 2415414025711009804241695 := by
  unfold tailWord_4704002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42892261976052902106598565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114379365269474405617596173 42892261976052902106598565)
  ·
    refine ⟨8042299120509919144987231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42892261976052902106598565 8042299120509919144987231)
    ·
      refine ⟨12063448680764878717480847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8042299120509919144987231 12063448680764878717480847)
      ·
        refine ⟨18095173021147318076221271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12063448680764878717480847 18095173021147318076221271)
        ·
          refine ⟨27142759531720977114331907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18095173021147318076221271 27142759531720977114331907)
          ·
            refine ⟨40714139297581465671497861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27142759531720977114331907 40714139297581465671497861)
            ·
              refine ⟨7633901118296524813405849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40714139297581465671497861 7633901118296524813405849)
              ·
                refine ⟨5725425838722393610054387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7633901118296524813405849 5725425838722393610054387)
                ·
                  refine ⟨8588138758083590415081581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5725425838722393610054387 8588138758083590415081581)
                  ·
                    refine ⟨3220552034281346405655593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8588138758083590415081581 3220552034281346405655593)
                    ·
                      refine ⟨2415414025711009804241695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220552034281346405655593 2415414025711009804241695)
                      ·
                        rfl

theorem cell23_4704002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_4704002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704002 prefixEnd_4704002 := by exact prefixLift 4704002
  have htrace : WordTrace (prefixWord ++ tailWord_4704002) baseStart_4704002 baseEnd_4704002 := by
    simpa [prefixWord, tailWord_4704002, baseEnd_4704002] using wordTrace_append hprefix tailTrace_4704002
  have hstable : (prefixWord ++ tailWord_4704002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704002).length < 2 ^ (prefixWord ++ tailWord_4704002).sum := by decide
  have hdescent : baseEnd_4704002 < baseStart_4704002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704018 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4704018 : Nat := 118140960795 + 4704018 * 2 ^ 59
def prefixEnd_4704018 : Nat := 4983230072969 + 3 ^ 40 * 4704018 * 2
def baseEnd_4704018 : Nat := 2415422241401481741641621

theorem tailTrace_4704018 : CollatzResearch.WordTrace tailWord_4704018 prefixEnd_4704018 2415422241401481741641621 := by
  unfold tailWord_4704018
  simp only [CollatzResearch.WordTrace]
  refine ⟨42892407868038410789744177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114379754314769095439317805 42892407868038410789744177)
  ·
    refine ⟨32169305901028808092308133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42892407868038410789744177 32169305901028808092308133)
    ·
      refine ⟨6031744856442901517307775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32169305901028808092308133 6031744856442901517307775)
      ·
        refine ⟨9047617284664352275961663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6031744856442901517307775 9047617284664352275961663)
        ·
          refine ⟨13571425926996528413942495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9047617284664352275961663 13571425926996528413942495)
          ·
            refine ⟨20357138890494792620913743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13571425926996528413942495 20357138890494792620913743)
            ·
              refine ⟨30535708335742188931370615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20357138890494792620913743 30535708335742188931370615)
              ·
                refine ⟨45803562503613283397055923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30535708335742188931370615 45803562503613283397055923)
                ·
                  refine ⟨68705343755419925095583885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45803562503613283397055923 68705343755419925095583885)
                  ·
                    refine ⟨25764503908282471910843957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68705343755419925095583885 25764503908282471910843957)
                    ·
                      refine ⟨2415422241401481741641621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25764503908282471910843957 2415422241401481741641621)
                      ·
                        rfl

theorem cell23_4704018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4704018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704018 prefixEnd_4704018 := by exact prefixLift 4704018
  have htrace : WordTrace (prefixWord ++ tailWord_4704018) baseStart_4704018 baseEnd_4704018 := by
    simpa [prefixWord, tailWord_4704018, baseEnd_4704018] using wordTrace_append hprefix tailTrace_4704018
  have hstable : (prefixWord ++ tailWord_4704018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704018).length < 2 ^ (prefixWord ++ tailWord_4704018).sum := by decide
  have hdescent : baseEnd_4704018 < baseStart_4704018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704049 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 2, 2, 2]
def baseStart_4704049 : Nat := 118140960795 + 4704049 * 2 ^ 59
def prefixEnd_4704049 : Nat := 4983230072969 + 3 ^ 40 * 4704049 * 2
def baseEnd_4704049 : Nat := 2415438159301771120353979

theorem tailTrace_4704049 : CollatzResearch.WordTrace tailWord_4704049 prefixEnd_4704049 2415438159301771120353979 := by
  unfold tailWord_4704049
  simp only [CollatzResearch.WordTrace]
  refine ⟨171570762135041335453355201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114380508090027556968903467 171570762135041335453355201)
  ·
    refine ⟨128678071601281001590016401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171570762135041335453355201 128678071601281001590016401)
    ·
      refine ⟨96508553700960751192512301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128678071601281001590016401 96508553700960751192512301)
      ·
        refine ⟨36190707637860281697192113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96508553700960751192512301 36190707637860281697192113)
        ·
          refine ⟨27143030728395211272894085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36190707637860281697192113 27143030728395211272894085)
          ·
            refine ⟨5089318261574102113667641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27143030728395211272894085 5089318261574102113667641)
            ·
              refine ⟨3816988696180576585250731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5089318261574102113667641 3816988696180576585250731)
              ·
                refine ⟨5725483044270864877876097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816988696180576585250731 5725483044270864877876097)
                ·
                  refine ⟨4294112283203148658407073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5725483044270864877876097 4294112283203148658407073)
                  ·
                    refine ⟨3220584212402361493805305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4294112283203148658407073 3220584212402361493805305)
                    ·
                      refine ⟨2415438159301771120353979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220584212402361493805305 2415438159301771120353979)
                      ·
                        rfl

theorem cell23_4704049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_4704049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704049 prefixEnd_4704049 := by exact prefixLift 4704049
  have htrace : WordTrace (prefixWord ++ tailWord_4704049) baseStart_4704049 baseEnd_4704049 := by
    simpa [prefixWord, tailWord_4704049, baseEnd_4704049] using wordTrace_append hprefix tailTrace_4704049
  have hstable : (prefixWord ++ tailWord_4704049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704049).length < 2 ^ (prefixWord ++ tailWord_4704049).sum := by decide
  have hdescent : baseEnd_4704049 < baseStart_4704049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704071 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_4704071 : Nat := 118140960795 + 4704071 * 2 ^ 59
def prefixEnd_4704071 : Nat := 4983230072969 + 3 ^ 40 * 4704071 * 2
def baseEnd_4704071 : Nat := 2415449455876170034278877

theorem tailTrace_4704071 : CollatzResearch.WordTrace tailWord_4704071 prefixEnd_4704071 2415449455876170034278877 := by
  unfold tailWord_4704071
  simp only [CollatzResearch.WordTrace]
  refine ⟨171571564540961633210656067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114381043027307755473770711 171571564540961633210656067)
  ·
    refine ⟨257357346811442449815984101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171571564540961633210656067 257357346811442449815984101)
    ·
      refine ⟨48254502527145459340497019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257357346811442449815984101 48254502527145459340497019)
      ·
        refine ⟨72381753790718189010745529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48254502527145459340497019 72381753790718189010745529)
        ·
          refine ⟨54286315343038641758059147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72381753790718189010745529 54286315343038641758059147)
          ·
            refine ⟨81429473014557962637088721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54286315343038641758059147 81429473014557962637088721)
            ·
              refine ⟨61072104760918471977816541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81429473014557962637088721 61072104760918471977816541)
              ·
                refine ⟨22902039285344426991681203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61072104760918471977816541 22902039285344426991681203)
                ·
                  refine ⟨34353058928016640487521805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22902039285344426991681203 34353058928016640487521805)
                  ·
                    refine ⟨12882397098006240182820677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34353058928016640487521805 12882397098006240182820677)
                    ·
                      refine ⟨2415449455876170034278877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12882397098006240182820677 2415449455876170034278877)
                      ·
                        rfl

theorem cell23_4704071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_4704071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704071 prefixEnd_4704071 := by exact prefixLift 4704071
  have htrace : WordTrace (prefixWord ++ tailWord_4704071) baseStart_4704071 baseEnd_4704071 := by
    simpa [prefixWord, tailWord_4704071, baseEnd_4704071] using wordTrace_append hprefix tailTrace_4704071
  have hstable : (prefixWord ++ tailWord_4704071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704071).length < 2 ^ (prefixWord ++ tailWord_4704071).sum := by decide
  have hdescent : baseEnd_4704071 < baseStart_4704071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704101 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_4704101 : Nat := 118140960795 + 4704101 * 2 ^ 59
def prefixEnd_4704101 : Nat := 4983230072969 + 3 ^ 40 * 4704101 * 2
def baseEnd_4704101 : Nat := 2415464860295804916903739

theorem tailTrace_4704101 : CollatzResearch.WordTrace tailWord_4704101 prefixEnd_4704101 2415464860295804916903739 := by
  unfold tailWord_4704101
  simp only [CollatzResearch.WordTrace]
  refine ⟨171572658730852948334248157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114381772487235298889498771 171572658730852948334248157)
  ·
    refine ⟨64339747024069855625343059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171572658730852948334248157 64339747024069855625343059)
    ·
      refine ⟨96509620536104783438014589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64339747024069855625343059 96509620536104783438014589)
      ·
        refine ⟨36191107701039293789255471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96509620536104783438014589 36191107701039293789255471)
        ·
          refine ⟨54286661551558940683883207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36191107701039293789255471 54286661551558940683883207)
          ·
            refine ⟨81429992327338411025824811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54286661551558940683883207 81429992327338411025824811)
            ·
              refine ⟨122144988491007616538737217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81429992327338411025824811 122144988491007616538737217)
              ·
                refine ⟨91608741368255712404052913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122144988491007616538737217 91608741368255712404052913)
                ·
                  refine ⟨68706556026191784303039685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91608741368255712404052913 68706556026191784303039685)
                  ·
                    refine ⟨12882479254910959556819941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68706556026191784303039685 12882479254910959556819941)
                    ·
                      refine ⟨2415464860295804916903739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12882479254910959556819941 2415464860295804916903739)
                      ·
                        rfl

theorem cell23_4704101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_4704101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704101 prefixEnd_4704101 := by exact prefixLift 4704101
  have htrace : WordTrace (prefixWord ++ tailWord_4704101) baseStart_4704101 baseEnd_4704101 := by
    simpa [prefixWord, tailWord_4704101, baseEnd_4704101] using wordTrace_append hprefix tailTrace_4704101
  have hstable : (prefixWord ++ tailWord_4704101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704101).length < 2 ^ (prefixWord ++ tailWord_4704101).sum := by decide
  have hdescent : baseEnd_4704101 < baseStart_4704101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704148 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4704148 : Nat := 118140960795 + 4704148 * 2 ^ 59
def prefixEnd_4704148 : Nat := 4983230072969 + 3 ^ 40 * 4704148 * 2
def baseEnd_4704148 : Nat := 2415488993886566233016023

theorem tailTrace_4704148 : CollatzResearch.WordTrace tailWord_4704148 prefixEnd_4704148 2415488993886566233016023 := by
  unfold tailWord_4704148
  simp only [CollatzResearch.WordTrace]
  refine ⟨85787186480841337680604549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114382915307788450240806065 85787186480841337680604549)
  ·
    refine ⟨16085097465157750815113353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85787186480841337680604549 16085097465157750815113353)
    ·
      refine ⟨12063823098868313111335015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16085097465157750815113353 12063823098868313111335015)
      ·
        refine ⟨18095734648302469667002523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12063823098868313111335015 18095734648302469667002523)
        ·
          refine ⟨27143601972453704500503785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18095734648302469667002523 27143601972453704500503785)
          ·
            refine ⟨20357701479340278375377839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27143601972453704500503785 20357701479340278375377839)
            ·
              refine ⟨30536552219010417563066759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20357701479340278375377839 30536552219010417563066759)
              ·
                refine ⟨45804828328515626344600139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30536552219010417563066759 45804828328515626344600139)
                ·
                  refine ⟨68707242492773439516900209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45804828328515626344600139 68707242492773439516900209)
                  ·
                    refine ⟨51530431869580079637675157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68707242492773439516900209 51530431869580079637675157)
                    ·
                      refine ⟨2415488993886566233016023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51530431869580079637675157 2415488993886566233016023)
                      ·
                        rfl

theorem cell23_4704148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4704148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704148 prefixEnd_4704148 := by exact prefixLift 4704148
  have htrace : WordTrace (prefixWord ++ tailWord_4704148) baseStart_4704148 baseEnd_4704148 := by
    simpa [prefixWord, tailWord_4704148, baseEnd_4704148] using wordTrace_append hprefix tailTrace_4704148
  have hstable : (prefixWord ++ tailWord_4704148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704148).length < 2 ^ (prefixWord ++ tailWord_4704148).sum := by decide
  have hdescent : baseEnd_4704148 < baseStart_4704148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704162 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 6]
def baseStart_4704162 : Nat := 118140960795 + 4704162 * 2 ^ 59
def prefixEnd_4704162 : Nat := 4983230072969 + 3 ^ 40 * 4704162 * 2
def baseEnd_4704162 : Nat := 268388464735081019804551

theorem tailTrace_4704162 : CollatzResearch.WordTrace tailWord_4704162 prefixEnd_4704162 268388464735081019804551 := by
  unfold tailWord_4704162
  simp only [CollatzResearch.WordTrace]
  refine ⟨42893720895907988938054685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114383255722421303834812493 42893720895907988938054685)
  ·
    refine ⟨16085145335965495851770507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42893720895907988938054685 16085145335965495851770507)
    ·
      refine ⟨24127718003948243777655761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16085145335965495851770507 24127718003948243777655761)
      ·
        refine ⟨18095788502961182833241821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24127718003948243777655761 18095788502961182833241821)
        ·
          refine ⟨6785920688610443562465683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18095788502961182833241821 6785920688610443562465683)
          ·
            refine ⟨10178881032915665343698525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785920688610443562465683 10178881032915665343698525)
            ·
              refine ⟨3817080387343374503886947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10178881032915665343698525 3817080387343374503886947)
              ·
                refine ⟨5725620581015061755830421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817080387343374503886947 5725620581015061755830421)
                ·
                  refine ⟨268388464735081019804551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5725620581015061755830421 268388464735081019804551)
                  ·
                    rfl

theorem cell23_4704162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_4704162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704162 prefixEnd_4704162 := by exact prefixLift 4704162
  have htrace : WordTrace (prefixWord ++ tailWord_4704162) baseStart_4704162 baseEnd_4704162 := by
    simpa [prefixWord, tailWord_4704162, baseEnd_4704162] using wordTrace_append hprefix tailTrace_4704162
  have hstable : (prefixWord ++ tailWord_4704162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704162).length < 2 ^ (prefixWord ++ tailWord_4704162).sum := by decide
  have hdescent : baseEnd_4704162 < baseStart_4704162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704178 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_4704178 : Nat := 118140960795 + 4704178 * 2 ^ 59
def prefixEnd_4704178 : Nat := 4983230072969 + 3 ^ 40 * 4704178 * 2
def baseEnd_4704178 : Nat := 2415504398306201115640885

theorem tailTrace_4704178 : CollatzResearch.WordTrace tailWord_4704178 prefixEnd_4704178 2415504398306201115640885 := by
  unfold tailWord_4704178
  simp only [CollatzResearch.WordTrace]
  refine ⟨42893866787893497621200297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114383644767715993656534125 42893866787893497621200297)
  ·
    refine ⟨32170400090920123215900223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42893866787893497621200297 32170400090920123215900223)
    ·
      refine ⟨48255600136380184823850335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32170400090920123215900223 48255600136380184823850335)
      ·
        refine ⟨72383400204570277235775503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48255600136380184823850335 72383400204570277235775503)
        ·
          refine ⟨108575100306855415853663255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72383400204570277235775503 108575100306855415853663255)
          ·
            refine ⟨162862650460283123780494883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108575100306855415853663255 162862650460283123780494883)
            ·
              refine ⟨244293975690424685670742325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162862650460283123780494883 244293975690424685670742325)
              ·
                refine ⟨22902560220977314281632093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244293975690424685670742325 22902560220977314281632093)
                ·
                  refine ⟨8588460082866492855612035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22902560220977314281632093 8588460082866492855612035)
                  ·
                    refine ⟨12882690124299739283418053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8588460082866492855612035 12882690124299739283418053)
                    ·
                      refine ⟨2415504398306201115640885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12882690124299739283418053 2415504398306201115640885)
                      ·
                        rfl

theorem cell23_4704178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_4704178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704178 prefixEnd_4704178 := by exact prefixLift 4704178
  have htrace : WordTrace (prefixWord ++ tailWord_4704178) baseStart_4704178 baseEnd_4704178 := by
    simpa [prefixWord, tailWord_4704178, baseEnd_4704178] using wordTrace_append hprefix tailTrace_4704178
  have hstable : (prefixWord ++ tailWord_4704178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704178).length < 2 ^ (prefixWord ++ tailWord_4704178).sum := by decide
  have hdescent : baseEnd_4704178 < baseStart_4704178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704189 : List Nat := [1, 4, 1, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_4704189 : Nat := 118140960795 + 4704189 * 2 ^ 59
def prefixEnd_4704189 : Nat := 4983230072969 + 3 ^ 40 * 4704189 * 2
def baseEnd_4704189 : Nat := 2415510046593400572603335

theorem tailTrace_4704189 : CollatzResearch.WordTrace tailWord_4704189 prefixEnd_4704189 2415510046593400572603335 := by
  unfold tailWord_4704189
  simp only [CollatzResearch.WordTrace]
  refine ⟨171575868354534139363451621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114383912236356092908967747 171575868354534139363451621)
  ·
    refine ⟨32170475316475151130647179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171575868354534139363451621 32170475316475151130647179)
    ·
      refine ⟨48255712974712726695970769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32170475316475151130647179 48255712974712726695970769)
      ·
        refine ⟨36191784731034545021978077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48255712974712726695970769 36191784731034545021978077)
        ·
          refine ⟨13571919274137954383241779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36191784731034545021978077 13571919274137954383241779)
          ·
            refine ⟨20357878911206931574862669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13571919274137954383241779 20357878911206931574862669)
            ·
              refine ⟨7634204591702599340573501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20357878911206931574862669 7634204591702599340573501)
              ·
                refine ⟨2862826721888474752715063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7634204591702599340573501 2862826721888474752715063)
                ·
                  refine ⟨4294240082832712129072595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862826721888474752715063 4294240082832712129072595)
                  ·
                    refine ⟨6441360124249068193608893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4294240082832712129072595 6441360124249068193608893)
                    ·
                      refine ⟨2415510046593400572603335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6441360124249068193608893 2415510046593400572603335)
                      ·
                        rfl

theorem cell23_4704189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_4704189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704189 prefixEnd_4704189 := by exact prefixLift 4704189
  have htrace : WordTrace (prefixWord ++ tailWord_4704189) baseStart_4704189 baseEnd_4704189 := by
    simpa [prefixWord, tailWord_4704189, baseEnd_4704189] using wordTrace_append hprefix tailTrace_4704189
  have hstable : (prefixWord ++ tailWord_4704189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704189).length < 2 ^ (prefixWord ++ tailWord_4704189).sum := by decide
  have hdescent : baseEnd_4704189 < baseStart_4704189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704226 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4704226 : Nat := 118140960795 + 4704226 * 2 ^ 59
def prefixEnd_4704226 : Nat := 4983230072969 + 3 ^ 40 * 4704226 * 2
def baseEnd_4704226 : Nat := 805176348459205642613555

theorem tailTrace_4704226 : CollatzResearch.WordTrace tailWord_4704226 prefixEnd_4704226 805176348459205642613555 := by
  unfold tailWord_4704226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42894304463850023670637133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114384811903600063121699021 42894304463850023670637133)
  ·
    refine ⟨16085364173943758876488925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42894304463850023670637133 16085364173943758876488925)
    ·
      refine ⟨6032011565228909578683347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16085364173943758876488925 6032011565228909578683347)
      ·
        refine ⟨9048017347843364368025021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6032011565228909578683347 9048017347843364368025021)
        ·
          refine ⟨3393006505441261638009383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9048017347843364368025021 3393006505441261638009383)
          ·
            refine ⟨5089509758161892457014075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393006505441261638009383 5089509758161892457014075)
            ·
              refine ⟨7634264637242838685521113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5089509758161892457014075 7634264637242838685521113)
              ·
                refine ⟨5725698477932129014140835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7634264637242838685521113 5725698477932129014140835)
                ·
                  refine ⟨8588547716898193521211253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5725698477932129014140835 8588547716898193521211253)
                  ·
                    refine ⟨805176348459205642613555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8588547716898193521211253 805176348459205642613555)
                    ·
                      rfl

theorem cell23_4704226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4704226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704226 prefixEnd_4704226 := by exact prefixLift 4704226
  have htrace : WordTrace (prefixWord ++ tailWord_4704226) baseStart_4704226 baseEnd_4704226 := by
    simpa [prefixWord, tailWord_4704226, baseEnd_4704226] using wordTrace_append hprefix tailTrace_4704226
  have hstable : (prefixWord ++ tailWord_4704226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704226).length < 2 ^ (prefixWord ++ tailWord_4704226).sum := by decide
  have hdescent : baseEnd_4704226 < baseStart_4704226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704263 : List Nat := [1, 1, 4, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_4704263 : Nat := 118140960795 + 4704263 * 2 ^ 59
def prefixEnd_4704263 : Nat := 4983230072969 + 3 ^ 40 * 4704263 * 2
def baseEnd_4704263 : Nat := 2415548044161833283077995

theorem tailTrace_4704263 : CollatzResearch.WordTrace tailWord_4704263 prefixEnd_4704263 2415548044161833283077995 := by
  unfold tailWord_4704263
  simp only [CollatzResearch.WordTrace]
  refine ⟨171578567356266050001645443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114385711570844033334430295 171578567356266050001645443)
  ·
    refine ⟨257367851034399075002468165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171578567356266050001645443 257367851034399075002468165)
    ·
      refine ⟨48256472068949826562962781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257367851034399075002468165 48256472068949826562962781)
      ·
        refine ⟨18096177025856184961111043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48256472068949826562962781 18096177025856184961111043)
        ·
          refine ⟨27144265538784277441666565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18096177025856184961111043 27144265538784277441666565)
          ·
            refine ⟨5089549788522052020312481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27144265538784277441666565 5089549788522052020312481)
            ·
              refine ⟨3817162341391539015234361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5089549788522052020312481 3817162341391539015234361)
              ·
                refine ⟨2862871756043654261425771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3817162341391539015234361 2862871756043654261425771)
                ·
                  refine ⟨4294307634065481392138657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862871756043654261425771 4294307634065481392138657)
                  ·
                    refine ⟨3220730725549111044103993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4294307634065481392138657 3220730725549111044103993)
                    ·
                      refine ⟨2415548044161833283077995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220730725549111044103993 2415548044161833283077995)
                      ·
                        rfl

theorem cell23_4704263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_4704263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704263 prefixEnd_4704263 := by exact prefixLift 4704263
  have htrace : WordTrace (prefixWord ++ tailWord_4704263) baseStart_4704263 baseEnd_4704263 := by
    simpa [prefixWord, tailWord_4704263, baseEnd_4704263] using wordTrace_append hprefix tailTrace_4704263
  have hstable : (prefixWord ++ tailWord_4704263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704263).length < 2 ^ (prefixWord ++ tailWord_4704263).sum := by decide
  have hdescent : baseEnd_4704263 < baseStart_4704263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704268 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_4704268 : Nat := 118140960795 + 4704268 * 2 ^ 59
def prefixEnd_4704268 : Nat := 4983230072969 + 3 ^ 40 * 4704268 * 2
def baseEnd_4704268 : Nat := 2415550611565105763515471

theorem tailTrace_4704268 : CollatzResearch.WordTrace tailWord_4704268 prefixEnd_4704268 2415550611565105763515471 := by
  unfold tailWord_4704268
  simp only [CollatzResearch.WordTrace]
  refine ⟨85789374860623967927788729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114385833147498623903718305 85789374860623967927788729)
  ·
    refine ⟨64342031145467975945841547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85789374860623967927788729 64342031145467975945841547)
    ·
      refine ⟨96513046718201963918762321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64342031145467975945841547 96513046718201963918762321)
      ·
        refine ⟨72384785038651472939071741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96513046718201963918762321 72384785038651472939071741)
        ·
          refine ⟨27144294389494302352151903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72384785038651472939071741 27144294389494302352151903)
          ·
            refine ⟨40716441584241453528227855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27144294389494302352151903 40716441584241453528227855)
            ·
              refine ⟨61074662376362180292341783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40716441584241453528227855 61074662376362180292341783)
              ·
                refine ⟨91611993564543270438512675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61074662376362180292341783 91611993564543270438512675)
                ·
                  refine ⟨137417990346814905657769013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91611993564543270438512675 137417990346814905657769013)
                  ·
                    refine ⟨12882936595013897405415845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137417990346814905657769013 12882936595013897405415845)
                    ·
                      refine ⟨2415550611565105763515471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12882936595013897405415845 2415550611565105763515471)
                      ·
                        rfl

theorem cell23_4704268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_4704268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704268 prefixEnd_4704268 := by exact prefixLift 4704268
  have htrace : WordTrace (prefixWord ++ tailWord_4704268) baseStart_4704268 baseEnd_4704268 := by
    simpa [prefixWord, tailWord_4704268, baseEnd_4704268] using wordTrace_append hprefix tailTrace_4704268
  have hstable : (prefixWord ++ tailWord_4704268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704268).length < 2 ^ (prefixWord ++ tailWord_4704268).sum := by decide
  have hdescent : baseEnd_4704268 < baseStart_4704268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704306 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_4704306 : Nat := 118140960795 + 4704306 * 2 ^ 59
def prefixEnd_4704306 : Nat := 4983230072969 + 3 ^ 40 * 4704306 * 2
def baseEnd_4704306 : Nat := 2415570123829976614840297

theorem tailTrace_4704306 : CollatzResearch.WordTrace tailWord_4704306 prefixEnd_4704306 2415570123829976614840297 := by
  unfold tailWord_4704306
  simp only [CollatzResearch.WordTrace]
  refine ⟨42895033923777567086365193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114386757130073512230307181 42895033923777567086365193)
  ·
    refine ⟨32171275442833175314773895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42895033923777567086365193 32171275442833175314773895)
    ·
      refine ⟨48256913164249762972160843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32171275442833175314773895 48256913164249762972160843)
      ·
        refine ⟨72385369746374644458241265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48256913164249762972160843 72385369746374644458241265)
        ·
          refine ⟨54289027309780983343680949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72385369746374644458241265 54289027309780983343680949)
          ·
            refine ⟨5089596310291967188470089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54289027309780983343680949 5089596310291967188470089)
            ·
              refine ⟨3817197232718975391352567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5089596310291967188470089 3817197232718975391352567)
              ·
                refine ⟨5725795849078463087028851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817197232718975391352567 5725795849078463087028851)
                ·
                  refine ⟨8588693773617694630543277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5725795849078463087028851 8588693773617694630543277)
                  ·
                    refine ⟨3220760165106635486453729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8588693773617694630543277 3220760165106635486453729)
                    ·
                      refine ⟨2415570123829976614840297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220760165106635486453729 2415570123829976614840297)
                      ·
                        rfl

theorem cell23_4704306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_4704306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704306 prefixEnd_4704306 := by exact prefixLift 4704306
  have htrace : WordTrace (prefixWord ++ tailWord_4704306) baseStart_4704306 baseEnd_4704306 := by
    simpa [prefixWord, tailWord_4704306, baseEnd_4704306] using wordTrace_append hprefix tailTrace_4704306
  have hstable : (prefixWord ++ tailWord_4704306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704306).length < 2 ^ (prefixWord ++ tailWord_4704306).sum := by decide
  have hdescent : baseEnd_4704306 < baseStart_4704306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704319 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 2, 2, 2]
def baseStart_4704319 : Nat := 118140960795 + 4704319 * 2 ^ 59
def prefixEnd_4704319 : Nat := 4983230072969 + 3 ^ 40 * 4704319 * 2
def baseEnd_4704319 : Nat := 2415576799078485063977737

theorem tailTrace_4704319 : CollatzResearch.WordTrace tailWord_4704319 prefixEnd_4704319 2415576799078485063977737 := by
  unfold tailWord_4704319
  simp only [CollatzResearch.WordTrace]
  refine ⟨171580609844063171565684011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114387073229375447710456007 171580609844063171565684011)
  ·
    refine ⟨257370914766094757348526017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171580609844063171565684011 257370914766094757348526017)
    ·
      refine ⟨193028186074571068011394513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257370914766094757348526017 193028186074571068011394513)
      ·
        refine ⟨144771139555928301008545885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193028186074571068011394513 144771139555928301008545885)
        ·
          refine ⟨54289177333473112878204707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144771139555928301008545885 54289177333473112878204707)
          ·
            refine ⟨81433766000209669317307061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54289177333473112878204707 81433766000209669317307061)
            ·
              refine ⟨7634415562519656498497537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81433766000209669317307061 7634415562519656498497537)
              ·
                refine ⟨5725811671889742373873153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7634415562519656498497537 5725811671889742373873153)
                ·
                  refine ⟨4294358753917306780404865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5725811671889742373873153 4294358753917306780404865)
                  ·
                    refine ⟨3220769065437980085303649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4294358753917306780404865 3220769065437980085303649)
                    ·
                      refine ⟨2415576799078485063977737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220769065437980085303649 2415576799078485063977737)
                      ·
                        rfl

theorem cell23_4704319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_4704319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704319 prefixEnd_4704319 := by exact prefixLift 4704319
  have htrace : WordTrace (prefixWord ++ tailWord_4704319) baseStart_4704319 baseEnd_4704319 := by
    simpa [prefixWord, tailWord_4704319, baseEnd_4704319] using wordTrace_append hprefix tailTrace_4704319
  have hstable : (prefixWord ++ tailWord_4704319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704319).length < 2 ^ (prefixWord ++ tailWord_4704319).sum := by decide
  have hdescent : baseEnd_4704319 < baseStart_4704319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704365 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4704365 : Nat := 118140960795 + 4704365 * 2 ^ 59
def prefixEnd_4704365 : Nat := 4983230072969 + 3 ^ 40 * 4704365 * 2
def baseEnd_4704365 : Nat := 2415600419188591884002525

theorem tailTrace_4704365 : CollatzResearch.WordTrace tailWord_4704365 prefixEnd_4704365 2415600419188591884002525 := by
  unfold tailWord_4704365
  simp only [CollatzResearch.WordTrace]
  refine ⟨171582287601896521421858549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114388191734597680947905699 171582287601896521421858549)
  ·
    refine ⟨16085839462677798883299239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171582287601896521421858549 16085839462677798883299239)
    ·
      refine ⟨24128759194016698324948859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16085839462677798883299239 24128759194016698324948859)
      ·
        refine ⟨36193138791025047487423289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24128759194016698324948859 36193138791025047487423289)
        ·
          refine ⟨27144854093268785615567467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36193138791025047487423289 27144854093268785615567467)
          ·
            refine ⟨40717281139903178423351201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27144854093268785615567467 40717281139903178423351201)
            ·
              refine ⟨30537960854927383817513401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40717281139903178423351201 30537960854927383817513401)
              ·
                refine ⟨22903470641195537863135051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30537960854927383817513401 22903470641195537863135051)
                ·
                  refine ⟨34355205961793306794702577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22903470641195537863135051 34355205961793306794702577)
                  ·
                    refine ⟨25766404471344980096026933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34355205961793306794702577 25766404471344980096026933)
                    ·
                      refine ⟨2415600419188591884002525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25766404471344980096026933 2415600419188591884002525)
                      ·
                        rfl

theorem cell23_4704365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4704365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704365 prefixEnd_4704365 := by exact prefixLift 4704365
  have htrace : WordTrace (prefixWord ++ tailWord_4704365) baseStart_4704365 baseEnd_4704365 := by
    simpa [prefixWord, tailWord_4704365, baseEnd_4704365] using wordTrace_append hprefix tailTrace_4704365
  have hstable : (prefixWord ++ tailWord_4704365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704365).length < 2 ^ (prefixWord ++ tailWord_4704365).sum := by decide
  have hdescent : baseEnd_4704365 < baseStart_4704365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704375 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_4704375 : Nat := 118140960795 + 4704375 * 2 ^ 59
def prefixEnd_4704375 : Nat := 4983230072969 + 3 ^ 40 * 4704375 * 2
def baseEnd_4704375 : Nat := 2415605553995136844877479

theorem tailTrace_4704375 : CollatzResearch.WordTrace tailWord_4704375 prefixEnd_4704375 2415605553995136844877479 := by
  unfold tailWord_4704375
  simp only [CollatzResearch.WordTrace]
  refine ⟨171582652331860293129722579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114388434887906862086481719 171582652331860293129722579)
  ·
    refine ⟨257373978497790439694583869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171582652331860293129722579 257373978497790439694583869)
    ·
      refine ⟨96515241936671414885468951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257373978497790439694583869 96515241936671414885468951)
      ·
        refine ⟨144772862905007122328203427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96515241936671414885468951 144772862905007122328203427)
        ·
          refine ⟨217159294357510683492305141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144772862905007122328203427 217159294357510683492305141)
          ·
            refine ⟨20358683846016626577403607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217159294357510683492305141 20358683846016626577403607)
            ·
              refine ⟨30538025769024939866105411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20358683846016626577403607 30538025769024939866105411)
              ·
                refine ⟨45807038653537409799158117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30538025769024939866105411 45807038653537409799158117)
                ·
                  refine ⟨8588819747538264337342147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45807038653537409799158117 8588819747538264337342147)
                  ·
                    refine ⟨12883229621307396506013221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8588819747538264337342147 12883229621307396506013221)
                    ·
                      refine ⟨2415605553995136844877479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12883229621307396506013221 2415605553995136844877479)
                      ·
                        rfl

theorem cell23_4704375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_4704375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704375 prefixEnd_4704375 := by exact prefixLift 4704375
  have htrace : WordTrace (prefixWord ++ tailWord_4704375) baseStart_4704375 baseEnd_4704375 := by
    simpa [prefixWord, tailWord_4704375, baseEnd_4704375] using wordTrace_append hprefix tailTrace_4704375
  have hstable : (prefixWord ++ tailWord_4704375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704375).length < 2 ^ (prefixWord ++ tailWord_4704375).sum := by decide
  have hdescent : baseEnd_4704375 < baseStart_4704375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704402 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4704402 : Nat := 118140960795 + 4704402 * 2 ^ 59
def prefixEnd_4704402 : Nat := 4983230072969 + 3 ^ 40 * 4704402 * 2
def baseEnd_4704402 : Nat := 805206472657602746413285

theorem tailTrace_4704402 : CollatzResearch.WordTrace tailWord_4704402 prefixEnd_4704402 805206472657602746413285 := by
  unfold tailWord_4704402
  simp only [CollatzResearch.WordTrace]
  refine ⟨42895909275690619185238865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114389091401841651160636973 42895909275690619185238865)
  ·
    refine ⟨32171931956767964388929149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42895909275690619185238865 32171931956767964388929149)
    ·
      refine ⟨12064474483787986645848431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32171931956767964388929149 12064474483787986645848431)
      ·
        refine ⟨18096711725681979968772647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12064474483787986645848431 18096711725681979968772647)
        ·
          refine ⟨27145067588522969953158971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18096711725681979968772647 27145067588522969953158971)
          ·
            refine ⟨40717601382784454929738457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27145067588522969953158971 40717601382784454929738457)
            ·
              refine ⟨30538201037088341197303843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40717601382784454929738457 30538201037088341197303843)
              ·
                refine ⟨45807301555632511795955765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30538201037088341197303843 45807301555632511795955765)
                ·
                  refine ⟨4294434520840547980870853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45807301555632511795955765 4294434520840547980870853)
                  ·
                    refine ⟨805206472657602746413285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294434520840547980870853 805206472657602746413285)
                    ·
                      rfl

theorem cell23_4704402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4704402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704402 prefixEnd_4704402 := by exact prefixLift 4704402
  have htrace : WordTrace (prefixWord ++ tailWord_4704402) baseStart_4704402 baseEnd_4704402 := by
    simpa [prefixWord, tailWord_4704402, baseEnd_4704402] using wordTrace_append hprefix tailTrace_4704402
  have hstable : (prefixWord ++ tailWord_4704402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704402).length < 2 ^ (prefixWord ++ tailWord_4704402).sum := by decide
  have hdescent : baseEnd_4704402 < baseStart_4704402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704429 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_4704429 : Nat := 118140960795 + 4704429 * 2 ^ 59
def prefixEnd_4704429 : Nat := 4983230072969 + 3 ^ 40 * 4704429 * 2
def baseEnd_4704429 : Nat := 2415633281950479633602231

theorem tailTrace_4704429 : CollatzResearch.WordTrace tailWord_4704429 prefixEnd_4704429 2415633281950479633602231 := by
  unfold tailWord_4704429
  simp only [CollatzResearch.WordTrace]
  refine ⟨171584621873664660352188341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114389747915776440234792227 171584621873664660352188341)
  ·
    refine ⟨16086058300656061908017657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171584621873664660352188341 16086058300656061908017657)
    ·
      refine ⟨12064543725492046431013243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16086058300656061908017657 12064543725492046431013243)
      ·
        refine ⟨18096815588238069646519865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12064543725492046431013243 18096815588238069646519865)
        ·
          refine ⟨13572611691178552234889899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18096815588238069646519865 13572611691178552234889899)
          ·
            refine ⟨20358917536767828352334849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13572611691178552234889899 20358917536767828352334849)
            ·
              refine ⟨15269188152575871264251137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20358917536767828352334849 15269188152575871264251137)
              ·
                refine ⟨11451891114431903448188353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15269188152575871264251137 11451891114431903448188353)
                ·
                  refine ⟨8588918335823927586141265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11451891114431903448188353 8588918335823927586141265)
                  ·
                    refine ⟨6441688751867945689605949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8588918335823927586141265 6441688751867945689605949)
                    ·
                      refine ⟨2415633281950479633602231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6441688751867945689605949 2415633281950479633602231)
                      ·
                        rfl

theorem cell23_4704429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_4704429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704429 prefixEnd_4704429 := by exact prefixLift 4704429
  have htrace : WordTrace (prefixWord ++ tailWord_4704429) baseStart_4704429 baseEnd_4704429 := by
    simpa [prefixWord, tailWord_4704429, baseEnd_4704429] using wordTrace_append hprefix tailTrace_4704429
  have hstable : (prefixWord ++ tailWord_4704429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704429).length < 2 ^ (prefixWord ++ tailWord_4704429).sum := by decide
  have hdescent : baseEnd_4704429 < baseStart_4704429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704462 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_4704462 : Nat := 118140960795 + 4704462 * 2 ^ 59
def prefixEnd_4704462 : Nat := 4983230072969 + 3 ^ 40 * 4704462 * 2
def baseEnd_4704462 : Nat := 805216742270692668163193

theorem tailTrace_4704462 : CollatzResearch.WordTrace tailWord_4704462 prefixEnd_4704462 805216742270692668163193 := by
  unfold tailWord_4704462
  simp only [CollatzResearch.WordTrace]
  refine ⟨21448228185318138373517455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114390550321696737992093093 21448228185318138373517455)
  ·
    refine ⟨32172342277977207560276183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21448228185318138373517455 32172342277977207560276183)
    ·
      refine ⟨48258513416965811340414275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32172342277977207560276183 48258513416965811340414275)
      ·
        refine ⟨72387770125448717010621413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48258513416965811340414275 72387770125448717010621413)
        ·
          refine ⟨13572706898521634439491515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72387770125448717010621413 13572706898521634439491515)
          ·
            refine ⟨20359060347782451659237273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13572706898521634439491515 20359060347782451659237273)
            ·
              refine ⟨15269295260836838744427955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20359060347782451659237273 15269295260836838744427955)
              ·
                refine ⟨22903942891255258116641933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15269295260836838744427955 22903942891255258116641933)
                ·
                  refine ⟨8588978584220721793740725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22903942891255258116641933 8588978584220721793740725)
                  ·
                    refine ⟨805216742270692668163193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8588978584220721793740725 805216742270692668163193)
                    ·
                      rfl

theorem cell23_4704462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_4704462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704462 prefixEnd_4704462 := by exact prefixLift 4704462
  have htrace : WordTrace (prefixWord ++ tailWord_4704462) baseStart_4704462 baseEnd_4704462 := by
    simpa [prefixWord, tailWord_4704462, baseEnd_4704462] using wordTrace_append hprefix tailTrace_4704462
  have hstable : (prefixWord ++ tailWord_4704462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704462).length < 2 ^ (prefixWord ++ tailWord_4704462).sum := by decide
  have hdescent : baseEnd_4704462 < baseStart_4704462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704492 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_4704492 : Nat := 118140960795 + 4704492 * 2 ^ 59
def prefixEnd_4704492 : Nat := 4983230072969 + 3 ^ 40 * 4704492 * 2
def baseEnd_4704492 : Nat := 805221877077237629038147

theorem tailTrace_4704492 : CollatzResearch.WordTrace tailWord_4704492 prefixEnd_4704492 805221877077237629038147 := by
  unfold tailWord_4704492
  simp only [CollatzResearch.WordTrace]
  refine ⟨85793459836218211055865865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114391279781624281407821153 85793459836218211055865865)
  ·
    refine ⟨64345094877163658291899399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85793459836218211055865865 64345094877163658291899399)
    ·
      refine ⟨96517642315745487437849099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64345094877163658291899399 96517642315745487437849099)
      ·
        refine ⟨144776463473618231156773649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96517642315745487437849099 144776463473618231156773649)
        ·
          refine ⟨108582347605213673367580237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144776463473618231156773649 108582347605213673367580237)
          ·
            refine ⟨40718380351955127512842589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108582347605213673367580237 40718380351955127512842589)
            ·
              refine ⟨15269392631983172817315971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40718380351955127512842589 15269392631983172817315971)
              ·
                refine ⟨22904088947974759225973957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15269392631983172817315971 22904088947974759225973957)
                ·
                  refine ⟨4294516677745267354870117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22904088947974759225973957 4294516677745267354870117)
                  ·
                    refine ⟨805221877077237629038147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294516677745267354870117 805221877077237629038147)
                    ·
                      rfl

theorem cell23_4704492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_4704492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704492 prefixEnd_4704492 := by exact prefixLift 4704492
  have htrace : WordTrace (prefixWord ++ tailWord_4704492) baseStart_4704492 baseEnd_4704492 := by
    simpa [prefixWord, tailWord_4704492, baseEnd_4704492] using wordTrace_append hprefix tailTrace_4704492
  have hstable : (prefixWord ++ tailWord_4704492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704492).length < 2 ^ (prefixWord ++ tailWord_4704492).sum := by decide
  have hdescent : baseEnd_4704492 < baseStart_4704492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704502 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4704502 : Nat := 118140960795 + 4704502 * 2 ^ 59
def prefixEnd_4704502 : Nat := 4983230072969 + 3 ^ 40 * 4704502 * 2
def baseEnd_4704502 : Nat := 2415670766038257847989395

theorem tailTrace_4704502 : CollatzResearch.WordTrace tailWord_4704502 prefixEnd_4704502 2415670766038257847989395 := by
  unfold tailWord_4704502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10724205275150012113724735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114391522934933462546397173 10724205275150012113724735)
  ·
    refine ⟨16086307912725018170587103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10724205275150012113724735 16086307912725018170587103)
    ·
      refine ⟨24129461869087527255880655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16086307912725018170587103 24129461869087527255880655)
      ·
        refine ⟨36194192803631290883820983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24129461869087527255880655 36194192803631290883820983)
        ·
          refine ⟨54291289205446936325731475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36194192803631290883820983 54291289205446936325731475)
          ·
            refine ⟨81436933808170404488597213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54291289205446936325731475 81436933808170404488597213)
            ·
              refine ⟨30538850178063901683223955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81436933808170404488597213 30538850178063901683223955)
              ·
                refine ⟨45808275267095852524835933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30538850178063901683223955 45808275267095852524835933)
                ·
                  refine ⟨17178103225160944696813475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45808275267095852524835933 17178103225160944696813475)
                  ·
                    refine ⟨25767154837741417045220213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17178103225160944696813475 25767154837741417045220213)
                    ·
                      refine ⟨2415670766038257847989395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25767154837741417045220213 2415670766038257847989395)
                      ·
                        rfl

theorem cell23_4704502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4704502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704502 prefixEnd_4704502 := by exact prefixLift 4704502
  have htrace : WordTrace (prefixWord ++ tailWord_4704502) baseStart_4704502 baseEnd_4704502 := by
    simpa [prefixWord, tailWord_4704502, baseEnd_4704502] using wordTrace_append hprefix tailTrace_4704502
  have hstable : (prefixWord ++ tailWord_4704502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704502).length < 2 ^ (prefixWord ++ tailWord_4704502).sum := by decide
  have hdescent : baseEnd_4704502 < baseStart_4704502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704512 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4]
def baseStart_4704512 : Nat := 118140960795 + 4704512 * 2 ^ 59
def prefixEnd_4704512 : Nat := 4983230072969 + 3 ^ 40 * 4704512 * 2
def baseEnd_4704512 : Nat := 2415675900844802808864349

theorem tailTrace_4704512 : CollatzResearch.WordTrace tailWord_4704512 prefixEnd_4704512 2415675900844802808864349 := by
  unfold tailWord_4704512
  simp only [CollatzResearch.WordTrace]
  refine ⟨85793824566181982763729895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114391766088242643684973193 85793824566181982763729895)
  ·
    refine ⟨128690736849272974145594843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85793824566181982763729895 128690736849272974145594843)
    ·
      refine ⟨193036105273909461218392265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128690736849272974145594843 193036105273909461218392265)
      ·
        refine ⟨144777078955432095913794199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193036105273909461218392265 144777078955432095913794199)
        ·
          refine ⟨217165618433148143870691299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144777078955432095913794199 217165618433148143870691299)
          ·
            refine ⟨325748427649722215806036949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217165618433148143870691299 325748427649722215806036949)
            ·
              refine ⟨7634728773040364432953991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 325748427649722215806036949 7634728773040364432953991)
              ·
                refine ⟨11452093159560546649430987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7634728773040364432953991 11452093159560546649430987)
                ·
                  refine ⟨17178139739340819974146481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11452093159560546649430987 17178139739340819974146481)
                  ·
                    refine ⟨12883604804505614980609861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17178139739340819974146481 12883604804505614980609861)
                    ·
                      refine ⟨2415675900844802808864349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12883604804505614980609861 2415675900844802808864349)
                      ·
                        rfl

theorem cell23_4704512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_4704512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704512 prefixEnd_4704512 := by exact prefixLift 4704512
  have htrace : WordTrace (prefixWord ++ tailWord_4704512) baseStart_4704512 baseEnd_4704512 := by
    simpa [prefixWord, tailWord_4704512, baseEnd_4704512] using wordTrace_append hprefix tailTrace_4704512
  have hstable : (prefixWord ++ tailWord_4704512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704512).length < 2 ^ (prefixWord ++ tailWord_4704512).sum := by decide
  have hdescent : baseEnd_4704512 < baseStart_4704512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704516 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4704516 : Nat := 118140960795 + 4704516 * 2 ^ 59
def prefixEnd_4704516 : Nat := 4983230072969 + 3 ^ 40 * 4704516 * 2
def baseEnd_4704516 : Nat := 2415677954767420793214331

theorem tailTrace_4704516 : CollatzResearch.WordTrace tailWord_4704516 prefixEnd_4704516 2415677954767420793214331 := by
  unfold tailWord_4704516
  simp only [CollatzResearch.WordTrace]
  refine ⟨85793897512174737105302701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114391863349566316140403601 85793897512174737105302701)
  ·
    refine ⟨32172711567065526414488513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85793897512174737105302701 32172711567065526414488513)
    ·
      refine ⟨24129533675299144810866385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32172711567065526414488513 24129533675299144810866385)
      ·
        refine ⟨18097150256474358608149789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24129533675299144810866385 18097150256474358608149789)
        ·
          refine ⟨6786431346177884478056171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18097150256474358608149789 6786431346177884478056171)
          ·
            refine ⟨10179647019266826717084257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6786431346177884478056171 10179647019266826717084257)
            ·
              refine ⟨7634735264450120037813193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10179647019266826717084257 7634735264450120037813193)
              ·
                refine ⟨5726051448337590028359895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7634735264450120037813193 5726051448337590028359895)
                ·
                  refine ⟨8589077172506385042539843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5726051448337590028359895 8589077172506385042539843)
                  ·
                    refine ⟨12883615758759577563809765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8589077172506385042539843 12883615758759577563809765)
                    ·
                      refine ⟨2415677954767420793214331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12883615758759577563809765 2415677954767420793214331)
                      ·
                        rfl

theorem cell23_4704516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4704516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704516 prefixEnd_4704516 := by exact prefixLift 4704516
  have htrace : WordTrace (prefixWord ++ tailWord_4704516) baseStart_4704516 baseEnd_4704516 := by
    simpa [prefixWord, tailWord_4704516, baseEnd_4704516] using wordTrace_append hprefix tailTrace_4704516
  have hstable : (prefixWord ++ tailWord_4704516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704516).length < 2 ^ (prefixWord ++ tailWord_4704516).sum := by decide
  have hdescent : baseEnd_4704516 < baseStart_4704516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704522 : List Nat := [3, 1, 2, 2, 1, 1, 6, 7]
def baseStart_4704522 : Nat := 118140960795 + 4704522 * 2 ^ 59
def prefixEnd_4704522 : Nat := 4983230072969 + 3 ^ 40 * 4704522 * 2
def baseEnd_4704522 : Nat := 89469667987086954434789

theorem tailTrace_4704522 : CollatzResearch.WordTrace tailWord_4704522 prefixEnd_4704522 89469667987086954434789 := by
  unfold tailWord_4704522
  simp only [CollatzResearch.WordTrace]
  refine ⟨42897003465581934308830955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114392009241551824823549213 42897003465581934308830955)
  ·
    refine ⟨64345505198372901463246433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42897003465581934308830955 64345505198372901463246433)
    ·
      refine ⟨48259128898779676097434825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64345505198372901463246433 48259128898779676097434825)
      ·
        refine ⟨36194346674084757073076119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48259128898779676097434825 36194346674084757073076119)
        ·
          refine ⟨54291520011127135609614179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36194346674084757073076119 54291520011127135609614179)
          ·
            refine ⟨81437280016690703414421269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54291520011127135609614179 81437280016690703414421269)
            ·
              refine ⟨3817372500782376722550997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81437280016690703414421269 3817372500782376722550997)
              ·
                refine ⟨89469667987086954434789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3817372500782376722550997 89469667987086954434789)
                ·
                  rfl

theorem cell23_4704522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_4704522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704522 prefixEnd_4704522 := by exact prefixLift 4704522
  have htrace : WordTrace (prefixWord ++ tailWord_4704522) baseStart_4704522 baseEnd_4704522 := by
    simpa [prefixWord, tailWord_4704522, baseEnd_4704522] using wordTrace_append hprefix tailTrace_4704522
  have hstable : (prefixWord ++ tailWord_4704522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704522).length < 2 ^ (prefixWord ++ tailWord_4704522).sum := by decide
  have hdescent : baseEnd_4704522 < baseStart_4704522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704533 : List Nat := [1, 3, 2, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_4704533 : Nat := 118140960795 + 4704533 * 2 ^ 59
def prefixEnd_4704533 : Nat := 4983230072969 + 3 ^ 40 * 4704533 * 2
def baseEnd_4704533 : Nat := 2415686683938547226701753

theorem tailTrace_4704533 : CollatzResearch.WordTrace tailWord_4704533 prefixEnd_4704533 2415686683938547226701753 := by
  unfold tailWord_4704533
  simp only [CollatzResearch.WordTrace]
  refine ⟨171588415065287886113974253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114392276710191924075982835 171588415065287886113974253)
  ·
    refine ⟨64345655649482957292740345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171588415065287886113974253 64345655649482957292740345)
    ·
      refine ⟨48259241737112217969555259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64345655649482957292740345 48259241737112217969555259)
      ·
        refine ⟨72388862605668326954332889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48259241737112217969555259 72388862605668326954332889)
        ·
          refine ⟨54291646954251245215749667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72388862605668326954332889 54291646954251245215749667)
          ·
            refine ⟨81437470431376867823624501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54291646954251245215749667 81437470431376867823624501)
            ·
              refine ⟨7634762852941581358464797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81437470431376867823624501 7634762852941581358464797)
              ·
                refine ⟨2863036069853093009424299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7634762852941581358464797 2863036069853093009424299)
                ·
                  refine ⟨4294554104779639514136449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863036069853093009424299 4294554104779639514136449)
                  ·
                    refine ⟨3220915578584729635602337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4294554104779639514136449 3220915578584729635602337)
                    ·
                      refine ⟨2415686683938547226701753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220915578584729635602337 2415686683938547226701753)
                      ·
                        rfl

theorem cell23_4704533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_4704533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704533 prefixEnd_4704533 := by exact prefixLift 4704533
  have htrace : WordTrace (prefixWord ++ tailWord_4704533) baseStart_4704533 baseEnd_4704533 := by
    simpa [prefixWord, tailWord_4704533, baseEnd_4704533] using wordTrace_append hprefix tailTrace_4704533
  have hstable : (prefixWord ++ tailWord_4704533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704533).length < 2 ^ (prefixWord ++ tailWord_4704533).sum := by decide
  have hdescent : baseEnd_4704533 < baseStart_4704533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704592 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_4704592 : Nat := 118140960795 + 4704592 * 2 ^ 59
def prefixEnd_4704592 : Nat := 4983230072969 + 3 ^ 40 * 4704592 * 2
def baseEnd_4704592 : Nat := 2415716979297162495863981

theorem tailTrace_4704592 : CollatzResearch.WordTrace tailWord_4704592 prefixEnd_4704592 2415716979297162495863981 := by
  unfold tailWord_4704592
  simp only [CollatzResearch.WordTrace]
  refine ⟨85795283486037069595186015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114393711314716092793581353 85795283486037069595186015)
  ·
    refine ⟨128692925229055604392779023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85795283486037069595186015 128692925229055604392779023)
    ·
      refine ⟨193039387843583406589168535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128692925229055604392779023 193039387843583406589168535)
      ·
        refine ⟨289559081765375109883752803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193039387843583406589168535 289559081765375109883752803)
        ·
          refine ⟨434338622648062664825629205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289559081765375109883752803 434338622648062664825629205)
          ·
            refine ⟨20359622936627937413701369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 434338622648062664825629205 20359622936627937413701369)
            ·
              refine ⟨15269717202470953060276027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20359622936627937413701369 15269717202470953060276027)
              ·
                refine ⟨22904575803706429590414041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15269717202470953060276027 22904575803706429590414041)
                ·
                  refine ⟨17178431852779822192810531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22904575803706429590414041 17178431852779822192810531)
                  ·
                    refine ⟨25767647779169733289215797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17178431852779822192810531 25767647779169733289215797)
                    ·
                      refine ⟨2415716979297162495863981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25767647779169733289215797 2415716979297162495863981)
                      ·
                        rfl

theorem cell23_4704592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_4704592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704592 prefixEnd_4704592 := by exact prefixLift 4704592
  have htrace : WordTrace (prefixWord ++ tailWord_4704592) baseStart_4704592 baseEnd_4704592 := by
    simpa [prefixWord, tailWord_4704592, baseEnd_4704592] using wordTrace_append hprefix tailTrace_4704592
  have hstable : (prefixWord ++ tailWord_4704592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704592).length < 2 ^ (prefixWord ++ tailWord_4704592).sum := by decide
  have hdescent : baseEnd_4704592 < baseStart_4704592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704593 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 1, 3, 2]
def baseStart_4704593 : Nat := 118140960795 + 4704593 * 2 ^ 59
def prefixEnd_4704593 : Nat := 4983230072969 + 3 ^ 40 * 4704593 * 2
def baseEnd_4704593 : Nat := 2415717492777816991951477

theorem tailTrace_4704593 : CollatzResearch.WordTrace tailWord_4704593 prefixEnd_4704593 2415717492777816991951477 := by
  unfold tailWord_4704593
  simp only [CollatzResearch.WordTrace]
  refine ⟨171590603445070516361158433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114393735630047010907438955 171590603445070516361158433)
  ·
    refine ⟨128692952583802887270868825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171590603445070516361158433 128692952583802887270868825)
    ·
      refine ⟨96519714437852165453151619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128692952583802887270868825 96519714437852165453151619)
      ·
        refine ⟨144779571656778248179727429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96519714437852165453151619 144779571656778248179727429)
        ·
          refine ⟨27146169685645921533698893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144779571656778248179727429 27146169685645921533698893)
          ·
            refine ⟨10179813632117220575137085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27146169685645921533698893 10179813632117220575137085)
            ·
              refine ⟨3817430112043957715676407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10179813632117220575137085 3817430112043957715676407)
              ·
                refine ⟨5726145168065936573514611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817430112043957715676407 5726145168065936573514611)
                ·
                  refine ⟨8589217752098904860271917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5726145168065936573514611 8589217752098904860271917)
                  ·
                    refine ⟨3220956657037089322601969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8589217752098904860271917 3220956657037089322601969)
                    ·
                      refine ⟨2415717492777816991951477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3220956657037089322601969 2415717492777816991951477)
                      ·
                        rfl

theorem cell23_4704593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_4704593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704593 prefixEnd_4704593 := by exact prefixLift 4704593
  have htrace : WordTrace (prefixWord ++ tailWord_4704593) baseStart_4704593 baseEnd_4704593 := by
    simpa [prefixWord, tailWord_4704593, baseEnd_4704593] using wordTrace_append hprefix tailTrace_4704593
  have hstable : (prefixWord ++ tailWord_4704593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704593).length < 2 ^ (prefixWord ++ tailWord_4704593).sum := by decide
  have hdescent : baseEnd_4704593 < baseStart_4704593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704595 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 11]
def baseStart_4704595 : Nat := 118140960795 + 4704595 * 2 ^ 59
def prefixEnd_4704595 : Nat := 4983230072969 + 3 ^ 40 * 4704595 * 2
def baseEnd_4704595 : Nat := 268413168859902887125163

theorem tailTrace_4704595 : CollatzResearch.WordTrace tailWord_4704595 prefixEnd_4704595 268413168859902887125163 := by
  unfold tailWord_4704595
  simp only [CollatzResearch.WordTrace]
  refine ⟨171590676391063270702731239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114393784260708847135154159 171590676391063270702731239)
  ·
    refine ⟨257386014586594906054096859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171590676391063270702731239 257386014586594906054096859)
    ·
      refine ⟨386079021879892359081145289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257386014586594906054096859 386079021879892359081145289)
      ·
        refine ⟨289559266409919269310858967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386079021879892359081145289 289559266409919269310858967)
        ·
          refine ⟨434338899614878903966288451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289559266409919269310858967 434338899614878903966288451)
          ·
            refine ⟨651508349422318355949432677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434338899614878903966288451 651508349422318355949432677)
            ·
              refine ⟨122157815516684691740518627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 651508349422318355949432677 122157815516684691740518627)
              ·
                refine ⟨183236723275027037610777941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122157815516684691740518627 183236723275027037610777941)
                ·
                  refine ⟨268413168859902887125163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 183236723275027037610777941 268413168859902887125163)
                  ·
                    rfl

theorem cell23_4704595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 11].length) (baseStart_4704595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704595 prefixEnd_4704595 := by exact prefixLift 4704595
  have htrace : WordTrace (prefixWord ++ tailWord_4704595) baseStart_4704595 baseEnd_4704595 := by
    simpa [prefixWord, tailWord_4704595, baseEnd_4704595] using wordTrace_append hprefix tailTrace_4704595
  have hstable : (prefixWord ++ tailWord_4704595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704595).length < 2 ^ (prefixWord ++ tailWord_4704595).sum := by decide
  have hdescent : baseEnd_4704595 < baseStart_4704595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704602 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_4704602 : Nat := 118140960795 + 4704602 * 2 ^ 59
def prefixEnd_4704602 : Nat := 4983230072969 + 3 ^ 40 * 4704602 * 2
def baseEnd_4704602 : Nat := 2415722114103707456738935

theorem tailTrace_4704602 : CollatzResearch.WordTrace tailWord_4704602 prefixEnd_4704602 2415722114103707456738935 := by
  unfold tailWord_4704602
  simp only [CollatzResearch.WordTrace]
  refine ⟨42897732925509477724559015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114393954468025273932157373 42897732925509477724559015)
  ·
    refine ⟨64346599388264216586838523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42897732925509477724559015 64346599388264216586838523)
    ·
      refine ⟨96519899082396324880257785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64346599388264216586838523 96519899082396324880257785)
      ·
        refine ⟨72389924311797243660193339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96519899082396324880257785 72389924311797243660193339)
        ·
          refine ⟨108584886467695865490290009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72389924311797243660193339 108584886467695865490290009)
          ·
            refine ⟨81438664850771899117717507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108584886467695865490290009 81438664850771899117717507)
            ·
              refine ⟨122157997276157848676576261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81438664850771899117717507 122157997276157848676576261)
              ·
                refine ⟨22904624489279596626858049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122157997276157848676576261 22904624489279596626858049)
                ·
                  refine ⟨17178468366959697470143537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22904624489279596626858049 17178468366959697470143537)
                  ·
                    refine ⟨12883851275219773102607653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17178468366959697470143537 12883851275219773102607653)
                    ·
                      refine ⟨2415722114103707456738935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12883851275219773102607653 2415722114103707456738935)
                      ·
                        rfl

theorem cell23_4704602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_4704602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704602 prefixEnd_4704602 := by exact prefixLift 4704602
  have htrace : WordTrace (prefixWord ++ tailWord_4704602) baseStart_4704602 baseEnd_4704602 := by
    simpa [prefixWord, tailWord_4704602, baseEnd_4704602] using wordTrace_append hprefix tailTrace_4704602
  have hstable : (prefixWord ++ tailWord_4704602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704602).length < 2 ^ (prefixWord ++ tailWord_4704602).sum := by decide
  have hdescent : baseEnd_4704602 < baseStart_4704602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704612 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 7]
def baseStart_4704612 : Nat := 118140960795 + 4704612 * 2 ^ 59
def prefixEnd_4704612 : Nat := 4983230072969 + 3 ^ 40 * 4704612 * 2
def baseEnd_4704612 : Nat := 268414138767805824179321

theorem tailTrace_4704612 : CollatzResearch.WordTrace tailWord_4704612 prefixEnd_4704612 268414138767805824179321 := by
  unfold tailWord_4704612
  simp only [CollatzResearch.WordTrace]
  refine ⟨85795648216000841303050045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114394197621334455070733393 85795648216000841303050045)
  ·
    refine ⟨32173368081000315488643767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85795648216000841303050045 32173368081000315488643767)
    ·
      refine ⟨48260052121500473232965651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32173368081000315488643767 48260052121500473232965651)
      ·
        refine ⟨72390078182250709849448477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48260052121500473232965651 72390078182250709849448477)
        ·
          refine ⟨27146279318344016193543179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72390078182250709849448477 27146279318344016193543179)
          ·
            refine ⟨40719418977516024290314769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27146279318344016193543179 40719418977516024290314769)
            ·
              refine ⟨30539564233137018217736077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40719418977516024290314769 30539564233137018217736077)
              ·
                refine ⟨11452336587426381831651029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30539564233137018217736077 11452336587426381831651029)
                ·
                  refine ⟨268414138767805824179321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11452336587426381831651029 268414138767805824179321)
                  ·
                    rfl

theorem cell23_4704612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_4704612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704612 prefixEnd_4704612 := by exact prefixLift 4704612
  have htrace : WordTrace (prefixWord ++ tailWord_4704612) baseStart_4704612 baseEnd_4704612 := by
    simpa [prefixWord, tailWord_4704612, baseEnd_4704612] using wordTrace_append hprefix tailTrace_4704612
  have hstable : (prefixWord ++ tailWord_4704612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704612).length < 2 ^ (prefixWord ++ tailWord_4704612).sum := by decide
  have hdescent : baseEnd_4704612 < baseStart_4704612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704629 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 7]
def baseStart_4704629 : Nat := 118140960795 + 4704629 * 2 ^ 59
def prefixEnd_4704629 : Nat := 4983230072969 + 3 ^ 40 * 4704629 * 2
def baseEnd_4704629 : Nat := 268415108675708761233479

theorem tailTrace_4704629 : CollatzResearch.WordTrace tailWord_4704629 prefixEnd_4704629 268415108675708761233479 := by
  unfold tailWord_4704629
  simp only [CollatzResearch.WordTrace]
  refine ⟨171591916472940094509468941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114394610981960063006312627 171591916472940094509468941)
  ·
    refine ⟨64346968677352535441050853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171591916472940094509468941 64346968677352535441050853)
    ·
      refine ⟨12065056627003600395197035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64346968677352535441050853 12065056627003600395197035)
      ·
        refine ⟨18097584940505400592795553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12065056627003600395197035 18097584940505400592795553)
        ·
          refine ⟨13573188705379050444596665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18097584940505400592795553 13573188705379050444596665)
          ·
            refine ⟨10179891529034287833447499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13573188705379050444596665 10179891529034287833447499)
            ·
              refine ⟨15269837293551431750171249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10179891529034287833447499 15269837293551431750171249)
              ·
                refine ⟨11452377970163573812628437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15269837293551431750171249 11452377970163573812628437)
                ·
                  refine ⟨268415108675708761233479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11452377970163573812628437 268415108675708761233479)
                  ·
                    rfl

theorem cell23_4704629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_4704629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704629 prefixEnd_4704629 := by exact prefixLift 4704629
  have htrace : WordTrace (prefixWord ++ tailWord_4704629) baseStart_4704629 baseEnd_4704629 := by
    simpa [prefixWord, tailWord_4704629, baseEnd_4704629] using wordTrace_append hprefix tailTrace_4704629
  have hstable : (prefixWord ++ tailWord_4704629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704629).length < 2 ^ (prefixWord ++ tailWord_4704629).sum := by decide
  have hdescent : baseEnd_4704629 < baseStart_4704629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704679 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4704679 : Nat := 118140960795 + 4704679 * 2 ^ 59
def prefixEnd_4704679 : Nat := 4983230072969 + 3 ^ 40 * 4704679 * 2
def baseEnd_4704679 : Nat := 2415761652114103655476081

theorem tailTrace_4704679 : CollatzResearch.WordTrace tailWord_4704679 prefixEnd_4704679 2415761652114103655476081 := by
  unfold tailWord_4704679
  simp only [CollatzResearch.WordTrace]
  refine ⟨171593740122758953048789091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114395826748505968699192727 171593740122758953048789091)
  ·
    refine ⟨257390610184138429573183637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171593740122758953048789091 257390610184138429573183637)
    ·
      refine ⟨12065184852381488886242983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 257390610184138429573183637 12065184852381488886242983)
      ·
        refine ⟨18097777278572233329364475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12065184852381488886242983 18097777278572233329364475)
        ·
          refine ⟨27146665917858349994046713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18097777278572233329364475 27146665917858349994046713)
          ·
            refine ⟨20359999438393762495535035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27146665917858349994046713 20359999438393762495535035)
            ·
              refine ⟨30539999157590643743302553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20359999438393762495535035 30539999157590643743302553)
              ·
                refine ⟨22904999368192982807476915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30539999157590643743302553 22904999368192982807476915)
                ·
                  refine ⟨34357499052289474211215373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22904999368192982807476915 34357499052289474211215373)
                  ·
                    refine ⟨12884062144608552829205765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34357499052289474211215373 12884062144608552829205765)
                    ·
                      refine ⟨2415761652114103655476081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12884062144608552829205765 2415761652114103655476081)
                      ·
                        rfl

theorem cell23_4704679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4704679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704679 prefixEnd_4704679 := by exact prefixLift 4704679
  have htrace : WordTrace (prefixWord ++ tailWord_4704679) baseStart_4704679 baseEnd_4704679 := by
    simpa [prefixWord, tailWord_4704679, baseEnd_4704679] using wordTrace_append hprefix tailTrace_4704679
  have hstable : (prefixWord ++ tailWord_4704679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704679).length < 2 ^ (prefixWord ++ tailWord_4704679).sum := by decide
  have hdescent : baseEnd_4704679 < baseStart_4704679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704774 : List Nat := [6, 2, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4704774 : Nat := 118140960795 + 4704774 * 2 ^ 59
def prefixEnd_4704774 : Nat := 4983230072969 + 3 ^ 40 * 4704774 * 2
def baseEnd_4704774 : Nat := 805270144258760261262715

theorem tailTrace_4704774 : CollatzResearch.WordTrace tailWord_4704774 prefixEnd_4704774 805270144258760261262715 := by
  unfold tailWord_4704774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5362412658044212008546793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114398136704943189515664917 5362412658044212008546793)
  ·
    refine ⟨4021809493533159006410095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5362412658044212008546793 4021809493533159006410095)
    ·
      refine ⟨6032714240299738509615143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4021809493533159006410095 6032714240299738509615143)
      ·
        refine ⟨9049071360449607764422715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6032714240299738509615143 9049071360449607764422715)
        ·
          refine ⟨13573607040674411646634073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9049071360449607764422715 13573607040674411646634073)
          ·
            refine ⟨10180205280505808734975555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13573607040674411646634073 10180205280505808734975555)
            ·
              refine ⟨15270307920758713102463333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10180205280505808734975555 15270307920758713102463333)
              ·
                refine ⟨2863182735142258706711875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15270307920758713102463333 2863182735142258706711875)
                ·
                  refine ⟨4294774102713388060067813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863182735142258706711875 4294774102713388060067813)
                  ·
                    refine ⟨805270144258760261262715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294774102713388060067813 805270144258760261262715)
                    ·
                      rfl

theorem cell23_4704774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4704774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704774 prefixEnd_4704774 := by exact prefixLift 4704774
  have htrace : WordTrace (prefixWord ++ tailWord_4704774) baseStart_4704774 baseEnd_4704774 := by
    simpa [prefixWord, tailWord_4704774, baseEnd_4704774] using wordTrace_append hprefix tailTrace_4704774
  have hstable : (prefixWord ++ tailWord_4704774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704774).length < 2 ^ (prefixWord ++ tailWord_4704774).sum := by decide
  have hdescent : baseEnd_4704774 < baseStart_4704774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704780 : List Nat := [2, 2, 1, 2, 4, 2, 1, 4, 1, 1, 3]
def baseStart_4704780 : Nat := 118140960795 + 4704780 * 2 ^ 59
def prefixEnd_4704780 : Nat := 4983230072969 + 3 ^ 40 * 4704780 * 2
def baseEnd_4704780 : Nat := 2415813513660207760313117

theorem tailTrace_4704780 : CollatzResearch.WordTrace tailWord_4704780 prefixEnd_4704780 2415813513660207760313117 := by
  unfold tailWord_4704780
  simp only [CollatzResearch.WordTrace]
  refine ⟨85798711947696523649107897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114398282596928698198810529 85798711947696523649107897)
  ·
    refine ⟨64349033960772392736830923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85798711947696523649107897 64349033960772392736830923)
    ·
      refine ⟨96523550941158589105246385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64349033960772392736830923 96523550941158589105246385)
      ·
        refine ⟨72392663205868941828934789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96523550941158589105246385 72392663205868941828934789)
        ·
          refine ⟨13573624351100426592925273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72392663205868941828934789 13573624351100426592925273)
          ·
            refine ⟨10180218263325319944693955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13573624351100426592925273 10180218263325319944693955)
            ·
              refine ⟨15270327394987979917040933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10180218263325319944693955 15270327394987979917040933)
              ·
                refine ⟨2863186386560246234445175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15270327394987979917040933 2863186386560246234445175)
                ·
                  refine ⟨4294779579840369351667763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863186386560246234445175 4294779579840369351667763)
                  ·
                    refine ⟨6442169369760554027501645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4294779579840369351667763 6442169369760554027501645)
                    ·
                      refine ⟨2415813513660207760313117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6442169369760554027501645 2415813513660207760313117)
                      ·
                        rfl

theorem cell23_4704780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_4704780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704780 prefixEnd_4704780 := by exact prefixLift 4704780
  have htrace : WordTrace (prefixWord ++ tailWord_4704780) baseStart_4704780 baseEnd_4704780 := by
    simpa [prefixWord, tailWord_4704780, baseEnd_4704780] using wordTrace_append hprefix tailTrace_4704780
  have hstable : (prefixWord ++ tailWord_4704780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704780).length < 2 ^ (prefixWord ++ tailWord_4704780).sum := by decide
  have hdescent : baseEnd_4704780 < baseStart_4704780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704789 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_4704789 : Nat := 118140960795 + 4704789 * 2 ^ 59
def prefixEnd_4704789 : Nat := 4983230072969 + 3 ^ 40 * 4704789 * 2
def baseEnd_4704789 : Nat := 2415818134986098225100575

theorem tailTrace_4704789 : CollatzResearch.WordTrace tailWord_4704789 prefixEnd_4704789 2415818134986098225100575 := by
  unfold tailWord_4704789
  simp only [CollatzResearch.WordTrace]
  refine ⟨171597752152360441835293421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114398501434906961223528947 171597752152360441835293421)
  ·
    refine ⟨64349157057135165688235033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171597752152360441835293421 64349157057135165688235033)
    ·
      refine ⟨48261867792851374266176275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64349157057135165688235033 48261867792851374266176275)
      ·
        refine ⟨72392801689277061399264413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48261867792851374266176275 72392801689277061399264413)
        ·
          refine ⟨27147300633478898024724155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72392801689277061399264413 27147300633478898024724155)
          ·
            refine ⟨40720950950218347037086233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27147300633478898024724155 40720950950218347037086233)
            ·
              refine ⟨30540713212663760277814675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40720950950218347037086233 30540713212663760277814675)
              ·
                refine ⟨45811069818995640416722013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30540713212663760277814675 45811069818995640416722013)
                ·
                  refine ⟨17179151182123365156270755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45811069818995640416722013 17179151182123365156270755)
                  ·
                    refine ⟨25768726773185047734406133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17179151182123365156270755 25768726773185047734406133)
                    ·
                      refine ⟨2415818134986098225100575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25768726773185047734406133 2415818134986098225100575)
                      ·
                        rfl

theorem cell23_4704789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_4704789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704789 prefixEnd_4704789 := by exact prefixLift 4704789
  have htrace : WordTrace (prefixWord ++ tailWord_4704789) baseStart_4704789 baseEnd_4704789 := by
    simpa [prefixWord, tailWord_4704789, baseEnd_4704789] using wordTrace_append hprefix tailTrace_4704789
  have hstable : (prefixWord ++ tailWord_4704789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704789).length < 2 ^ (prefixWord ++ tailWord_4704789).sum := by decide
  have hdescent : baseEnd_4704789 < baseStart_4704789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704796 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_4704796 : Nat := 118140960795 + 4704796 * 2 ^ 59
def prefixEnd_4704796 : Nat := 4983230072969 + 3 ^ 40 * 4704796 * 2
def baseEnd_4704796 : Nat := 805273909783559899237681

theorem tailTrace_4704796 : CollatzResearch.WordTrace tailWord_4704796 prefixEnd_4704796 805273909783559899237681 := by
  unfold tailWord_4704796
  simp only [CollatzResearch.WordTrace]
  refine ⟨85799003731667541015399121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114398671642223388020532161 85799003731667541015399121)
  ·
    refine ⟨64349252798750655761549341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85799003731667541015399121 64349252798750655761549341)
    ·
      refine ⟨24130969799531495910581003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64349252798750655761549341 24130969799531495910581003)
      ·
        refine ⟨36196454699297243865871505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24130969799531495910581003 36196454699297243865871505)
        ·
          refine ⟨27147341024472932899403629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36196454699297243865871505 27147341024472932899403629)
          ·
            refine ⟨10180252884177349837276361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27147341024472932899403629 10180252884177349837276361)
            ·
              refine ⟨7635189663133012377957271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10180252884177349837276361 7635189663133012377957271)
              ·
                refine ⟨11452784494699518566935907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635189663133012377957271 11452784494699518566935907)
                ·
                  refine ⟨17179176742049277850403861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11452784494699518566935907 17179176742049277850403861)
                  ·
                    refine ⟨805273909783559899237681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17179176742049277850403861 805273909783559899237681)
                    ·
                      rfl

theorem cell23_4704796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_4704796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704796 prefixEnd_4704796 := by exact prefixLift 4704796
  have htrace : WordTrace (prefixWord ++ tailWord_4704796) baseStart_4704796 baseEnd_4704796 := by
    simpa [prefixWord, tailWord_4704796, baseEnd_4704796] using wordTrace_append hprefix tailTrace_4704796
  have hstable : (prefixWord ++ tailWord_4704796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704796).length < 2 ^ (prefixWord ++ tailWord_4704796).sum := by decide
  have hdescent : baseEnd_4704796 < baseStart_4704796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704803 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 5, 2, 2]
def baseStart_4704803 : Nat := 118140960795 + 4704803 * 2 ^ 59
def prefixEnd_4704803 : Nat := 4983230072969 + 3 ^ 40 * 4704803 * 2
def baseEnd_4704803 : Nat := 2415825323715261170325511

theorem tailTrace_4704803 : CollatzResearch.WordTrace tailWord_4704803 prefixEnd_4704803 2415825323715261170325511 := by
  unfold tailWord_4704803
  simp only [CollatzResearch.WordTrace]
  refine ⟨171598262774309722226303063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114398841849539814817535375 171598262774309722226303063)
  ·
    refine ⟨257397394161464583339454595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171598262774309722226303063 257397394161464583339454595)
    ·
      refine ⟨386096091242196875009181893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257397394161464583339454595 386096091242196875009181893)
      ·
        refine ⟨72393017107911914064221605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 386096091242196875009181893 72393017107911914064221605)
        ·
          refine ⟨13573690707733483887041551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72393017107911914064221605 13573690707733483887041551)
          ·
            refine ⟨20360536061600225830562327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13573690707733483887041551 20360536061600225830562327)
            ·
              refine ⟨30540804092400338745843491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20360536061600225830562327 30540804092400338745843491)
              ·
                refine ⟨45811206138600508118765237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30540804092400338745843491 45811206138600508118765237)
                ·
                  refine ⟨4294800575493797636134241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45811206138600508118765237 4294800575493797636134241)
                  ·
                    refine ⟨3221100431620348227100681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4294800575493797636134241 3221100431620348227100681)
                    ·
                      refine ⟨2415825323715261170325511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221100431620348227100681 2415825323715261170325511)
                      ·
                        rfl

theorem cell23_4704803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_4704803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704803 prefixEnd_4704803 := by exact prefixLift 4704803
  have htrace : WordTrace (prefixWord ++ tailWord_4704803) baseStart_4704803 baseEnd_4704803 := by
    simpa [prefixWord, tailWord_4704803, baseEnd_4704803] using wordTrace_append hprefix tailTrace_4704803
  have hstable : (prefixWord ++ tailWord_4704803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704803).length < 2 ^ (prefixWord ++ tailWord_4704803).sum := by decide
  have hdescent : baseEnd_4704803 < baseStart_4704803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704830 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_4704830 : Nat := 118140960795 + 4704830 * 2 ^ 59
def prefixEnd_4704830 : Nat := 4983230072969 + 3 ^ 40 * 4704830 * 2
def baseEnd_4704830 : Nat := 805279729230977521562629

theorem tailTrace_4704830 : CollatzResearch.WordTrace tailWord_4704830 prefixEnd_4704830 805279729230977521562629 := by
  unfold tailWord_4704830
  simp only [CollatzResearch.WordTrace]
  refine ⟨21449905943151488229691993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114399498363474603891690629 21449905943151488229691993)
  ·
    refine ⟨16087429457363616172268995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21449905943151488229691993 16087429457363616172268995)
    ·
      refine ⟨24131144186045424258403493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16087429457363616172268995 24131144186045424258403493)
      ·
        refine ⟨4524589534883517048450655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24131144186045424258403493 4524589534883517048450655)
        ·
          refine ⟨6786884302325275572675983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524589534883517048450655 6786884302325275572675983)
          ·
            refine ⟨10180326453487913359013975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6786884302325275572675983 10180326453487913359013975)
            ·
              refine ⟨15270489680231870038520963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10180326453487913359013975 15270489680231870038520963)
              ·
                refine ⟨22905734520347805057781445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15270489680231870038520963 22905734520347805057781445)
                ·
                  refine ⟨4294825222565213448334021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22905734520347805057781445 4294825222565213448334021)
                  ·
                    refine ⟨805279729230977521562629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294825222565213448334021 805279729230977521562629)
                    ·
                      rfl

theorem cell23_4704830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_4704830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704830 prefixEnd_4704830 := by exact prefixLift 4704830
  have htrace : WordTrace (prefixWord ++ tailWord_4704830) baseStart_4704830 baseEnd_4704830 := by
    simpa [prefixWord, tailWord_4704830, baseEnd_4704830] using wordTrace_append hprefix tailTrace_4704830
  have hstable : (prefixWord ++ tailWord_4704830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704830).length < 2 ^ (prefixWord ++ tailWord_4704830).sum := by decide
  have hdescent : baseEnd_4704830 < baseStart_4704830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704853 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4704853 : Nat := 118140960795 + 4704853 * 2 ^ 59
def prefixEnd_4704853 : Nat := 4983230072969 + 3 ^ 40 * 4704853 * 2
def baseEnd_4704853 : Nat := 2415850997747985974700281

theorem tailTrace_4704853 : CollatzResearch.WordTrace tailWord_4704853 prefixEnd_4704853 2415850997747985974700281 := by
  unfold tailWord_4704853
  simp only [CollatzResearch.WordTrace]
  refine ⟨171600086424128580765623213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114400057616085720510415475 171600086424128580765623213)
  ·
    refine ⟨64350032409048217787108705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171600086424128580765623213 64350032409048217787108705)
    ·
      refine ⟨48262524306786163340331529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64350032409048217787108705 48262524306786163340331529)
      ·
        refine ⟨36196893230089622505248647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48262524306786163340331529 36196893230089622505248647)
        ·
          refine ⟨54295339845134433757872971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36196893230089622505248647 54295339845134433757872971)
          ·
            refine ⟨81443009767701650636809457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54295339845134433757872971 81443009767701650636809457)
            ·
              refine ⟨61082257325776237977607093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81443009767701650636809457 61082257325776237977607093)
              ·
                refine ⟨5726461624291522310400665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61082257325776237977607093 5726461624291522310400665)
                ·
                  refine ⟨4294846218218641732800499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5726461624291522310400665 4294846218218641732800499)
                  ·
                    refine ⟨6442269327327962599200749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4294846218218641732800499 6442269327327962599200749)
                    ·
                      refine ⟨2415850997747985974700281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6442269327327962599200749 2415850997747985974700281)
                      ·
                        rfl

theorem cell23_4704853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4704853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704853 prefixEnd_4704853 := by exact prefixLift 4704853
  have htrace : WordTrace (prefixWord ++ tailWord_4704853) baseStart_4704853 baseEnd_4704853 := by
    simpa [prefixWord, tailWord_4704853, baseEnd_4704853] using wordTrace_append hprefix tailTrace_4704853
  have hstable : (prefixWord ++ tailWord_4704853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704853).length < 2 ^ (prefixWord ++ tailWord_4704853).sum := by decide
  have hdescent : baseEnd_4704853 < baseStart_4704853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704860 : List Nat := [2, 2, 4, 1, 4, 1, 2, 7]
def baseStart_4704860 : Nat := 118140960795 + 4704860 * 2 ^ 59
def prefixEnd_4704860 : Nat := 4983230072969 + 3 ^ 40 * 4704860 * 2
def baseEnd_4704860 : Nat := 89476096004169164715287

theorem tailTrace_4704860 : CollatzResearch.WordTrace tailWord_4704860 prefixEnd_4704860 89476096004169164715287 := by
  unfold tailWord_4704860
  simp only [CollatzResearch.WordTrace]
  refine ⟨85800170867551610480564017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114400227823402147307418689 85800170867551610480564017)
  ·
    refine ⟨64350128150663707860423013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85800170867551610480564017 64350128150663707860423013)
    ·
      refine ⟨12065649028249445223829315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64350128150663707860423013 12065649028249445223829315)
      ·
        refine ⟨18098473542374167835743973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12065649028249445223829315 18098473542374167835743973)
        ·
          refine ⟨3393463789195156469201995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18098473542374167835743973 3393463789195156469201995)
          ·
            refine ⟨5090195683792734703802993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393463789195156469201995 5090195683792734703802993)
            ·
              refine ⟨3817646762844551027852245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5090195683792734703802993 3817646762844551027852245)
              ·
                refine ⟨89476096004169164715287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3817646762844551027852245 89476096004169164715287)
                ·
                  rfl

theorem cell23_4704860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 7].length) (baseStart_4704860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704860 prefixEnd_4704860 := by exact prefixLift 4704860
  have htrace : WordTrace (prefixWord ++ tailWord_4704860) baseStart_4704860 baseEnd_4704860 := by
    simpa [prefixWord, tailWord_4704860, baseEnd_4704860] using wordTrace_append hprefix tailTrace_4704860
  have hstable : (prefixWord ++ tailWord_4704860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704860).length < 2 ^ (prefixWord ++ tailWord_4704860).sum := by decide
  have hdescent : baseEnd_4704860 < baseStart_4704860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704879 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_4704879 : Nat := 118140960795 + 4704879 * 2 ^ 59
def prefixEnd_4704879 : Nat := 4983230072969 + 3 ^ 40 * 4704879 * 2
def baseEnd_4704879 : Nat := 2415864348245002872975161

theorem tailTrace_4704879 : CollatzResearch.WordTrace tailWord_4704879 prefixEnd_4704879 2415864348245002872975161 := by
  unfold tailWord_4704879
  simp only [CollatzResearch.WordTrace]
  refine ⟨171601034722034387206069691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114400689814689591470713127 171601034722034387206069691)
  ·
    refine ⟨257401552083051580809104537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171601034722034387206069691 257401552083051580809104537)
    ·
      refine ⟨193051164062288685606828403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257401552083051580809104537 193051164062288685606828403)
      ·
        refine ⟨289576746093433028410242605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193051164062288685606828403 289576746093433028410242605)
        ·
          refine ⟨108591279785037385653840977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289576746093433028410242605 108591279785037385653840977)
          ·
            refine ⟨81443459838778039240380733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108591279785037385653840977 81443459838778039240380733)
            ·
              refine ⟨30541297439541764715142775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81443459838778039240380733 30541297439541764715142775)
              ·
                refine ⟨45811946159312647072714163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30541297439541764715142775 45811946159312647072714163)
                ·
                  refine ⟨68717919238968970609071245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45811946159312647072714163 68717919238968970609071245)
                  ·
                    refine ⟨25769219714613363978401717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68717919238968970609071245 25769219714613363978401717)
                    ·
                      refine ⟨2415864348245002872975161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25769219714613363978401717 2415864348245002872975161)
                      ·
                        rfl

theorem cell23_4704879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_4704879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704879 prefixEnd_4704879 := by exact prefixLift 4704879
  have htrace : WordTrace (prefixWord ++ tailWord_4704879) baseStart_4704879 baseEnd_4704879 := by
    simpa [prefixWord, tailWord_4704879, baseEnd_4704879] using wordTrace_append hprefix tailTrace_4704879
  have hstable : (prefixWord ++ tailWord_4704879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704879).length < 2 ^ (prefixWord ++ tailWord_4704879).sum := by decide
  have hdescent : baseEnd_4704879 < baseStart_4704879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704898 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4704898 : Nat := 118140960795 + 4704898 * 2 ^ 59
def prefixEnd_4704898 : Nat := 4983230072969 + 3 ^ 40 * 4704898 * 2
def baseEnd_4704898 : Nat := 805291368125812766212525

theorem tailTrace_4704898 : CollatzResearch.WordTrace tailWord_4704898 prefixEnd_4704898 805291368125812766212525 := by
  unfold tailWord_4704898
  simp only [CollatzResearch.WordTrace]
  refine ⟨42900431927241388362752837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114401151805977035634007565 42900431927241388362752837)
  ·
    refine ⟨8043830986357760318016157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42900431927241388362752837 8043830986357760318016157)
    ·
      refine ⟨3016436619884160119256059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8043830986357760318016157 3016436619884160119256059)
      ·
        refine ⟨4524654929826240178884089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016436619884160119256059 4524654929826240178884089)
        ·
          refine ⟨3393491197369680134163067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4524654929826240178884089 3393491197369680134163067)
          ·
            refine ⟨5090236796054520201244601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393491197369680134163067 5090236796054520201244601)
            ·
              refine ⟨3817677597040890150933451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5090236796054520201244601 3817677597040890150933451)
              ·
                refine ⟨5726516395561335226400177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817677597040890150933451 5726516395561335226400177)
                ·
                  refine ⟨4294887296671001419800133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5726516395561335226400177 4294887296671001419800133)
                  ·
                    refine ⟨805291368125812766212525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294887296671001419800133 805291368125812766212525)
                    ·
                      rfl

theorem cell23_4704898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4704898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704898 prefixEnd_4704898 := by exact prefixLift 4704898
  have htrace : WordTrace (prefixWord ++ tailWord_4704898) baseStart_4704898 baseEnd_4704898 := by
    simpa [prefixWord, tailWord_4704898, baseEnd_4704898] using wordTrace_append hprefix tailTrace_4704898
  have hstable : (prefixWord ++ tailWord_4704898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704898).length < 2 ^ (prefixWord ++ tailWord_4704898).sum := by decide
  have hdescent : baseEnd_4704898 < baseStart_4704898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704956 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4704956 : Nat := 118140960795 + 4704956 * 2 ^ 59
def prefixEnd_4704956 : Nat := 4983230072969 + 3 ^ 40 * 4704956 * 2
def baseEnd_4704956 : Nat := 2415903886255399071712307

theorem tailTrace_4704956 : CollatzResearch.WordTrace tailWord_4704956 prefixEnd_4704956 2415903886255399071712307 := by
  unfold tailWord_4704956
  simp only [CollatzResearch.WordTrace]
  refine ⟨85801921571377714678311361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114402562095170286237748481 85801921571377714678311361)
  ·
    refine ⟨64351441178533286008733521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85801921571377714678311361 64351441178533286008733521)
    ·
      refine ⟨48263580883899964506550141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64351441178533286008733521 48263580883899964506550141)
      ·
        refine ⟨18098842831462486689956303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48263580883899964506550141 18098842831462486689956303)
        ·
          refine ⟨27148264247193730034934455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18098842831462486689956303 27148264247193730034934455)
          ·
            refine ⟨40722396370790595052401683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27148264247193730034934455 40722396370790595052401683)
            ·
              refine ⟨61083594556185892578602525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40722396370790595052401683 61083594556185892578602525)
              ·
                refine ⟨22906347958569709716975947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61083594556185892578602525 22906347958569709716975947)
                ·
                  refine ⟨34359521937854564575463921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22906347958569709716975947 34359521937854564575463921)
                  ·
                    refine ⟨25769641453390923431597941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34359521937854564575463921 25769641453390923431597941)
                    ·
                      refine ⟨2415903886255399071712307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25769641453390923431597941 2415903886255399071712307)
                      ·
                        rfl

theorem cell23_4704956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4704956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704956 prefixEnd_4704956 := by exact prefixLift 4704956
  have htrace : WordTrace (prefixWord ++ tailWord_4704956) baseStart_4704956 baseEnd_4704956 := by
    simpa [prefixWord, tailWord_4704956, baseEnd_4704956] using wordTrace_append hprefix tailTrace_4704956
  have hstable : (prefixWord ++ tailWord_4704956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704956).length < 2 ^ (prefixWord ++ tailWord_4704956).sum := by decide
  have hdescent : baseEnd_4704956 < baseStart_4704956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704983 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_4704983 : Nat := 118140960795 + 4704983 * 2 ^ 59
def prefixEnd_4704983 : Nat := 4983230072969 + 3 ^ 40 * 4704983 * 2
def baseEnd_4704983 : Nat := 2415917750233070466074683

theorem tailTrace_4704983 : CollatzResearch.WordTrace tailWord_4704983 prefixEnd_4704983 2415917750233070466074683 := by
  unfold tailWord_4704983
  simp only [CollatzResearch.WordTrace]
  refine ⟨171604827913657612967855603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114403218609105075311903735 171604827913657612967855603)
  ·
    refine ⟨257407241870486419451783405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171604827913657612967855603 257407241870486419451783405)
    ·
      refine ⟨96527715701432407294418777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257407241870486419451783405 96527715701432407294418777)
      ·
        refine ⟨72395786776074305470814083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96527715701432407294418777 72395786776074305470814083)
        ·
          refine ⟨108593680164111458206221125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72395786776074305470814083 108593680164111458206221125)
          ·
            refine ⟨20361315030770898413666461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108593680164111458206221125 20361315030770898413666461)
            ·
              refine ⟨7635493136539086905124923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20361315030770898413666461 7635493136539086905124923)
              ·
                refine ⟨11453239704808630357687385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635493136539086905124923 11453239704808630357687385)
                ·
                  refine ⟨8589929778606472768265539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11453239704808630357687385 8589929778606472768265539)
                  ·
                    refine ⟨12884894667909709152398309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8589929778606472768265539 12884894667909709152398309)
                    ·
                      refine ⟨2415917750233070466074683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12884894667909709152398309 2415917750233070466074683)
                      ·
                        rfl

theorem cell23_4704983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_4704983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704983 prefixEnd_4704983 := by exact prefixLift 4704983
  have htrace : WordTrace (prefixWord ++ tailWord_4704983) baseStart_4704983 baseEnd_4704983 := by
    simpa [prefixWord, tailWord_4704983, baseEnd_4704983] using wordTrace_append hprefix tailTrace_4704983
  have hstable : (prefixWord ++ tailWord_4704983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704983).length < 2 ^ (prefixWord ++ tailWord_4704983).sum := by decide
  have hdescent : baseEnd_4704983 < baseStart_4704983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704996 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_4704996 : Nat := 118140960795 + 4704996 * 2 ^ 59
def prefixEnd_4704996 : Nat := 4983230072969 + 3 ^ 40 * 4704996 * 2
def baseEnd_4704996 : Nat := 2415924425481578915212123

theorem tailTrace_4704996 : CollatzResearch.WordTrace tailWord_4704996 prefixEnd_4704996 2415924425481578915212123 := by
  unfold tailWord_4704996
  simp only [CollatzResearch.WordTrace]
  refine ⟨85802651031305258094039421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114403534708407010792052561 85802651031305258094039421)
  ·
    refine ⟨32175994136739471785264783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85802651031305258094039421 32175994136739471785264783)
    ·
      refine ⟨48263991205109207677897175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32175994136739471785264783 48263991205109207677897175)
      ·
        refine ⟨72395986807663811516845763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48263991205109207677897175 72395986807663811516845763)
        ·
          refine ⟨108593980211495717275268645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72395986807663811516845763 108593980211495717275268645)
          ·
            refine ⟨20361371289655446989112871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108593980211495717275268645 20361371289655446989112871)
            ·
              refine ⟨30542056934483170483669307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20361371289655446989112871 30542056934483170483669307)
              ·
                refine ⟨45813085401724755725503961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30542056934483170483669307 45813085401724755725503961)
                ·
                  refine ⟨34359814051293566794127971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45813085401724755725503961 34359814051293566794127971)
                  ·
                    refine ⟨51539721076940350191191957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34359814051293566794127971 51539721076940350191191957)
                    ·
                      refine ⟨2415924425481578915212123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51539721076940350191191957 2415924425481578915212123)
                      ·
                        rfl

theorem cell23_4704996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_4704996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704996 prefixEnd_4704996 := by exact prefixLift 4704996
  have htrace : WordTrace (prefixWord ++ tailWord_4704996) baseStart_4704996 baseEnd_4704996 := by
    simpa [prefixWord, tailWord_4704996, baseEnd_4704996] using wordTrace_append hprefix tailTrace_4704996
  have hstable : (prefixWord ++ tailWord_4704996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704996).length < 2 ^ (prefixWord ++ tailWord_4704996).sum := by decide
  have hdescent : baseEnd_4704996 < baseStart_4704996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705010 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_4705010 : Nat := 118140960795 + 4705010 * 2 ^ 59
def prefixEnd_4705010 : Nat := 4983230072969 + 3 ^ 40 * 4705010 * 2
def baseEnd_4705010 : Nat := 805310538070247286812353

theorem tailTrace_4705010 : CollatzResearch.WordTrace tailWord_4705010 prefixEnd_4705010 805310538070247286812353 := by
  unfold tailWord_4705010
  simp only [CollatzResearch.WordTrace]
  refine ⟨42901453171139949144772121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114403875123039864386058989 42901453171139949144772121)
  ·
    refine ⟨32176089878354961858579091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42901453171139949144772121 32176089878354961858579091)
    ·
      refine ⟨48264134817532442787868637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32176089878354961858579091 48264134817532442787868637)
      ·
        refine ⟨18099050556574666045450739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48264134817532442787868637 18099050556574666045450739)
        ·
          refine ⟨27148575834861999068176109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18099050556574666045450739 27148575834861999068176109)
          ·
            refine ⟨10180715938073249650566041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27148575834861999068176109 10180715938073249650566041)
            ·
              refine ⟨7635536953554937237924531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10180715938073249650566041 7635536953554937237924531)
              ·
                refine ⟨11453305430332405856886797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635536953554937237924531 11453305430332405856886797)
                ·
                  refine ⟨4294989536374652196332549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11453305430332405856886797 4294989536374652196332549)
                  ·
                    refine ⟨805310538070247286812353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294989536374652196332549 805310538070247286812353)
                    ·
                      rfl

theorem cell23_4705010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_4705010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705010 prefixEnd_4705010 := by exact prefixLift 4705010
  have htrace : WordTrace (prefixWord ++ tailWord_4705010) baseStart_4705010 baseEnd_4705010 := by
    simpa [prefixWord, tailWord_4705010, baseEnd_4705010] using wordTrace_append hprefix tailTrace_4705010
  have hstable : (prefixWord ++ tailWord_4705010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705010).length < 2 ^ (prefixWord ++ tailWord_4705010).sum := by decide
  have hdescent : baseEnd_4705010 < baseStart_4705010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705043 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 1, 5, 2]
def baseStart_4705043 : Nat := 118140960795 + 4705043 * 2 ^ 59
def prefixEnd_4705043 : Nat := 4983230072969 + 3 ^ 40 * 4705043 * 2
def baseEnd_4705043 : Nat := 2415948559072340231324407

theorem tailTrace_4705043 : CollatzResearch.WordTrace tailWord_4705043 prefixEnd_4705043 2415948559072340231324407 := by
  unfold tailWord_4705043
  simp only [CollatzResearch.WordTrace]
  refine ⟨171607016293440243215039783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114404677528960162143359855 171607016293440243215039783)
  ·
    refine ⟨257410524440160364822559675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171607016293440243215039783 257410524440160364822559675)
    ·
      refine ⟨386115786660240547233839513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257410524440160364822559675 386115786660240547233839513)
      ·
        refine ⟨289586839995180410425379635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386115786660240547233839513 289586839995180410425379635)
        ·
          refine ⟨434380259992770615638069453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289586839995180410425379635 434380259992770615638069453)
          ·
            refine ⟨162892597497288980864276045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434380259992770615638069453 162892597497288980864276045)
            ·
              refine ⟨61084724061483367824103517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162892597497288980864276045 61084724061483367824103517)
              ·
                refine ⟨22906771523056262934038819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61084724061483367824103517 22906771523056262934038819)
                ·
                  refine ⟨34360157284584394401058229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22906771523056262934038819 34360157284584394401058229)
                  ·
                    refine ⟨3221264745429786975099209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34360157284584394401058229 3221264745429786975099209)
                    ·
                      refine ⟨2415948559072340231324407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221264745429786975099209 2415948559072340231324407)
                      ·
                        rfl

theorem cell23_4705043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5, 2].length) (baseStart_4705043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705043 prefixEnd_4705043 := by exact prefixLift 4705043
  have htrace : WordTrace (prefixWord ++ tailWord_4705043) baseStart_4705043 baseEnd_4705043 := by
    simpa [prefixWord, tailWord_4705043, baseEnd_4705043] using wordTrace_append hprefix tailTrace_4705043
  have hstable : (prefixWord ++ tailWord_4705043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705043).length < 2 ^ (prefixWord ++ tailWord_4705043).sum := by decide
  have hdescent : baseEnd_4705043 < baseStart_4705043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705073 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_4705073 : Nat := 118140960795 + 4705073 * 2 ^ 59
def prefixEnd_4705073 : Nat := 4983230072969 + 3 ^ 40 * 4705073 * 2
def baseEnd_4705073 : Nat := 2415963963491975113949269

theorem tailTrace_4705073 : CollatzResearch.WordTrace tailWord_4705073 prefixEnd_4705073 2415963963491975113949269 := by
  unfold tailWord_4705073
  simp only [CollatzResearch.WordTrace]
  refine ⟨171608110483331558338631873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114405406988887705559087915 171608110483331558338631873)
  ·
    refine ⟨128706082862498668753973905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171608110483331558338631873 128706082862498668753973905)
    ·
      refine ⟨96529562146874001565480429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128706082862498668753973905 96529562146874001565480429)
      ·
        refine ⟨36198585805077750587055161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96529562146874001565480429 36198585805077750587055161)
        ·
          refine ⟨27148939353808312940291371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36198585805077750587055161 27148939353808312940291371)
          ·
            refine ⟨40723409030712469410437057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27148939353808312940291371 40723409030712469410437057)
            ·
              refine ⟨30542556773034352057827793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40723409030712469410437057 30542556773034352057827793)
              ·
                refine ⟨22906917579775764043370845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30542556773034352057827793 22906917579775764043370845)
                ·
                  refine ⟨8590094092415911516264067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22906917579775764043370845 8590094092415911516264067)
                  ·
                    refine ⟨12885141138623867274396101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8590094092415911516264067 12885141138623867274396101)
                    ·
                      refine ⟨2415963963491975113949269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12885141138623867274396101 2415963963491975113949269)
                      ·
                        rfl

theorem cell23_4705073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_4705073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705073 prefixEnd_4705073 := by exact prefixLift 4705073
  have htrace : WordTrace (prefixWord ++ tailWord_4705073) baseStart_4705073 baseEnd_4705073 := by
    simpa [prefixWord, tailWord_4705073, baseEnd_4705073] using wordTrace_append hprefix tailTrace_4705073
  have hstable : (prefixWord ++ tailWord_4705073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705073).length < 2 ^ (prefixWord ++ tailWord_4705073).sum := by decide
  have hdescent : baseEnd_4705073 < baseStart_4705073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705096 : List Nat := [2, 1, 3, 1, 1, 3, 1, 11]
def baseStart_4705096 : Nat := 118140960795 + 4705096 * 2 ^ 59
def prefixEnd_4705096 : Nat := 4983230072969 + 3 ^ 40 * 4705096 * 2
def baseEnd_4705096 : Nat := 89480584205445500887469

theorem tailTrace_4705096 : CollatzResearch.WordTrace tailWord_4705096 prefixEnd_4705096 89480584205445500887469 := by
  unfold tailWord_4705096
  simp only [CollatzResearch.WordTrace]
  refine ⟨85804474681124116633359571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114405966241498822177812761 85804474681124116633359571)
  ·
    refine ⟨128706712021686174950039357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85804474681124116633359571 128706712021686174950039357)
    ·
      refine ⟨48265017008132315606264759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128706712021686174950039357 48265017008132315606264759)
      ·
        refine ⟨72397525512198473409397139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48265017008132315606264759 72397525512198473409397139)
        ·
          refine ⟨108596288268297710114095709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72397525512198473409397139 108596288268297710114095709)
          ·
            refine ⟨40723608100611641292785891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108596288268297710114095709 40723608100611641292785891)
            ·
              refine ⟨61085412150917461939178837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40723608100611641292785891 61085412150917461939178837)
              ·
                refine ⟨89480584205445500887469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 61085412150917461939178837 89480584205445500887469)
                ·
                  rfl

theorem cell23_4705096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 11].length) (baseStart_4705096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705096 prefixEnd_4705096 := by exact prefixLift 4705096
  have htrace : WordTrace (prefixWord ++ tailWord_4705096) baseStart_4705096 baseEnd_4705096 := by
    simpa [prefixWord, tailWord_4705096, baseEnd_4705096] using wordTrace_append hprefix tailTrace_4705096
  have hstable : (prefixWord ++ tailWord_4705096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705096).length < 2 ^ (prefixWord ++ tailWord_4705096).sum := by decide
  have hdescent : baseEnd_4705096 < baseStart_4705096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705173 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_4705173 : Nat := 118140960795 + 4705173 * 2 ^ 59
def prefixEnd_4705173 : Nat := 4983230072969 + 3 ^ 40 * 4705173 * 2
def baseEnd_4705173 : Nat := 805338437185808240899603

theorem tailTrace_4705173 : CollatzResearch.WordTrace tailWord_4705173 prefixEnd_4705173 805338437185808240899603 := by
  unfold tailWord_4705173
  simp only [CollatzResearch.WordTrace]
  refine ⟨171611757782969275417272173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114407838521979516944848115 171611757782969275417272173)
  ·
    refine ⟨64354409168613478281477065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171611757782969275417272173 64354409168613478281477065)
    ·
      refine ⟨48265806876460108711107799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64354409168613478281477065 48265806876460108711107799)
      ·
        refine ⟨72398710314690163066661699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48265806876460108711107799 72398710314690163066661699)
        ·
          refine ⟨108598065472035244599992549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72398710314690163066661699 108598065472035244599992549)
          ·
            refine ⟨20362137276006608362498603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108598065472035244599992549 20362137276006608362498603)
            ·
              refine ⟨30543205914009912543747905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20362137276006608362498603 30543205914009912543747905)
              ·
                refine ⟨22907404435507434407810929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30543205914009912543747905 22907404435507434407810929)
                ·
                  refine ⟨17180553326630575805858197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22907404435507434407810929 17180553326630575805858197)
                  ·
                    refine ⟨805338437185808240899603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17180553326630575805858197 805338437185808240899603)
                    ·
                      rfl

theorem cell23_4705173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_4705173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705173 prefixEnd_4705173 := by exact prefixLift 4705173
  have htrace : WordTrace (prefixWord ++ tailWord_4705173) baseStart_4705173 baseEnd_4705173 := by
    simpa [prefixWord, tailWord_4705173, baseEnd_4705173] using wordTrace_append hprefix tailTrace_4705173
  have hstable : (prefixWord ++ tailWord_4705173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705173).length < 2 ^ (prefixWord ++ tailWord_4705173).sum := by decide
  have hdescent : baseEnd_4705173 < baseStart_4705173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705191 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_4705191 : Nat := 118140960795 + 4705191 * 2 ^ 59
def prefixEnd_4705191 : Nat := 4983230072969 + 3 ^ 40 * 4705191 * 2
def baseEnd_4705191 : Nat := 2416024554209205652273727

theorem tailTrace_4705191 : CollatzResearch.WordTrace tailWord_4705191 prefixEnd_4705191 2416024554209205652273727 := by
  unfold tailWord_4705191
  simp only [CollatzResearch.WordTrace]
  refine ⟨171612414296904064491427427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114408276197936042994284951 171612414296904064491427427)
  ·
    refine ⟨257418621445356096737141141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171612414296904064491427427 257418621445356096737141141)
    ·
      refine ⟨12066497880251067034553491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 257418621445356096737141141 12066497880251067034553491)
      ·
        refine ⟨18099746820376600551830237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12066497880251067034553491 18099746820376600551830237)
        ·
          refine ⟨6787405057641225206936339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18099746820376600551830237 6787405057641225206936339)
          ·
            refine ⟨10181107586461837810404509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6787405057641225206936339 10181107586461837810404509)
            ·
              refine ⟨3817915344923189178901691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10181107586461837810404509 3817915344923189178901691)
              ·
                refine ⟨5726873017384783768352537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817915344923189178901691 5726873017384783768352537)
                ·
                  refine ⟨4295154763038587826264403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5726873017384783768352537 4295154763038587826264403)
                  ·
                    refine ⟨6442732144557881739396605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4295154763038587826264403 6442732144557881739396605)
                    ·
                      refine ⟨2416024554209205652273727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6442732144557881739396605 2416024554209205652273727)
                      ·
                        rfl

theorem cell23_4705191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_4705191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705191 prefixEnd_4705191 := by exact prefixLift 4705191
  have htrace : WordTrace (prefixWord ++ tailWord_4705191) baseStart_4705191 baseEnd_4705191 := by
    simpa [prefixWord, tailWord_4705191, baseEnd_4705191] using wordTrace_append hprefix tailTrace_4705191
  have hstable : (prefixWord ++ tailWord_4705191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705191).length < 2 ^ (prefixWord ++ tailWord_4705191).sum := by decide
  have hdescent : baseEnd_4705191 < baseStart_4705191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705193 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_4705193 : Nat := 118140960795 + 4705193 * 2 ^ 59
def prefixEnd_4705193 : Nat := 4983230072969 + 3 ^ 40 * 4705193 * 2
def baseEnd_4705193 : Nat := 2416025581170514644448717

theorem tailTrace_4705193 : CollatzResearch.WordTrace tailWord_4705193 prefixEnd_4705193 2416025581170514644448717 := by
  unfold tailWord_4705193
  simp only [CollatzResearch.WordTrace]
  refine ⟨171612487242896818833000233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114408324828597879222000155 171612487242896818833000233)
  ·
    refine ⟨128709365432172614124750175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171612487242896818833000233 128709365432172614124750175)
    ·
      refine ⟨193064048148258921187125263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128709365432172614124750175 193064048148258921187125263)
      ·
        refine ⟨289596072222388381780687895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193064048148258921187125263 289596072222388381780687895)
        ·
          refine ⟨434394108333582572671031843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289596072222388381780687895 434394108333582572671031843)
          ·
            refine ⟨651591162500373859006547765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434394108333582572671031843 651591162500373859006547765)
            ·
              refine ⟨61086671484410049281863853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 651591162500373859006547765 61086671484410049281863853)
              ·
                refine ⟨22907501806653768480698945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61086671484410049281863853 22907501806653768480698945)
                ·
                  refine ⟨17180626354990326360524209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22907501806653768480698945 17180626354990326360524209)
                  ·
                    refine ⟨12885469766242744770393157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17180626354990326360524209 12885469766242744770393157)
                    ·
                      refine ⟨2416025581170514644448717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12885469766242744770393157 2416025581170514644448717)
                      ·
                        rfl

theorem cell23_4705193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_4705193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705193 prefixEnd_4705193 := by exact prefixLift 4705193
  have htrace : WordTrace (prefixWord ++ tailWord_4705193) baseStart_4705193 baseEnd_4705193 := by
    simpa [prefixWord, tailWord_4705193, baseEnd_4705193] using wordTrace_append hprefix tailTrace_4705193
  have hstable : (prefixWord ++ tailWord_4705193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705193).length < 2 ^ (prefixWord ++ tailWord_4705193).sum := by decide
  have hdescent : baseEnd_4705193 < baseStart_4705193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705237 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 7]
def baseStart_4705237 : Nat := 118140960795 + 4705237 * 2 ^ 59
def prefixEnd_4705237 : Nat := 4983230072969 + 3 ^ 40 * 4705237 * 2
def baseEnd_4705237 : Nat := 268449797146590274699835

theorem tailTrace_4705237 : CollatzResearch.WordTrace tailWord_4705237 prefixEnd_4705237 268449797146590274699835 := by
  unfold tailWord_4705237
  simp only [CollatzResearch.WordTrace]
  refine ⟨171614092054737414347601965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114409394703158276231734643 171614092054737414347601965)
  ·
    refine ⟨64355284520526530380350737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171614092054737414347601965 64355284520526530380350737)
    ·
      refine ⟨48266463390394897785263053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64355284520526530380350737 48266463390394897785263053)
      ·
        refine ⟨18099923771398086669473645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48266463390394897785263053 18099923771398086669473645)
        ·
          refine ⟨6787471414274282501052617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18099923771398086669473645 6787471414274282501052617)
          ·
            refine ⟨5090603560705711875789463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6787471414274282501052617 5090603560705711875789463)
            ·
              refine ⟨7635905341058567813684195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090603560705711875789463 7635905341058567813684195)
              ·
                refine ⟨11453858011587851720526293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635905341058567813684195 11453858011587851720526293)
                ·
                  refine ⟨268449797146590274699835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11453858011587851720526293 268449797146590274699835)
                  ·
                    rfl

theorem cell23_4705237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_4705237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705237 prefixEnd_4705237 := by exact prefixLift 4705237
  have htrace : WordTrace (prefixWord ++ tailWord_4705237) baseStart_4705237 baseEnd_4705237 := by
    simpa [prefixWord, tailWord_4705237, baseEnd_4705237] using wordTrace_append hprefix tailTrace_4705237
  have hstable : (prefixWord ++ tailWord_4705237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705237).length < 2 ^ (prefixWord ++ tailWord_4705237).sum := by decide
  have hdescent : baseEnd_4705237 < baseStart_4705237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705287 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_4705287 : Nat := 118140960795 + 4705287 * 2 ^ 59
def prefixEnd_4705287 : Nat := 4983230072969 + 3 ^ 40 * 4705287 * 2
def baseEnd_4705287 : Nat := 2416073848352037276673285

theorem tailTrace_4705287 : CollatzResearch.WordTrace tailWord_4705287 prefixEnd_4705287 2416073848352037276673285 := by
  unfold tailWord_4705287
  simp only [CollatzResearch.WordTrace]
  refine ⟨171615915704556272886922115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114410610469704181924614743 171615915704556272886922115)
  ·
    refine ⟨257423873556834409330383173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171615915704556272886922115 257423873556834409330383173)
    ·
      refine ⟨48266976291906451749446845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257423873556834409330383173 48266976291906451749446845)
      ·
        refine ⟨18100116109464919406042567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48266976291906451749446845 18100116109464919406042567)
        ·
          refine ⟨27150174164197379109063851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18100116109464919406042567 27150174164197379109063851)
          ·
            refine ⟨40725261246296068663595777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27150174164197379109063851 40725261246296068663595777)
            ·
              refine ⟨30543945934722051497696833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40725261246296068663595777 30543945934722051497696833)
              ·
                refine ⟨22907959451041538623272625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30543945934722051497696833 22907959451041538623272625)
                ·
                  refine ⟨17180969588281153967454469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22907959451041538623272625 17180969588281153967454469)
                  ·
                    refine ⟨3221431797802716368897713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17180969588281153967454469 3221431797802716368897713)
                    ·
                      refine ⟨2416073848352037276673285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221431797802716368897713 2416073848352037276673285)
                      ·
                        rfl

theorem cell23_4705287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_4705287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705287 prefixEnd_4705287 := by exact prefixLift 4705287
  have htrace : WordTrace (prefixWord ++ tailWord_4705287) baseStart_4705287 baseEnd_4705287 := by
    simpa [prefixWord, tailWord_4705287, baseEnd_4705287] using wordTrace_append hprefix tailTrace_4705287
  have hstable : (prefixWord ++ tailWord_4705287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705287).length < 2 ^ (prefixWord ++ tailWord_4705287).sum := by decide
  have hdescent : baseEnd_4705287 < baseStart_4705287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705347 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 4, 3, 2]
def baseStart_4705347 : Nat := 118140960795 + 4705347 * 2 ^ 59
def prefixEnd_4705347 : Nat := 4983230072969 + 3 ^ 40 * 4705347 * 2
def baseEnd_4705347 : Nat := 2416104657191307041923009

theorem tailTrace_4705347 : CollatzResearch.WordTrace tailWord_4705347 prefixEnd_4705347 2416104657191307041923009 := by
  unfold tailWord_4705347
  simp only [CollatzResearch.WordTrace]
  refine ⟨171618104084338903134106295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114412069389559268756070863 171618104084338903134106295)
  ·
    refine ⟨257427156126508354701159443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171618104084338903134106295 257427156126508354701159443)
    ·
      refine ⟨386140734189762532051739165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257427156126508354701159443 386140734189762532051739165)
      ·
        refine ⟨144802775321160949519402187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386140734189762532051739165 144802775321160949519402187)
        ·
          refine ⟨217204162981741424279103281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144802775321160949519402187 217204162981741424279103281)
          ·
            refine ⟨162903122236306068209327461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217204162981741424279103281 162903122236306068209327461)
            ·
              refine ⟨30544335419307387789248899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162903122236306068209327461 30544335419307387789248899)
              ·
                refine ⟨45816503128961081683873349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30544335419307387789248899 45816503128961081683873349)
                ·
                  refine ⟨8590594336680202815726253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45816503128961081683873349 8590594336680202815726253)
                  ·
                    refine ⟨3221472876255076055897345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8590594336680202815726253 3221472876255076055897345)
                    ·
                      refine ⟨2416104657191307041923009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221472876255076055897345 2416104657191307041923009)
                      ·
                        rfl

theorem cell23_4705347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_4705347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705347 prefixEnd_4705347 := by exact prefixLift 4705347
  have htrace : WordTrace (prefixWord ++ tailWord_4705347) baseStart_4705347 baseEnd_4705347 := by
    simpa [prefixWord, tailWord_4705347, baseEnd_4705347] using wordTrace_append hprefix tailTrace_4705347
  have hstable : (prefixWord ++ tailWord_4705347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705347).length < 2 ^ (prefixWord ++ tailWord_4705347).sum := by decide
  have hdescent : baseEnd_4705347 < baseStart_4705347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705360 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_4705360 : Nat := 118140960795 + 4705360 * 2 ^ 59
def prefixEnd_4705360 : Nat := 4983230072969 + 3 ^ 40 * 4705360 * 2
def baseEnd_4705360 : Nat := 2416111332439815491060449

theorem tailTrace_4705360 : CollatzResearch.WordTrace tailWord_4705360 prefixEnd_4705360 2416111332439815491060449 := by
  unfold tailWord_4705360
  simp only [CollatzResearch.WordTrace]
  refine ⟨85809289116645903177164767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114412385488861204236219689 85809289116645903177164767)
  ·
    refine ⟨128713933674968854765747151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85809289116645903177164767 128713933674968854765747151)
    ·
      refine ⟨193070900512453282148620727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128713933674968854765747151 193070900512453282148620727)
      ·
        refine ⟨289606350768679923222931091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193070900512453282148620727 289606350768679923222931091)
        ·
          refine ⟨434409526153019884834396637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289606350768679923222931091 434409526153019884834396637)
          ·
            refine ⟨162903572307382456812898739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434409526153019884834396637 162903572307382456812898739)
            ·
              refine ⟨244355358461073685219348109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162903572307382456812898739 244355358461073685219348109)
              ·
                refine ⟨91633259422902631957255541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244355358461073685219348109 91633259422902631957255541)
                ·
                  refine ⟨8590618070897121745992707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91633259422902631957255541 8590618070897121745992707)
                  ·
                    refine ⟨12885927106345682618989061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8590618070897121745992707 12885927106345682618989061)
                    ·
                      refine ⟨2416111332439815491060449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12885927106345682618989061 2416111332439815491060449)
                      ·
                        rfl

theorem cell23_4705360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_4705360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705360 prefixEnd_4705360 := by exact prefixLift 4705360
  have htrace : WordTrace (prefixWord ++ tailWord_4705360) baseStart_4705360 baseEnd_4705360 := by
    simpa [prefixWord, tailWord_4705360, baseEnd_4705360] using wordTrace_append hprefix tailTrace_4705360
  have hstable : (prefixWord ++ tailWord_4705360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705360).length < 2 ^ (prefixWord ++ tailWord_4705360).sum := by decide
  have hdescent : baseEnd_4705360 < baseStart_4705360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705370 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_4705370 : Nat := 118140960795 + 4705370 * 2 ^ 59
def prefixEnd_4705370 : Nat := 4983230072969 + 3 ^ 40 * 4705370 * 2
def baseEnd_4705370 : Nat := 805372155748786817311801

theorem tailTrace_4705370 : CollatzResearch.WordTrace tailWord_4705370 prefixEnd_4705370 805372155748786817311801 := by
  unfold tailWord_4705370
  simp only [CollatzResearch.WordTrace]
  refine ⟨42904735740813894515548391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114412628642170385374795709 42904735740813894515548391)
  ·
    refine ⟨64357103611220841773322587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42904735740813894515548391 64357103611220841773322587)
    ·
      refine ⟨96535655416831262659983881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64357103611220841773322587 96535655416831262659983881)
      ·
        refine ⟨72401741562623446994987911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96535655416831262659983881 72401741562623446994987911)
        ·
          refine ⟨108602612343935170492481867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72401741562623446994987911 108602612343935170492481867)
          ·
            refine ⟨162903918515902755738722801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108602612343935170492481867 162903918515902755738722801)
            ·
              refine ⟨122177938886927066804042101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162903918515902755738722801 122177938886927066804042101)
              ·
                refine ⟨11454181770649412512878947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122177938886927066804042101 11454181770649412512878947)
                ·
                  refine ⟨17181272655974118769318421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11454181770649412512878947 17181272655974118769318421)
                  ·
                    refine ⟨805372155748786817311801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17181272655974118769318421 805372155748786817311801)
                    ·
                      rfl

theorem cell23_4705370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_4705370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705370 prefixEnd_4705370 := by exact prefixLift 4705370
  have htrace : WordTrace (prefixWord ++ tailWord_4705370) baseStart_4705370 baseEnd_4705370 := by
    simpa [prefixWord, tailWord_4705370, baseEnd_4705370] using wordTrace_append hprefix tailTrace_4705370
  have hstable : (prefixWord ++ tailWord_4705370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705370).length < 2 ^ (prefixWord ++ tailWord_4705370).sum := by decide
  have hdescent : baseEnd_4705370 < baseStart_4705370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705377 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_4705377 : Nat := 118140960795 + 4705377 * 2 ^ 59
def prefixEnd_4705377 : Nat := 4983230072969 + 3 ^ 40 * 4705377 * 2
def baseEnd_4705377 : Nat := 2416120061610941924547871

theorem tailTrace_4705377 : CollatzResearch.WordTrace tailWord_4705377 prefixEnd_4705377 2416120061610941924547871 := by
  unfold tailWord_4705377
  simp only [CollatzResearch.WordTrace]
  refine ⟨171619198274230218257698385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114412798849486812171798923 171619198274230218257698385)
  ·
    refine ⟨128714398705672663693273789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171619198274230218257698385 128714398705672663693273789)
    ·
      refine ⟨48267899514627248884977671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128714398705672663693273789 48267899514627248884977671)
      ·
        refine ⟨72401849271940873327466507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48267899514627248884977671 72401849271940873327466507)
        ·
          refine ⟨108602773907911309991199761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72401849271940873327466507 108602773907911309991199761)
          ·
            refine ⟨81452080430933482493399821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108602773907911309991199761 81452080430933482493399821)
            ·
              refine ⟨30544530161600055935024933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81452080430933482493399821 30544530161600055935024933)
              ·
                refine ⟨5727099405300010487817175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30544530161600055935024933 5727099405300010487817175)
                ·
                  refine ⟨8590649107950015731725763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727099405300010487817175 8590649107950015731725763)
                  ·
                    refine ⟨12885973661925023597588645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8590649107950015731725763 12885973661925023597588645)
                    ·
                      refine ⟨2416120061610941924547871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12885973661925023597588645 2416120061610941924547871)
                      ·
                        rfl

theorem cell23_4705377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_4705377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705377 prefixEnd_4705377 := by exact prefixLift 4705377
  have htrace : WordTrace (prefixWord ++ tailWord_4705377) baseStart_4705377 baseEnd_4705377 := by
    simpa [prefixWord, tailWord_4705377, baseEnd_4705377] using wordTrace_append hprefix tailTrace_4705377
  have hstable : (prefixWord ++ tailWord_4705377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705377).length < 2 ^ (prefixWord ++ tailWord_4705377).sum := by decide
  have hdescent : baseEnd_4705377 < baseStart_4705377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705380 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_4705380 : Nat := 118140960795 + 4705380 * 2 ^ 59
def prefixEnd_4705380 : Nat := 4983230072969 + 3 ^ 40 * 4705380 * 2
def baseEnd_4705380 : Nat := 2416121602052905412810357

theorem tailTrace_4705380 : CollatzResearch.WordTrace tailWord_4705380 prefixEnd_4705380 2416121602052905412810357 := by
  unfold tailWord_4705380
  simp only [CollatzResearch.WordTrace]
  refine ⟨85809653846609674885028797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114412871795479566513371729 85809653846609674885028797)
  ·
    refine ⟨32178620192478628081885799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85809653846609674885028797 32178620192478628081885799)
    ·
      refine ⟨48267930288717942122828699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32178620192478628081885799 48267930288717942122828699)
      ·
        refine ⟨72401895433076913184243049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48267930288717942122828699 72401895433076913184243049)
        ·
          refine ⟨54301421574807684888182287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72401895433076913184243049 54301421574807684888182287)
          ·
            refine ⟨81452132362211527332273431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54301421574807684888182287 81452132362211527332273431)
            ·
              refine ⟨122178198543317290998410147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81452132362211527332273431 122178198543317290998410147)
              ·
                refine ⟨183267297814975936497615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122178198543317290998410147 183267297814975936497615221)
                ·
                  refine ⟨17181309170153994046651427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183267297814975936497615221 17181309170153994046651427)
                  ·
                    refine ⟨25771963755230991069977141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17181309170153994046651427 25771963755230991069977141)
                    ·
                      refine ⟨2416121602052905412810357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25771963755230991069977141 2416121602052905412810357)
                      ·
                        rfl

theorem cell23_4705380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_4705380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705380 prefixEnd_4705380 := by exact prefixLift 4705380
  have htrace : WordTrace (prefixWord ++ tailWord_4705380) baseStart_4705380 baseEnd_4705380 := by
    simpa [prefixWord, tailWord_4705380, baseEnd_4705380] using wordTrace_append hprefix tailTrace_4705380
  have hstable : (prefixWord ++ tailWord_4705380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705380).length < 2 ^ (prefixWord ++ tailWord_4705380).sum := by decide
  have hdescent : baseEnd_4705380 < baseStart_4705380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705431 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_4705431 : Nat := 118140960795 + 4705431 * 2 ^ 59
def prefixEnd_4705431 : Nat := 4983230072969 + 3 ^ 40 * 4705431 * 2
def baseEnd_4705431 : Nat := 2416147789566284713272623

theorem tailTrace_4705431 : CollatzResearch.WordTrace tailWord_4705431 prefixEnd_4705431 2416147789566284713272623 := by
  unfold tailWord_4705431
  simp only [CollatzResearch.WordTrace]
  refine ⟨171621167816034585480164147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114414111877356390320109431 171621167816034585480164147)
  ·
    refine ⟨257431751724051878220246221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171621167816034585480164147 257431751724051878220246221)
    ·
      refine ⟨96536906896519454332592333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257431751724051878220246221 96536906896519454332592333)
      ·
        refine ⟨36201340086194795374722125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96536906896519454332592333 36201340086194795374722125)
        ·
          refine ⟨13575502532323048265520797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36201340086194795374722125 13575502532323048265520797)
          ·
            refine ⟨5090813449621143099570299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13575502532323048265520797 5090813449621143099570299)
            ·
              refine ⟨7636220174431714649355449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090813449621143099570299 7636220174431714649355449)
              ·
                refine ⟨5727165130823785987016587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7636220174431714649355449 5727165130823785987016587)
                ·
                  refine ⟨8590747696235678980524881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727165130823785987016587 8590747696235678980524881)
                  ·
                    refine ⟨6443060772176759235393661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8590747696235678980524881 6443060772176759235393661)
                    ·
                      refine ⟨2416147789566284713272623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6443060772176759235393661 2416147789566284713272623)
                      ·
                        rfl

theorem cell23_4705431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_4705431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705431 prefixEnd_4705431 := by exact prefixLift 4705431
  have htrace : WordTrace (prefixWord ++ tailWord_4705431) baseStart_4705431 baseEnd_4705431 := by
    simpa [prefixWord, tailWord_4705431, baseEnd_4705431] using wordTrace_append hprefix tailTrace_4705431
  have hstable : (prefixWord ++ tailWord_4705431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705431).length < 2 ^ (prefixWord ++ tailWord_4705431).sum := by decide
  have hdescent : baseEnd_4705431 < baseStart_4705431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705444 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_4705444 : Nat := 118140960795 + 4705444 * 2 ^ 59
def prefixEnd_4705444 : Nat := 4983230072969 + 3 ^ 40 * 4705444 * 2
def baseEnd_4705444 : Nat := 2416154464814793162410063

theorem tailTrace_4705444 : CollatzResearch.WordTrace tailWord_4705444 prefixEnd_4705444 2416154464814793162410063 := by
  unfold tailWord_4705444
  simp only [CollatzResearch.WordTrace]
  refine ⟨85810820982493744350193693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114414427976658325800258257 85810820982493744350193693)
  ·
    refine ⟨32179057868435154131322635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85810820982493744350193693 32179057868435154131322635)
    ·
      refine ⟨48268586802652731196983953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32179057868435154131322635 48268586802652731196983953)
      ·
        refine ⟨36201440101989548397737965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48268586802652731196983953 36201440101989548397737965)
        ·
          refine ⟨13575540038246080649151737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36201440101989548397737965 13575540038246080649151737)
          ·
            refine ⟨10181655028684560486863803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13575540038246080649151737 10181655028684560486863803)
            ·
              refine ⟨15272482543026840730295705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10181655028684560486863803 15272482543026840730295705)
              ·
                refine ⟨11454361907270130547721779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15272482543026840730295705 11454361907270130547721779)
                ·
                  refine ⟨17181542860905195821582669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11454361907270130547721779 17181542860905195821582669)
                  ·
                    refine ⟨6443078572839448433093501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17181542860905195821582669 6443078572839448433093501)
                    ·
                      refine ⟨2416154464814793162410063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6443078572839448433093501 2416154464814793162410063)
                      ·
                        rfl

theorem cell23_4705444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_4705444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705444 prefixEnd_4705444 := by exact prefixLift 4705444
  have htrace : WordTrace (prefixWord ++ tailWord_4705444) baseStart_4705444 baseEnd_4705444 := by
    simpa [prefixWord, tailWord_4705444, baseEnd_4705444] using wordTrace_append hprefix tailTrace_4705444
  have hstable : (prefixWord ++ tailWord_4705444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705444).length < 2 ^ (prefixWord ++ tailWord_4705444).sum := by decide
  have hdescent : baseEnd_4705444 < baseStart_4705444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705518 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_4705518 : Nat := 118140960795 + 4705518 * 2 ^ 59
def prefixEnd_4705518 : Nat := 4983230072969 + 3 ^ 40 * 4705518 * 2
def baseEnd_4705518 : Nat := 2416192462383225872884723

theorem tailTrace_4705518 : CollatzResearch.WordTrace tailWord_4705518 prefixEnd_4705518 2416192462383225872884723 := by
  unfold tailWord_4705518
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453042620839924917322651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114416227311146266225720805 21453042620839924917322651)
  ·
    refine ⟨32179563931259887375983977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21453042620839924917322651 32179563931259887375983977)
    ·
      refine ⟨24134672948444915531987983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32179563931259887375983977 24134672948444915531987983)
      ·
        refine ⟨36202009422667373297981975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24134672948444915531987983 36202009422667373297981975)
        ·
          refine ⟨54303014134001059946972963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36202009422667373297981975 54303014134001059946972963)
          ·
            refine ⟨81454521201001589920459445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54303014134001059946972963 81454521201001589920459445)
            ·
              refine ⟨7636361362593899055043073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81454521201001589920459445 7636361362593899055043073)
              ·
                refine ⟨5727271021945424291282305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7636361362593899055043073 5727271021945424291282305)
                ·
                  refine ⟨4295453266459068218461729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5727271021945424291282305 4295453266459068218461729)
                  ·
                    refine ⟨3221589949844301163846297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4295453266459068218461729 3221589949844301163846297)
                    ·
                      refine ⟨2416192462383225872884723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221589949844301163846297 2416192462383225872884723)
                      ·
                        rfl

theorem cell23_4705518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_4705518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705518 prefixEnd_4705518 := by exact prefixLift 4705518
  have htrace : WordTrace (prefixWord ++ tailWord_4705518) baseStart_4705518 baseEnd_4705518 := by
    simpa [prefixWord, tailWord_4705518, baseEnd_4705518] using wordTrace_append hprefix tailTrace_4705518
  have hstable : (prefixWord ++ tailWord_4705518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705518).length < 2 ^ (prefixWord ++ tailWord_4705518).sum := by decide
  have hdescent : baseEnd_4705518 < baseStart_4705518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705537 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 1, 7]
def baseStart_4705537 : Nat := 118140960795 + 4705537 * 2 ^ 59
def prefixEnd_4705537 : Nat := 4983230072969 + 3 ^ 40 * 4705537 * 2
def baseEnd_4705537 : Nat := 805400739505220432849045

theorem tailTrace_4705537 : CollatzResearch.WordTrace tailWord_4705537 prefixEnd_4705537 805400739505220432849045 := by
  unfold tailWord_4705537
  simp only [CollatzResearch.WordTrace]
  refine ⟨171625033953650565583522865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114416689302433710389015243 171625033953650565583522865)
  ·
    refine ⟨128718775465237924187642149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171625033953650565583522865 128718775465237924187642149)
    ·
      refine ⟨24134770399732110785182903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128718775465237924187642149 24134770399732110785182903)
      ·
        refine ⟨36202155599598166177774355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24134770399732110785182903 36202155599598166177774355)
        ·
          refine ⟨54303233399397249266661533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36202155599598166177774355 54303233399397249266661533)
          ·
            refine ⟨20363712524773968474998075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54303233399397249266661533 20363712524773968474998075)
            ·
              refine ⟨30545568787160952712497113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20363712524773968474998075 30545568787160952712497113)
              ·
                refine ⟨22909176590370714534372835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30545568787160952712497113 22909176590370714534372835)
                ·
                  refine ⟨34363764885556071801559253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22909176590370714534372835 34363764885556071801559253)
                  ·
                    refine ⟨805400739505220432849045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34363764885556071801559253 805400739505220432849045)
                    ·
                      rfl

theorem cell23_4705537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_4705537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705537 prefixEnd_4705537 := by exact prefixLift 4705537
  have htrace : WordTrace (prefixWord ++ tailWord_4705537) baseStart_4705537 baseEnd_4705537 := by
    simpa [prefixWord, tailWord_4705537, baseEnd_4705537] using wordTrace_append hprefix tailTrace_4705537
  have hstable : (prefixWord ++ tailWord_4705537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705537).length < 2 ^ (prefixWord ++ tailWord_4705537).sum := by decide
  have hdescent : baseEnd_4705537 < baseStart_4705537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705581 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4705581 : Nat := 118140960795 + 4705581 * 2 ^ 59
def prefixEnd_4705581 : Nat := 4983230072969 + 3 ^ 40 * 4705581 * 2
def baseEnd_4705581 : Nat := 2416224811664459126396933

theorem tailTrace_4705581 : CollatzResearch.WordTrace tailWord_4705581 prefixEnd_4705581 2416224811664459126396933 := by
  unfold tailWord_4705581
  simp only [CollatzResearch.WordTrace]
  refine ⟨171626638765491161098124597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114417759176994107398749731 171626638765491161098124597)
  ·
    refine ⟨16089997384264796352949181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171626638765491161098124597 16089997384264796352949181)
    ·
      refine ⟨6033749019099298632355943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16089997384264796352949181 6033749019099298632355943)
      ·
        refine ⟨9050623528648947948533915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6033749019099298632355943 9050623528648947948533915)
        ·
          refine ⟨13575935292973421922800873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9050623528648947948533915 13575935292973421922800873)
          ·
            refine ⟨10181951469730066442100655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13575935292973421922800873 10181951469730066442100655)
            ·
              refine ⟨15272927204595099663150983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10181951469730066442100655 15272927204595099663150983)
              ·
                refine ⟨22909390806892649494726475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15272927204595099663150983 22909390806892649494726475)
                ·
                  refine ⟨34364086210338974242089713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22909390806892649494726475 34364086210338974242089713)
                  ·
                    refine ⟨25773064657754230681567285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34364086210338974242089713 25773064657754230681567285)
                    ·
                      refine ⟨2416224811664459126396933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25773064657754230681567285 2416224811664459126396933)
                      ·
                        rfl

theorem cell23_4705581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4705581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705581 prefixEnd_4705581 := by exact prefixLift 4705581
  have htrace : WordTrace (prefixWord ++ tailWord_4705581) baseStart_4705581 baseEnd_4705581 := by
    simpa [prefixWord, tailWord_4705581, baseEnd_4705581] using wordTrace_append hprefix tailTrace_4705581
  have hstable : (prefixWord ++ tailWord_4705581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705581).length < 2 ^ (prefixWord ++ tailWord_4705581).sum := by decide
  have hdescent : baseEnd_4705581 < baseStart_4705581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705594 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_4705594 : Nat := 118140960795 + 4705594 * 2 ^ 59
def prefixEnd_4705594 : Nat := 4983230072969 + 3 ^ 40 * 4705594 * 2
def baseEnd_4705594 : Nat := 2416231486912967575534373

theorem tailTrace_4705594 : CollatzResearch.WordTrace tailWord_4705594 prefixEnd_4705594 2416231486912967575534373 := by
  unfold tailWord_4705594
  simp only [CollatzResearch.WordTrace]
  refine ⟨42906778228611016079586959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114418075276296042878898557 42906778228611016079586959)
  ·
    refine ⟨64360167342916524119380439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42906778228611016079586959 64360167342916524119380439)
    ·
      refine ⟨96540251014374786179070659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64360167342916524119380439 96540251014374786179070659)
      ·
        refine ⟨144810376521562179268605989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96540251014374786179070659 144810376521562179268605989)
        ·
          refine ⟨27151945597792908612863623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144810376521562179268605989 27151945597792908612863623)
          ·
            refine ⟨40727918396689362919295435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27151945597792908612863623 40727918396689362919295435)
            ·
              refine ⟨61091877595034044378943153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40727918396689362919295435 61091877595034044378943153)
              ·
                refine ⟨45818908196275533284207365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61091877595034044378943153 45818908196275533284207365)
                ·
                  refine ⟨8591045286801662490788881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45818908196275533284207365 8591045286801662490788881)
                  ·
                    refine ⟨6443283965101246868091661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8591045286801662490788881 6443283965101246868091661)
                    ·
                      refine ⟨2416231486912967575534373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6443283965101246868091661 2416231486912967575534373)
                      ·
                        rfl

theorem cell23_4705594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_4705594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705594 prefixEnd_4705594 := by exact prefixLift 4705594
  have htrace : WordTrace (prefixWord ++ tailWord_4705594) baseStart_4705594 baseEnd_4705594 := by
    simpa [prefixWord, tailWord_4705594, baseEnd_4705594] using wordTrace_append hprefix tailTrace_4705594
  have hstable : (prefixWord ++ tailWord_4705594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705594).length < 2 ^ (prefixWord ++ tailWord_4705594).sum := by decide
  have hdescent : baseEnd_4705594 < baseStart_4705594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705634 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4705634 : Nat := 118140960795 + 4705634 * 2 ^ 59
def prefixEnd_4705634 : Nat := 4983230072969 + 3 ^ 40 * 4705634 * 2
def baseEnd_4705634 : Nat := 2416252026139147419034189

theorem tailTrace_4705634 : CollatzResearch.WordTrace tailWord_4705634 prefixEnd_4705634 2416252026139147419034189 := by
  unfold tailWord_4705634
  simp only [CollatzResearch.WordTrace]
  refine ⟨42907142958574787787450989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114419047889532767433202637 42907142958574787787450989)
  ·
    refine ⟨16090178609465545420294121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42907142958574787787450989 16090178609465545420294121)
    ·
      refine ⟨12067633957099159065220591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16090178609465545420294121 12067633957099159065220591)
      ·
        refine ⟨18101450935648738597830887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12067633957099159065220591 18101450935648738597830887)
        ·
          refine ⟨27152176403473107896746331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18101450935648738597830887 27152176403473107896746331)
          ·
            refine ⟨40728264605209661845119497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27152176403473107896746331 40728264605209661845119497)
            ·
              refine ⟨30546198453907246383839623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40728264605209661845119497 30546198453907246383839623)
              ·
                refine ⟨45819297680860869575759435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30546198453907246383839623 45819297680860869575759435)
                ·
                  refine ⟨68728946521291304363639153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45819297680860869575759435 68728946521291304363639153)
                  ·
                    refine ⟨51546709890968478272729365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68728946521291304363639153 51546709890968478272729365)
                    ·
                      refine ⟨2416252026139147419034189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51546709890968478272729365 2416252026139147419034189)
                      ·
                        rfl

theorem cell23_4705634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4705634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705634 prefixEnd_4705634 := by exact prefixLift 4705634
  have htrace : WordTrace (prefixWord ++ tailWord_4705634) baseStart_4705634 baseEnd_4705634 := by
    simpa [prefixWord, tailWord_4705634, baseEnd_4705634] using wordTrace_append hprefix tailTrace_4705634
  have hstable : (prefixWord ++ tailWord_4705634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705634).length < 2 ^ (prefixWord ++ tailWord_4705634).sum := by decide
  have hdescent : baseEnd_4705634 < baseStart_4705634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705635 : List Nat := [1, 1, 1, 5, 2, 4, 2, 2, 1, 4]
def baseStart_4705635 : Nat := 118140960795 + 4705635 * 2 ^ 59
def prefixEnd_4705635 : Nat := 4983230072969 + 3 ^ 40 * 4705635 * 2
def baseEnd_4705635 : Nat := 805417513206600638373895

theorem tailTrace_4705635 : CollatzResearch.WordTrace tailWord_4705635 prefixEnd_4705635 805417513206600638373895 := by
  unfold tailWord_4705635
  simp only [CollatzResearch.WordTrace]
  refine ⟨171628608307295528320590359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114419072204863685547060239 171628608307295528320590359)
  ·
    refine ⟨257442912460943292480885539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171628608307295528320590359 257442912460943292480885539)
    ·
      refine ⟨386164368691414938721328309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257442912460943292480885539 386164368691414938721328309)
      ·
        refine ⟨36202909564820150505124529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 386164368691414938721328309 36202909564820150505124529)
        ·
          refine ⟨27152182173615112878843397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36202909564820150505124529 27152182173615112878843397)
          ·
            refine ⟨5091034157552833664783137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27152182173615112878843397 5091034157552833664783137)
            ·
              refine ⟨3818275618164625248587353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091034157552833664783137 3818275618164625248587353)
              ·
                refine ⟨2863706713623468936440515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818275618164625248587353 2863706713623468936440515)
                ·
                  refine ⟨4295560070435203404660773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863706713623468936440515 4295560070435203404660773)
                  ·
                    refine ⟨805417513206600638373895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4295560070435203404660773 805417513206600638373895)
                    ·
                      rfl

theorem cell23_4705635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 4].length) (baseStart_4705635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705635 prefixEnd_4705635 := by exact prefixLift 4705635
  have htrace : WordTrace (prefixWord ++ tailWord_4705635) baseStart_4705635 baseEnd_4705635 := by
    simpa [prefixWord, tailWord_4705635, baseEnd_4705635] using wordTrace_append hprefix tailTrace_4705635
  have hstable : (prefixWord ++ tailWord_4705635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705635).length < 2 ^ (prefixWord ++ tailWord_4705635).sum := by decide
  have hdescent : baseEnd_4705635 < baseStart_4705635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705644 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_4705644 : Nat := 118140960795 + 4705644 * 2 ^ 59
def prefixEnd_4705644 : Nat := 4983230072969 + 3 ^ 40 * 4705644 * 2
def baseEnd_4705644 : Nat := 805419053648564126636381

theorem tailTrace_4705644 : CollatzResearch.WordTrace tailWord_4705644 prefixEnd_4705644 805419053648564126636381 := by
  unfold tailWord_4705644
  simp only [CollatzResearch.WordTrace]
  refine ⟨85814468282131461428833993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114419291042841948571778657 85814468282131461428833993)
  ·
    refine ⟨64360851211598596071625495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85814468282131461428833993 64360851211598596071625495)
    ·
      refine ⟨96541276817397894107438243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64360851211598596071625495 96541276817397894107438243)
      ·
        refine ⟨144811915226096841161157365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96541276817397894107438243 144811915226096841161157365)
        ·
          refine ⟨13576117052446578858858503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144811915226096841161157365 13576117052446578858858503)
          ·
            refine ⟨20364175578669868288287755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13576117052446578858858503 20364175578669868288287755)
            ·
              refine ⟨30546263368004802432431633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20364175578669868288287755 30546263368004802432431633)
              ·
                refine ⟨22909697526003601824323725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30546263368004802432431633 22909697526003601824323725)
                ·
                  refine ⟨8591136572251350684121397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22909697526003601824323725 8591136572251350684121397)
                  ·
                    refine ⟨805419053648564126636381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8591136572251350684121397 805419053648564126636381)
                    ·
                      rfl

theorem cell23_4705644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_4705644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705644 prefixEnd_4705644 := by exact prefixLift 4705644
  have htrace : WordTrace (prefixWord ++ tailWord_4705644) baseStart_4705644 baseEnd_4705644 := by
    simpa [prefixWord, tailWord_4705644, baseEnd_4705644] using wordTrace_append hprefix tailTrace_4705644
  have hstable : (prefixWord ++ tailWord_4705644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705644).length < 2 ^ (prefixWord ++ tailWord_4705644).sum := by decide
  have hdescent : baseEnd_4705644 < baseStart_4705644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705662 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4705662 : Nat := 118140960795 + 4705662 * 2 ^ 59
def prefixEnd_4705662 : Nat := 4983230072969 + 3 ^ 40 * 4705662 * 2
def baseEnd_4705662 : Nat := 2416266403597473309484061

theorem tailTrace_4705662 : CollatzResearch.WordTrace tailWord_4705662 prefixEnd_4705662 2416266403597473309484061 := by
  unfold tailWord_4705662
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453699134774713991477905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114419728718798474621215493 21453699134774713991477905)
  ·
    refine ⟨16090274351081035493608429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21453699134774713991477905 16090274351081035493608429)
    ·
      refine ⟨6033852881655388310103161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16090274351081035493608429 6033852881655388310103161)
      ·
        refine ⟨4525389661241541232577371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6033852881655388310103161 4525389661241541232577371)
        ·
          refine ⟨6788084491862311848866057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525389661241541232577371 6788084491862311848866057)
          ·
            refine ⟨5091063368896733886649543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6788084491862311848866057 5091063368896733886649543)
            ·
              refine ⟨7636595053345100829974315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091063368896733886649543 7636595053345100829974315)
              ·
                refine ⟨11454892580017651244961473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7636595053345100829974315 11454892580017651244961473)
                ·
                  refine ⟨8591169435013238433721105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11454892580017651244961473 8591169435013238433721105)
                  ·
                    refine ⟨6443377076259928825290829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8591169435013238433721105 6443377076259928825290829)
                    ·
                      refine ⟨2416266403597473309484061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6443377076259928825290829 2416266403597473309484061)
                      ·
                        rfl

theorem cell23_4705662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4705662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705662 prefixEnd_4705662 := by exact prefixLift 4705662
  have htrace : WordTrace (prefixWord ++ tailWord_4705662) baseStart_4705662 baseEnd_4705662 := by
    simpa [prefixWord, tailWord_4705662, baseEnd_4705662] using wordTrace_append hprefix tailTrace_4705662
  have hstable : (prefixWord ++ tailWord_4705662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705662).length < 2 ^ (prefixWord ++ tailWord_4705662).sum := by decide
  have hdescent : baseEnd_4705662 < baseStart_4705662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705668 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_4705668 : Nat := 118140960795 + 4705668 * 2 ^ 59
def prefixEnd_4705668 : Nat := 4983230072969 + 3 ^ 40 * 4705668 * 2
def baseEnd_4705668 : Nat := 2416269484481400286009033

theorem tailTrace_4705668 : CollatzResearch.WordTrace tailWord_4705668 prefixEnd_4705668 2416269484481400286009033 := by
  unfold tailWord_4705668
  simp only [CollatzResearch.WordTrace]
  refine ⟨85814905958087987478270829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114419874610783983304361105 85814905958087987478270829)
  ·
    refine ⟨32180589734282995304351561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85814905958087987478270829 32180589734282995304351561)
    ·
      refine ⟨24135442300712246478263671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32180589734282995304351561 24135442300712246478263671)
      ·
        refine ⟨36203163451068369717395507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24135442300712246478263671 36203163451068369717395507)
        ·
          refine ⟨54304745176602554576093261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36203163451068369717395507 54304745176602554576093261)
          ·
            refine ⟨20364279441225957966034973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54304745176602554576093261 20364279441225957966034973)
            ·
              refine ⟨7636604790459734237263115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20364279441225957966034973 7636604790459734237263115)
              ·
                refine ⟨11454907185689601355894673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7636604790459734237263115 11454907185689601355894673)
                ·
                  refine ⟨8591180389267201016921005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11454907185689601355894673 8591180389267201016921005)
                  ·
                    refine ⟨3221692645975200381345377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8591180389267201016921005 3221692645975200381345377)
                    ·
                      refine ⟨2416269484481400286009033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221692645975200381345377 2416269484481400286009033)
                      ·
                        rfl

theorem cell23_4705668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_4705668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705668 prefixEnd_4705668 := by exact prefixLift 4705668
  have htrace : WordTrace (prefixWord ++ tailWord_4705668) baseStart_4705668 baseEnd_4705668 := by
    simpa [prefixWord, tailWord_4705668, baseEnd_4705668] using wordTrace_append hprefix tailTrace_4705668
  have hstable : (prefixWord ++ tailWord_4705668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705668).length < 2 ^ (prefixWord ++ tailWord_4705668).sum := by decide
  have hdescent : baseEnd_4705668 < baseStart_4705668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705678 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_4705678 : Nat := 118140960795 + 4705678 * 2 ^ 59
def prefixEnd_4705678 : Nat := 4983230072969 + 3 ^ 40 * 4705678 * 2
def baseEnd_4705678 : Nat := 805424873095981748961329

theorem tailTrace_4705678 : CollatzResearch.WordTrace tailWord_4705678 prefixEnd_4705678 805424873095981748961329 := by
  unfold tailWord_4705678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453772080767468333050711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114420117764093164442937125 21453772080767468333050711)
  ·
    refine ⟨32180658121151202499576067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21453772080767468333050711 32180658121151202499576067)
    ·
      refine ⟨48270987181726803749364101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32180658121151202499576067 48270987181726803749364101)
      ·
        refine ⟨9050810096573775703005769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48270987181726803749364101 9050810096573775703005769)
        ·
          refine ⟨6788107572430331777254327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9050810096573775703005769 6788107572430331777254327)
          ·
            refine ⟨10182161358645497665881491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6788107572430331777254327 10182161358645497665881491)
            ·
              refine ⟨15273242037968246498822237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10182161358645497665881491 15273242037968246498822237)
              ·
                refine ⟨5727465764238092437058339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15273242037968246498822237 5727465764238092437058339)
                ·
                  refine ⟨8591198646357138655587509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727465764238092437058339 8591198646357138655587509)
                  ·
                    refine ⟨805424873095981748961329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8591198646357138655587509 805424873095981748961329)
                    ·
                      rfl

theorem cell23_4705678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_4705678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705678 prefixEnd_4705678 := by exact prefixLift 4705678
  have htrace : WordTrace (prefixWord ++ tailWord_4705678) baseStart_4705678 baseEnd_4705678 := by
    simpa [prefixWord, tailWord_4705678, baseEnd_4705678] using wordTrace_append hprefix tailTrace_4705678
  have hstable : (prefixWord ++ tailWord_4705678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705678).length < 2 ^ (prefixWord ++ tailWord_4705678).sum := by decide
  have hdescent : baseEnd_4705678 < baseStart_4705678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705707 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8]
def baseStart_4705707 : Nat := 118140960795 + 4705707 * 2 ^ 59
def prefixEnd_4705707 : Nat := 4983230072969 + 3 ^ 40 * 4705707 * 2
def baseEnd_4705707 : Nat := 2416289510226925633421353

theorem tailTrace_4705707 : CollatzResearch.WordTrace tailWord_4705707 prefixEnd_4705707 2416289510226925633421353 := by
  unfold tailWord_4705707
  simp only [CollatzResearch.WordTrace]
  refine ⟨171631234363034684617211375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114420822908689789744807583 171631234363034684617211375)
  ·
    refine ⟨257446851544552026925817063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171631234363034684617211375 257446851544552026925817063)
    ·
      refine ⟨386170277316828040388725595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257446851544552026925817063 386170277316828040388725595)
      ·
        refine ⟨579255415975242060583088393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386170277316828040388725595 579255415975242060583088393)
        ·
          refine ⟨434441561981431545437316295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 579255415975242060583088393 434441561981431545437316295)
          ·
            refine ⟨651662342972147318155974443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434441561981431545437316295 651662342972147318155974443)
            ·
              refine ⟨977493514458220977233961665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651662342972147318155974443 977493514458220977233961665)
              ·
                refine ⟨733120135843665732925471249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977493514458220977233961665 733120135843665732925471249)
                ·
                  refine ⟨549840101882749299694103437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 733120135843665732925471249 549840101882749299694103437)
                  ·
                    refine ⟨206190038206030987385288789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549840101882749299694103437 206190038206030987385288789)
                    ·
                      refine ⟨2416289510226925633421353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 206190038206030987385288789 2416289510226925633421353)
                      ·
                        rfl

theorem cell23_4705707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_4705707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705707 prefixEnd_4705707 := by exact prefixLift 4705707
  have htrace : WordTrace (prefixWord ++ tailWord_4705707) baseStart_4705707 baseEnd_4705707 := by
    simpa [prefixWord, tailWord_4705707, baseEnd_4705707] using wordTrace_append hprefix tailTrace_4705707
  have hstable : (prefixWord ++ tailWord_4705707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705707).length < 2 ^ (prefixWord ++ tailWord_4705707).sum := by decide
  have hdescent : baseEnd_4705707 < baseStart_4705707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705731 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 3]
def baseStart_4705731 : Nat := 118140960795 + 4705731 * 2 ^ 59
def prefixEnd_4705731 : Nat := 4983230072969 + 3 ^ 40 * 4705731 * 2
def baseEnd_4705731 : Nat := 2416301833762633539521243

theorem tailTrace_4705731 : CollatzResearch.WordTrace tailWord_4705731 prefixEnd_4705731 2416301833762633539521243 := by
  unfold tailWord_4705731
  simp only [CollatzResearch.WordTrace]
  refine ⟨171632109714947736716085047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114421406476631824477390031 171632109714947736716085047)
  ·
    refine ⟨257448164572421605074127571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171632109714947736716085047 257448164572421605074127571)
    ·
      refine ⟨386172246858632407611191357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257448164572421605074127571 386172246858632407611191357)
      ·
        refine ⟨144814592571987152854196759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386172246858632407611191357 144814592571987152854196759)
        ·
          refine ⟨217221888857980729281295139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144814592571987152854196759 217221888857980729281295139)
          ·
            refine ⟨325832833286971093921942709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217221888857980729281295139 325832833286971093921942709)
            ·
              refine ⟨30546828120653540055182129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 325832833286971093921942709 30546828120653540055182129)
              ·
                refine ⟨22910121090490155041386597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30546828120653540055182129 22910121090490155041386597)
                ·
                  refine ⟨4295647704466904070259987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22910121090490155041386597 4295647704466904070259987)
                  ·
                    refine ⟨6443471556700356105389981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4295647704466904070259987 6443471556700356105389981)
                    ·
                      refine ⟨2416301833762633539521243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6443471556700356105389981 2416301833762633539521243)
                      ·
                        rfl

theorem cell23_4705731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_4705731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705731 prefixEnd_4705731 := by exact prefixLift 4705731
  have htrace : WordTrace (prefixWord ++ tailWord_4705731) baseStart_4705731 baseEnd_4705731 := by
    simpa [prefixWord, tailWord_4705731, baseEnd_4705731] using wordTrace_append hprefix tailTrace_4705731
  have hstable : (prefixWord ++ tailWord_4705731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705731).length < 2 ^ (prefixWord ++ tailWord_4705731).sum := by decide
  have hdescent : baseEnd_4705731 < baseStart_4705731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705764 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_4705764 : Nat := 118140960795 + 4705764 * 2 ^ 59
def prefixEnd_4705764 : Nat := 4983230072969 + 3 ^ 40 * 4705764 * 2
def baseEnd_4705764 : Nat := 805439592874743970136197

theorem tailTrace_4705764 : CollatzResearch.WordTrace tailWord_4705764 prefixEnd_4705764 805439592874743970136197 := by
  unfold tailWord_4705764
  simp only [CollatzResearch.WordTrace]
  refine ⟨85816656661914091676018173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114422208882552122234690897 85816656661914091676018173)
  ·
    refine ⟨32181246248217784378506815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85816656661914091676018173 32181246248217784378506815)
    ·
      refine ⟨48271869372326676567760223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32181246248217784378506815 48271869372326676567760223)
      ·
        refine ⟨72407804058490014851640335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48271869372326676567760223 72407804058490014851640335)
        ·
          refine ⟨108611706087735022277460503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72407804058490014851640335 108611706087735022277460503)
          ·
            refine ⟨162917559131602533416190755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108611706087735022277460503 162917559131602533416190755)
            ·
              refine ⟨244376338697403800124286133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162917559131602533416190755 244376338697403800124286133)
              ·
                refine ⟨22910281752881606261651825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244376338697403800124286133 22910281752881606261651825)
                ·
                  refine ⟨17182711314661204696238869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22910281752881606261651825 17182711314661204696238869)
                  ·
                    refine ⟨805439592874743970136197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17182711314661204696238869 805439592874743970136197)
                    ·
                      rfl

theorem cell23_4705764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_4705764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705764 prefixEnd_4705764 := by exact prefixLift 4705764
  have htrace : WordTrace (prefixWord ++ tailWord_4705764) baseStart_4705764 baseEnd_4705764 := by
    simpa [prefixWord, tailWord_4705764, baseEnd_4705764] using wordTrace_append hprefix tailTrace_4705764
  have hstable : (prefixWord ++ tailWord_4705764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705764).length < 2 ^ (prefixWord ++ tailWord_4705764).sum := by decide
  have hdescent : baseEnd_4705764 < baseStart_4705764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705765 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4705765 : Nat := 118140960795 + 4705765 * 2 ^ 59
def prefixEnd_4705765 : Nat := 4983230072969 + 3 ^ 40 * 4705765 * 2
def baseEnd_4705765 : Nat := 2416319292104886406496087

theorem tailTrace_4705765 : CollatzResearch.WordTrace tailWord_4705765 prefixEnd_4705765 2416319292104886406496087 := by
  unfold tailWord_4705765
  simp only [CollatzResearch.WordTrace]
  refine ⟨171633349796824560522822749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114422233197883040348548499 171633349796824560522822749)
  ·
    refine ⟨64362506173809210196058531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171633349796824560522822749 64362506173809210196058531)
    ·
      refine ⟨96543759260713815294087797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64362506173809210196058531 96543759260713815294087797)
      ·
        refine ⟨9050977430691920183820731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96543759260713815294087797 9050977430691920183820731)
        ·
          refine ⟨13576466146037880275731097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9050977430691920183820731 13576466146037880275731097)
          ·
            refine ⟨10182349609528410206798323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13576466146037880275731097 10182349609528410206798323)
            ·
              refine ⟨15273524414292615310197485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10182349609528410206798323 15273524414292615310197485)
              ·
                refine ⟨5727571655359730741324057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15273524414292615310197485 5727571655359730741324057)
                ·
                  refine ⟨4295678741519798055993043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5727571655359730741324057 4295678741519798055993043)
                  ·
                    refine ⟨6443518112279697083989565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4295678741519798055993043 6443518112279697083989565)
                    ·
                      refine ⟨2416319292104886406496087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6443518112279697083989565 2416319292104886406496087)
                      ·
                        rfl

theorem cell23_4705765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4705765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705765 prefixEnd_4705765 := by exact prefixLift 4705765
  have htrace : WordTrace (prefixWord ++ tailWord_4705765) baseStart_4705765 baseEnd_4705765 := by
    simpa [prefixWord, tailWord_4705765, baseEnd_4705765] using wordTrace_append hprefix tailTrace_4705765
  have hstable : (prefixWord ++ tailWord_4705765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705765).length < 2 ^ (prefixWord ++ tailWord_4705765).sum := by decide
  have hdescent : baseEnd_4705765 < baseStart_4705765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705788 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_4705788 : Nat := 118140960795 + 4705788 * 2 ^ 59
def prefixEnd_4705788 : Nat := 4983230072969 + 3 ^ 40 * 4705788 * 2
def baseEnd_4705788 : Nat := 2416331102159939816508481

theorem tailTrace_4705788 : CollatzResearch.WordTrace tailWord_4705788 prefixEnd_4705788 2416331102159939816508481 := by
  unfold tailWord_4705788
  simp only [CollatzResearch.WordTrace]
  refine ⟨85817094337870617725455009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114422792450494156967273345 85817094337870617725455009)
  ·
    refine ⟨64362820753402963294091257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85817094337870617725455009 64362820753402963294091257)
    ·
      refine ⟨48272115565052222470568443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64362820753402963294091257 48272115565052222470568443)
      ·
        refine ⟨72408173347578333705852665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48272115565052222470568443 72408173347578333705852665)
        ·
          refine ⟨54306130010683750279389499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72408173347578333705852665 54306130010683750279389499)
          ·
            refine ⟨81459195016025625419084249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54306130010683750279389499 81459195016025625419084249)
            ·
              refine ⟨61094396262019219064313187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81459195016025625419084249 61094396262019219064313187)
              ·
                refine ⟨91641594393028828596469781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61094396262019219064313187 91641594393028828596469781)
                ·
                  refine ⟨4295699737173226340459521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91641594393028828596469781 4295699737173226340459521)
                  ·
                    refine ⟨3221774802879919755344641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4295699737173226340459521 3221774802879919755344641)
                    ·
                      refine ⟨2416331102159939816508481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221774802879919755344641 2416331102159939816508481)
                      ·
                        rfl

theorem cell23_4705788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_4705788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705788 prefixEnd_4705788 := by exact prefixLift 4705788
  have htrace : WordTrace (prefixWord ++ tailWord_4705788) baseStart_4705788 baseEnd_4705788 := by
    simpa [prefixWord, tailWord_4705788, baseEnd_4705788] using wordTrace_append hprefix tailTrace_4705788
  have hstable : (prefixWord ++ tailWord_4705788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705788).length < 2 ^ (prefixWord ++ tailWord_4705788).sum := by decide
  have hdescent : baseEnd_4705788 < baseStart_4705788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705861 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_4705861 : Nat := 118140960795 + 4705861 * 2 ^ 59
def prefixEnd_4705861 : Nat := 4983230072969 + 3 ^ 40 * 4705861 * 2
def baseEnd_4705861 : Nat := 2416368586247718030895645

theorem tailTrace_4705861 : CollatzResearch.WordTrace tailWord_4705861 prefixEnd_4705861 2416368586247718030895645 := by
  unfold tailWord_4705861
  simp only [CollatzResearch.WordTrace]
  refine ⟨171636851204476768918317437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114424567469651179278878291 171636851204476768918317437)
  ·
    refine ⟨64363819201678788344369039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171636851204476768918317437 64363819201678788344369039)
    ·
      refine ⟨96545728802518182516553559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64363819201678788344369039 96545728802518182516553559)
      ·
        refine ⟨144818593203777273774830339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96545728802518182516553559 144818593203777273774830339)
        ·
          refine ⟨217227889805665910662245509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144818593203777273774830339 217227889805665910662245509)
          ·
            refine ⟨40730229338562358249171033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217227889805665910662245509 40730229338562358249171033)
            ·
              refine ⟨30547672003921768686878275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40730229338562358249171033 30547672003921768686878275)
              ·
                refine ⟨45821508005882653030317413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30547672003921768686878275 45821508005882653030317413)
                ·
                  refine ⟨8591532751102997443184515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45821508005882653030317413 8591532751102997443184515)
                  ·
                    refine ⟨12887299126654496164776773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8591532751102997443184515 12887299126654496164776773)
                    ·
                      refine ⟨2416368586247718030895645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12887299126654496164776773 2416368586247718030895645)
                      ·
                        rfl

theorem cell23_4705861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_4705861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705861 prefixEnd_4705861 := by exact prefixLift 4705861
  have htrace : WordTrace (prefixWord ++ tailWord_4705861) baseStart_4705861 baseEnd_4705861 := by
    simpa [prefixWord, tailWord_4705861, baseEnd_4705861] using wordTrace_append hprefix tailTrace_4705861
  have hstable : (prefixWord ++ tailWord_4705861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705861).length < 2 ^ (prefixWord ++ tailWord_4705861).sum := by decide
  have hdescent : baseEnd_4705861 < baseStart_4705861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705898 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_4705898 : Nat := 118140960795 + 4705898 * 2 ^ 59
def prefixEnd_4705898 : Nat := 4983230072969 + 3 ^ 40 * 4705898 * 2
def baseEnd_4705898 : Nat := 2416387585031934386132975

theorem tailTrace_4705898 : CollatzResearch.WordTrace tailWord_4705898 prefixEnd_4705898 2416387585031934386132975 := by
  unfold tailWord_4705898
  simp only [CollatzResearch.WordTrace]
  refine ⟨42909550176335681059353587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114425467136895149491609565 42909550176335681059353587)
  ·
    refine ⟨64364325264503521589030381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42909550176335681059353587 64364325264503521589030381)
    ·
      refine ⟨24136621974188820595886393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64364325264503521589030381 24136621974188820595886393)
      ·
        refine ⟨18102466480641615446914795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24136621974188820595886393 18102466480641615446914795)
        ·
          refine ⟨27153699720962423170372193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18102466480641615446914795 27153699720962423170372193)
          ·
            refine ⟨20365274790721817377779145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27153699720962423170372193 20365274790721817377779145)
            ·
              refine ⟨15273956093041363033334359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20365274790721817377779145 15273956093041363033334359)
              ·
                refine ⟨22910934139562044550001539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15273956093041363033334359 22910934139562044550001539)
                ·
                  refine ⟨34366401209343066825002309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22910934139562044550001539 34366401209343066825002309)
                  ·
                    refine ⟨6443700226751825029687933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34366401209343066825002309 6443700226751825029687933)
                    ·
                      refine ⟨2416387585031934386132975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6443700226751825029687933 2416387585031934386132975)
                      ·
                        rfl

theorem cell23_4705898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_4705898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705898 prefixEnd_4705898 := by exact prefixLift 4705898
  have htrace : WordTrace (prefixWord ++ tailWord_4705898) baseStart_4705898 baseEnd_4705898 := by
    simpa [prefixWord, tailWord_4705898, baseEnd_4705898] using wordTrace_append hprefix tailTrace_4705898
  have hstable : (prefixWord ++ tailWord_4705898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705898).length < 2 ^ (prefixWord ++ tailWord_4705898).sum := by decide
  have hdescent : baseEnd_4705898 < baseStart_4705898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705931 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 3, 5]
def baseStart_4705931 : Nat := 118140960795 + 4705931 * 2 ^ 59
def prefixEnd_4705931 : Nat := 4983230072969 + 3 ^ 40 * 4705931 * 2
def baseEnd_4705931 : Nat := 805468176631177585673441

theorem tailTrace_4705931 : CollatzResearch.WordTrace tailWord_4705931 prefixEnd_4705931 805468176631177585673441 := by
  unfold tailWord_4705931
  simp only [CollatzResearch.WordTrace]
  refine ⟨171639404314223170873365647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114426269542815447248910431 171639404314223170873365647)
  ·
    refine ⟨257459106471334756310048471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171639404314223170873365647 257459106471334756310048471)
    ·
      refine ⟨386188659707002134465072707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257459106471334756310048471 386188659707002134465072707)
      ·
        refine ⟨579282989560503201697609061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386188659707002134465072707 579282989560503201697609061)
        ·
          refine ⟨108615560542594350318301699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 579282989560503201697609061 108615560542594350318301699)
          ·
            refine ⟨162923340813891525477452549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108615560542594350318301699 162923340813891525477452549)
            ·
              refine ⟨30548126402604661027022353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162923340813891525477452549 30548126402604661027022353)
              ·
                refine ⟨22911094801953495770266765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30548126402604661027022353 22911094801953495770266765)
                ·
                  refine ⟨8591660550732560913850037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22911094801953495770266765 8591660550732560913850037)
                  ·
                    refine ⟨805468176631177585673441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8591660550732560913850037 805468176631177585673441)
                    ·
                      rfl

theorem cell23_4705931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 5].length) (baseStart_4705931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705931 prefixEnd_4705931 := by exact prefixLift 4705931
  have htrace : WordTrace (prefixWord ++ tailWord_4705931) baseStart_4705931 baseEnd_4705931 := by
    simpa [prefixWord, tailWord_4705931, baseEnd_4705931] using wordTrace_append hprefix tailTrace_4705931
  have hstable : (prefixWord ++ tailWord_4705931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705931).length < 2 ^ (prefixWord ++ tailWord_4705931).sum := by decide
  have hdescent : baseEnd_4705931 < baseStart_4705931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705955 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 2, 3, 2]
def baseStart_4705955 : Nat := 118140960795 + 4705955 * 2 ^ 59
def prefixEnd_4705955 : Nat := 4983230072969 + 3 ^ 40 * 4705955 * 2
def baseEnd_4705955 : Nat := 2416416853429240663120213

theorem tailTrace_4705955 : CollatzResearch.WordTrace tailWord_4705955 prefixEnd_4705955 2416416853429240663120213 := by
  unfold tailWord_4705955
  simp only [CollatzResearch.WordTrace]
  refine ⟨171640279666136222972239319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114426853110757481981492879 171640279666136222972239319)
  ·
    refine ⟨257460419499204334458358979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171640279666136222972239319 257460419499204334458358979)
    ·
      refine ⟨386190629248806501687538469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257460419499204334458358979 386190629248806501687538469)
      ·
        refine ⟨72410742984151219066413463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 386190629248806501687538469 72410742984151219066413463)
        ·
          refine ⟨108616114476226828599620195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72410742984151219066413463 108616114476226828599620195)
          ·
            refine ⟨162924171714340242899430293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108616114476226828599620195 162924171714340242899430293)
            ·
              refine ⟨7637070549109698885910795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 162924171714340242899430293 7637070549109698885910795)
              ·
                refine ⟨11455605823664548328866193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637070549109698885910795 11455605823664548328866193)
                ·
                  refine ⟨8591704367748411246649645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11455605823664548328866193 8591704367748411246649645)
                  ·
                    refine ⟨3221889137905654217493617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8591704367748411246649645 3221889137905654217493617)
                    ·
                      refine ⟨2416416853429240663120213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221889137905654217493617 2416416853429240663120213)
                      ·
                        rfl

theorem cell23_4705955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_4705955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705955 prefixEnd_4705955 := by exact prefixLift 4705955
  have htrace : WordTrace (prefixWord ++ tailWord_4705955) baseStart_4705955 baseEnd_4705955 := by
    simpa [prefixWord, tailWord_4705955, baseEnd_4705955] using wordTrace_append hprefix tailTrace_4705955
  have hstable : (prefixWord ++ tailWord_4705955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705955).length < 2 ^ (prefixWord ++ tailWord_4705955).sum := by decide
  have hdescent : baseEnd_4705955 < baseStart_4705955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705968 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4]
def baseStart_4705968 : Nat := 118140960795 + 4705968 * 2 ^ 59
def prefixEnd_4705968 : Nat := 4983230072969 + 3 ^ 40 * 4705968 * 2
def baseEnd_4705968 : Nat := 2416423528677749112257653

theorem tailTrace_4705968 : CollatzResearch.WordTrace tailWord_4705968 prefixEnd_4705968 2416423528677749112257653 := by
  unfold tailWord_4705968
  simp only [CollatzResearch.WordTrace]
  refine ⟨85820376907544563096231279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114427169210059417461641705 85820376907544563096231279)
  ·
    refine ⟨128730565361316844644346919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85820376907544563096231279 128730565361316844644346919)
    ·
      refine ⟨193095848041975266966520379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128730565361316844644346919 193095848041975266966520379)
      ·
        refine ⟨289643772062962900449780569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193095848041975266966520379 289643772062962900449780569)
        ·
          refine ⟨217232829047222175337335427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289643772062962900449780569 217232829047222175337335427)
          ·
            refine ⟨325849243570833263006003141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217232829047222175337335427 325849243570833263006003141)
            ·
              refine ⟨61096733169531236813625589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325849243570833263006003141 61096733169531236813625589)
              ·
                refine ⟨5727818734643553451277399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61096733169531236813625589 5727818734643553451277399)
                ·
                  refine ⟨8591728101965330176916099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727818734643553451277399 8591728101965330176916099)
                  ·
                    refine ⟨12887592152947995265374149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8591728101965330176916099 12887592152947995265374149)
                    ·
                      refine ⟨2416423528677749112257653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12887592152947995265374149 2416423528677749112257653)
                      ·
                        rfl

theorem cell23_4705968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_4705968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705968 prefixEnd_4705968 := by exact prefixLift 4705968
  have htrace : WordTrace (prefixWord ++ tailWord_4705968) baseStart_4705968 baseEnd_4705968 := by
    simpa [prefixWord, tailWord_4705968, baseEnd_4705968] using wordTrace_append hprefix tailTrace_4705968
  have hstable : (prefixWord ++ tailWord_4705968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705968).length < 2 ^ (prefixWord ++ tailWord_4705968).sum := by decide
  have hdescent : baseEnd_4705968 < baseStart_4705968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705988 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4705988 : Nat := 118140960795 + 4705988 * 2 ^ 59
def prefixEnd_4705988 : Nat := 4983230072969 + 3 ^ 40 * 4705988 * 2
def baseEnd_4705988 : Nat := 2416433798290839034007561

theorem tailTrace_4705988 : CollatzResearch.WordTrace tailWord_4705988 prefixEnd_4705988 2416433798290839034007561 := by
  unfold tailWord_4705988
  simp only [CollatzResearch.WordTrace]
  refine ⟨85820741637508334804095309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114427655516677779738793745 85820741637508334804095309)
  ·
    refine ⟨32182778114065625551535741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85820741637508334804095309 32182778114065625551535741)
    ·
      refine ⟨12068541792774609581825903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32182778114065625551535741 12068541792774609581825903)
      ·
        refine ⟨18102812689161914372738855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12068541792774609581825903 18102812689161914372738855)
        ·
          refine ⟨27154219033742871559108283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18102812689161914372738855 27154219033742871559108283)
          ·
            refine ⟨40731328550614307338662425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27154219033742871559108283 40731328550614307338662425)
            ·
              refine ⟨30548496412960730503996819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40731328550614307338662425 30548496412960730503996819)
              ·
                refine ⟨45822744619441095755995229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30548496412960730503996819 45822744619441095755995229)
                ·
                  refine ⟨17183529232290410908498211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45822744619441095755995229 17183529232290410908498211)
                  ·
                    refine ⟨25775293848435616362747317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17183529232290410908498211 25775293848435616362747317)
                    ·
                      refine ⟨2416433798290839034007561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25775293848435616362747317 2416433798290839034007561)
                      ·
                        rfl

theorem cell23_4705988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4705988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4705988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4705988 prefixEnd_4705988 := by exact prefixLift 4705988
  have htrace : WordTrace (prefixWord ++ tailWord_4705988) baseStart_4705988 baseEnd_4705988 := by
    simpa [prefixWord, tailWord_4705988, baseEnd_4705988] using wordTrace_append hprefix tailTrace_4705988
  have hstable : (prefixWord ++ tailWord_4705988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705988).length < 2 ^ (prefixWord ++ tailWord_4705988).sum := by decide
  have hdescent : baseEnd_4705988 < baseStart_4705988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706002 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_4706002 : Nat := 118140960795 + 4706002 * 2 ^ 59
def prefixEnd_4706002 : Nat := 4983230072969 + 3 ^ 40 * 4706002 * 2
def baseEnd_4706002 : Nat := 2416440987020001979232497

theorem tailTrace_4706002 : CollatzResearch.WordTrace tailWord_4706002 prefixEnd_4706002 2416440987020001979232497 := by
  unfold tailWord_4706002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42910498474241487499800065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114427995931310633332800173 42910498474241487499800065)
  ·
    refine ⟨32182873855681115624850049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42910498474241487499800065 32182873855681115624850049)
    ·
      refine ⟨24137155391760836718637537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32182873855681115624850049 24137155391760836718637537)
      ·
        refine ⟨18102866543820627538978153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24137155391760836718637537 18102866543820627538978153)
        ·
          refine ⟨13577149907865470654233615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18102866543820627538978153 13577149907865470654233615)
          ·
            refine ⟨20365724861798205981350423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13577149907865470654233615 20365724861798205981350423)
            ·
              refine ⟨30548587292697308972025635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20365724861798205981350423 30548587292697308972025635)
              ·
                refine ⟨45822880939045963458038453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30548587292697308972025635 45822880939045963458038453)
                ·
                  refine ⟨4295895088035559074191105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45822880939045963458038453 4295895088035559074191105)
                  ·
                    refine ⟨3221921316026669305643329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4295895088035559074191105 3221921316026669305643329)
                    ·
                      refine ⟨2416440987020001979232497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221921316026669305643329 2416440987020001979232497)
                      ·
                        rfl

theorem cell23_4706002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_4706002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706002 prefixEnd_4706002 := by exact prefixLift 4706002
  have htrace : WordTrace (prefixWord ++ tailWord_4706002) baseStart_4706002 baseEnd_4706002 := by
    simpa [prefixWord, tailWord_4706002, baseEnd_4706002] using wordTrace_append hprefix tailTrace_4706002
  have hstable : (prefixWord ++ tailWord_4706002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706002).length < 2 ^ (prefixWord ++ tailWord_4706002).sum := by decide
  have hdescent : baseEnd_4706002 < baseStart_4706002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706008 : List Nat := [2, 1, 2, 2, 3, 1, 5, 7]
def baseStart_4706008 : Nat := 118140960795 + 4706008 * 2 ^ 59
def prefixEnd_4706008 : Nat := 4983230072969 + 3 ^ 40 * 4706008 * 2
def baseEnd_4706008 : Nat := 89497928440886257620647

theorem tailTrace_4706008 : CollatzResearch.WordTrace tailWord_4706008 prefixEnd_4706008 89497928440886257620647 := by
  unfold tailWord_4706008
  simp only [CollatzResearch.WordTrace]
  refine ⟨85821106367472106511959339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114428141823296142015945785 85821106367472106511959339)
  ·
    refine ⟨128731659551208159767939009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85821106367472106511959339 128731659551208159767939009)
    ·
      refine ⟨96548744663406119825954257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128731659551208159767939009 96548744663406119825954257)
      ·
        refine ⟨72411558497554589869465693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96548744663406119825954257 72411558497554589869465693)
        ·
          refine ⟨27154334436582971201049635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72411558497554589869465693 27154334436582971201049635)
          ·
            refine ⟨40731501654874456801574453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27154334436582971201049635 40731501654874456801574453)
            ·
              refine ⟨3818578280144480325147605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40731501654874456801574453 3818578280144480325147605)
              ·
                refine ⟨89497928440886257620647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3818578280144480325147605 89497928440886257620647)
                ·
                  rfl

theorem cell23_4706008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 7].length) (baseStart_4706008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706008 prefixEnd_4706008 := by exact prefixLift 4706008
  have htrace : WordTrace (prefixWord ++ tailWord_4706008) baseStart_4706008 baseEnd_4706008 := by
    simpa [prefixWord, tailWord_4706008, baseEnd_4706008] using wordTrace_append hprefix tailTrace_4706008
  have hstable : (prefixWord ++ tailWord_4706008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706008).length < 2 ^ (prefixWord ++ tailWord_4706008).sum := by decide
  have hdescent : baseEnd_4706008 < baseStart_4706008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706019 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4706019 : Nat := 118140960795 + 4706019 * 2 ^ 59
def prefixEnd_4706019 : Nat := 4983230072969 + 3 ^ 40 * 4706019 * 2
def baseEnd_4706019 : Nat := 2416449716191128412719919

theorem tailTrace_4706019 : CollatzResearch.WordTrace tailWord_4706019 prefixEnd_4706019 2416449716191128412719919 := by
  unfold tailWord_4706019
  simp only [CollatzResearch.WordTrace]
  refine ⟨171642613937904361902569111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114428409291936241268379407 171642613937904361902569111)
  ·
    refine ⟨257463920906856542853853667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171642613937904361902569111 257463920906856542853853667)
    ·
      refine ⟨386195881360284814280780501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257463920906856542853853667 386195881360284814280780501)
      ·
        refine ⟨9051465969381675334705793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 386195881360284814280780501 9051465969381675334705793)
        ·
          refine ⟨6788599477036256501029345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9051465969381675334705793 6788599477036256501029345)
          ·
            refine ⟨5091449607777192375772009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6788599477036256501029345 5091449607777192375772009)
            ·
              refine ⟨3818587205832894281829007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091449607777192375772009 3818587205832894281829007)
              ·
                refine ⟨5727880808749341422743511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3818587205832894281829007 5727880808749341422743511)
                ·
                  refine ⟨8591821213124012134115267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727880808749341422743511 8591821213124012134115267)
                  ·
                    refine ⟨12887731819686018201172901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8591821213124012134115267 12887731819686018201172901)
                    ·
                      refine ⟨2416449716191128412719919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12887731819686018201172901 2416449716191128412719919)
                      ·
                        rfl

theorem cell23_4706019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4706019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706019 prefixEnd_4706019 := by exact prefixLift 4706019
  have htrace : WordTrace (prefixWord ++ tailWord_4706019) baseStart_4706019 baseEnd_4706019 := by
    simpa [prefixWord, tailWord_4706019, baseEnd_4706019] using wordTrace_append hprefix tailTrace_4706019
  have hstable : (prefixWord ++ tailWord_4706019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706019).length < 2 ^ (prefixWord ++ tailWord_4706019).sum := by decide
  have hdescent : baseEnd_4706019 < baseStart_4706019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706036 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4706036 : Nat := 118140960795 + 4706036 * 2 ^ 59
def prefixEnd_4706036 : Nat := 4983230072969 + 3 ^ 40 * 4706036 * 2
def baseEnd_4706036 : Nat := 2416458445362254846207341

theorem tailTrace_4706036 : CollatzResearch.WordTrace tailWord_4706036 prefixEnd_4706036 2416458445362254846207341 := by
  unfold tailWord_4706036
  simp only [CollatzResearch.WordTrace]
  refine ⟨85821616989421386902968981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114428822652561849203958641 85821616989421386902968981)
  ·
    refine ⟨4022888296379127511076671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85821616989421386902968981 4022888296379127511076671)
    ·
      refine ⟨6034332444568691266615007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4022888296379127511076671 6034332444568691266615007)
      ·
        refine ⟨9051498666853036899922511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6034332444568691266615007 9051498666853036899922511)
        ·
          refine ⟨13577248000279555349883767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9051498666853036899922511 13577248000279555349883767)
          ·
            refine ⟨20365872000419333024825651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13577248000279555349883767 20365872000419333024825651)
            ·
              refine ⟨30548808000628999537238477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20365872000419333024825651 30548808000628999537238477)
              ·
                refine ⟨11455803000235874826464429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30548808000628999537238477 11455803000235874826464429)
                ·
                  refine ⟨4295926125088453059924161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11455803000235874826464429 4295926125088453059924161)
                  ·
                    refine ⟨3221944593816339794943121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4295926125088453059924161 3221944593816339794943121)
                    ·
                      refine ⟨2416458445362254846207341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221944593816339794943121 2416458445362254846207341)
                      ·
                        rfl

theorem cell23_4706036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4706036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706036 prefixEnd_4706036 := by exact prefixLift 4706036
  have htrace : WordTrace (prefixWord ++ tailWord_4706036) baseStart_4706036 baseEnd_4706036 := by
    simpa [prefixWord, tailWord_4706036, baseEnd_4706036] using wordTrace_append hprefix tailTrace_4706036
  have hstable : (prefixWord ++ tailWord_4706036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706036).length < 2 ^ (prefixWord ++ tailWord_4706036).sum := by decide
  have hdescent : baseEnd_4706036 < baseStart_4706036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706045 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_4706045 : Nat := 118140960795 + 4706045 * 2 ^ 59
def prefixEnd_4706045 : Nat := 4983230072969 + 3 ^ 40 * 4706045 * 2
def baseEnd_4706045 : Nat := 2416463066688145310994799

theorem tailTrace_4706045 : CollatzResearch.WordTrace tailWord_4706045 prefixEnd_4706045 2416463066688145310994799 := by
  unfold tailWord_4706045
  simp only [CollatzResearch.WordTrace]
  refine ⟨171643562235810168343015589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114429041490540112228677059 171643562235810168343015589)
  ·
    refine ⟨32183167919214406564315423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171643562235810168343015589 32183167919214406564315423)
    ·
      refine ⟨48274751878821609846473135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32183167919214406564315423 48274751878821609846473135)
      ·
        refine ⟨72412127818232414769709703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48274751878821609846473135 72412127818232414769709703)
        ·
          refine ⟨108618191727348622154564555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72412127818232414769709703 108618191727348622154564555)
          ·
            refine ⟨162927287591022933231846833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108618191727348622154564555 162927287591022933231846833)
            ·
              refine ⟨122195465693267199923885125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162927287591022933231846833 122195465693267199923885125)
              ·
                refine ⟨22911649817487599985728461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122195465693267199923885125 22911649817487599985728461)
                ·
                  refine ⟨8591868681557849994648173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22911649817487599985728461 8591868681557849994648173)
                  ·
                    refine ⟨3221950755584193747993065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8591868681557849994648173 3221950755584193747993065)
                    ·
                      refine ⟨2416463066688145310994799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221950755584193747993065 2416463066688145310994799)
                      ·
                        rfl

theorem cell23_4706045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_4706045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706045 prefixEnd_4706045 := by exact prefixLift 4706045
  have htrace : WordTrace (prefixWord ++ tailWord_4706045) baseStart_4706045 baseEnd_4706045 := by
    simpa [prefixWord, tailWord_4706045, baseEnd_4706045] using wordTrace_append hprefix tailTrace_4706045
  have hstable : (prefixWord ++ tailWord_4706045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706045).length < 2 ^ (prefixWord ++ tailWord_4706045).sum := by decide
  have hdescent : baseEnd_4706045 < baseStart_4706045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706052 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4706052 : Nat := 118140960795 + 4706052 * 2 ^ 59
def prefixEnd_4706052 : Nat := 4983230072969 + 3 ^ 40 * 4706052 * 2
def baseEnd_4706052 : Nat := 2416466661052726783607267

theorem tailTrace_4706052 : CollatzResearch.WordTrace tailWord_4706052 prefixEnd_4706052 2416466661052726783607267 := by
  unfold tailWord_4706052
  simp only [CollatzResearch.WordTrace]
  refine ⟨85821908773392404269260205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114429211697856539025680273 85821908773392404269260205)
  ·
    refine ⟨32183215790022151600972577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85821908773392404269260205 32183215790022151600972577)
    ·
      refine ⟨24137411842516613700729433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32183215790022151600972577 24137411842516613700729433)
      ·
        refine ⟨18103058881887460275547075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24137411842516613700729433 18103058881887460275547075)
        ·
          refine ⟨27154588322831190413320613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18103058881887460275547075 27154588322831190413320613)
          ·
            refine ⟨5091485310530848202497615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27154588322831190413320613 5091485310530848202497615)
            ·
              refine ⟨7637227965796272303746423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091485310530848202497615 7637227965796272303746423)
              ·
                refine ⟨11455841948694408455619635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637227965796272303746423 11455841948694408455619635)
                ·
                  refine ⟨17183762923041612683429453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11455841948694408455619635 17183762923041612683429453)
                  ·
                    refine ⟨6443911096140604756286045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17183762923041612683429453 6443911096140604756286045)
                    ·
                      refine ⟨2416466661052726783607267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6443911096140604756286045 2416466661052726783607267)
                      ·
                        rfl

theorem cell23_4706052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4706052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706052 prefixEnd_4706052 := by exact prefixLift 4706052
  have htrace : WordTrace (prefixWord ++ tailWord_4706052) baseStart_4706052 baseEnd_4706052 := by
    simpa [prefixWord, tailWord_4706052, baseEnd_4706052] using wordTrace_append hprefix tailTrace_4706052
  have hstable : (prefixWord ++ tailWord_4706052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706052).length < 2 ^ (prefixWord ++ tailWord_4706052).sum := by decide
  have hdescent : baseEnd_4706052 < baseStart_4706052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706062 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_4706062 : Nat := 118140960795 + 4706062 * 2 ^ 59
def prefixEnd_4706062 : Nat := 4983230072969 + 3 ^ 40 * 4706062 * 2
def baseEnd_4706062 : Nat := 2416471795859271744482221

theorem tailTrace_4706062 : CollatzResearch.WordTrace tailWord_4706062 prefixEnd_4706062 2416471795859271744482221 := by
  unfold tailWord_4706062
  simp only [CollatzResearch.WordTrace]
  refine ⟨21455522784593572530798055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114429454851165720164256293 21455522784593572530798055)
  ·
    refine ⟨32183284176890358796197083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21455522784593572530798055 32183284176890358796197083)
    ·
      refine ⟨48274926265335538194295625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32183284176890358796197083 48274926265335538194295625)
      ·
        refine ⟨36206194699001653645721719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48274926265335538194295625 36206194699001653645721719)
        ·
          refine ⟨54309292048502480468582579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36206194699001653645721719 54309292048502480468582579)
          ·
            refine ⟨81463938072753720702873869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54309292048502480468582579 81463938072753720702873869)
            ·
              refine ⟨30548976777282645263577701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81463938072753720702873869 30548976777282645263577701)
              ·
                refine ⟨5727933145740495986920819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30548976777282645263577701 5727933145740495986920819)
                ·
                  refine ⟨8591899718610743980381229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727933145740495986920819 8591899718610743980381229)
                  ·
                    refine ⟨3221962394479028992642961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8591899718610743980381229 3221962394479028992642961)
                    ·
                      refine ⟨2416471795859271744482221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221962394479028992642961 2416471795859271744482221)
                      ·
                        rfl

theorem cell23_4706062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_4706062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706062 prefixEnd_4706062 := by exact prefixLift 4706062
  have htrace : WordTrace (prefixWord ++ tailWord_4706062) baseStart_4706062 baseEnd_4706062 := by
    simpa [prefixWord, tailWord_4706062, baseEnd_4706062] using wordTrace_append hprefix tailTrace_4706062
  have hstable : (prefixWord ++ tailWord_4706062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706062).length < 2 ^ (prefixWord ++ tailWord_4706062).sum := by decide
  have hdescent : baseEnd_4706062 < baseStart_4706062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706092 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 4, 2, 2]
def baseStart_4706092 : Nat := 118140960795 + 4706092 * 2 ^ 59
def prefixEnd_4706092 : Nat := 4983230072969 + 3 ^ 40 * 4706092 * 2
def baseEnd_4706092 : Nat := 2416487200278906627107083

theorem tailTrace_4706092 : CollatzResearch.WordTrace tailWord_4706092 prefixEnd_4706092 2416487200278906627107083 := by
  unfold tailWord_4706092
  simp only [CollatzResearch.WordTrace]
  refine ⟨85822638233319947684988265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114430184311093263579984353 85822638233319947684988265)
  ·
    refine ⟨64366978674989960763741199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85822638233319947684988265 64366978674989960763741199)
    ·
      refine ⟨96550468012484941145611799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64366978674989960763741199 96550468012484941145611799)
      ·
        refine ⟨144825702018727411718417699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96550468012484941145611799 144825702018727411718417699)
        ·
          refine ⟨217238553028091117577626549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144825702018727411718417699 217238553028091117577626549)
          ·
            refine ⟨20366114346383542272902489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217238553028091117577626549 20366114346383542272902489)
            ·
              refine ⟨15274585759787656704676867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20366114346383542272902489 15274585759787656704676867)
              ·
                refine ⟨22911878639681485057015301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15274585759787656704676867 22911878639681485057015301)
                ·
                  refine ⟨4295977244940278448190369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22911878639681485057015301 4295977244940278448190369)
                  ·
                    refine ⟨3221982933705208836142777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4295977244940278448190369 3221982933705208836142777)
                    ·
                      refine ⟨2416487200278906627107083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3221982933705208836142777 2416487200278906627107083)
                      ·
                        rfl

theorem cell23_4706092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_4706092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706092 prefixEnd_4706092 := by exact prefixLift 4706092
  have htrace : WordTrace (prefixWord ++ tailWord_4706092) baseStart_4706092 baseEnd_4706092 := by
    simpa [prefixWord, tailWord_4706092, baseEnd_4706092] using wordTrace_append hprefix tailTrace_4706092
  have hstable : (prefixWord ++ tailWord_4706092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706092).length < 2 ^ (prefixWord ++ tailWord_4706092).sum := by decide
  have hdescent : baseEnd_4706092 < baseStart_4706092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706138 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_4706138 : Nat := 118140960795 + 4706138 * 2 ^ 59
def prefixEnd_4706138 : Nat := 4983230072969 + 3 ^ 40 * 4706138 * 2
def baseEnd_4706138 : Nat := 2416510820389013447131871

theorem tailTrace_4706138 : CollatzResearch.WordTrace tailWord_4706138 prefixEnd_4706138 2416510820389013447131871 := by
  unfold tailWord_4706138
  simp only [CollatzResearch.WordTrace]
  refine ⟨42911738556118311306537767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114431302816315496817434045 42911738556118311306537767)
  ·
    refine ⟨64367607834177466959806651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42911738556118311306537767 64367607834177466959806651)
    ·
      refine ⟨96551411751266200439709977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64367607834177466959806651 96551411751266200439709977)
      ·
        refine ⟨72413558813449650329782483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96551411751266200439709977 72413558813449650329782483)
        ·
          refine ⟨108620338220174475494673725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72413558813449650329782483 108620338220174475494673725)
          ·
            refine ⟨40732626832565428310502647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108620338220174475494673725 40732626832565428310502647)
            ·
              refine ⟨61098940248848142465753971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40732626832565428310502647 61098940248848142465753971)
              ·
                refine ⟨91648410373272213698630957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61098940248848142465753971 91648410373272213698630957)
                ·
                  refine ⟨34368153889977080136986609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91648410373272213698630957 34368153889977080136986609)
                  ·
                    refine ⟨25776115417482810102739957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34368153889977080136986609 25776115417482810102739957)
                    ·
                      refine ⟨2416510820389013447131871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25776115417482810102739957 2416510820389013447131871)
                      ·
                        rfl

theorem cell23_4706138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_4706138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706138 prefixEnd_4706138 := by exact prefixLift 4706138
  have htrace : WordTrace (prefixWord ++ tailWord_4706138) baseStart_4706138 baseEnd_4706138 := by
    simpa [prefixWord, tailWord_4706138, baseEnd_4706138] using wordTrace_append hprefix tailTrace_4706138
  have hstable : (prefixWord ++ tailWord_4706138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706138).length < 2 ^ (prefixWord ++ tailWord_4706138).sum := by decide
  have hdescent : baseEnd_4706138 < baseStart_4706138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706165 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4706165 : Nat := 118140960795 + 4706165 * 2 ^ 59
def prefixEnd_4706165 : Nat := 4983230072969 + 3 ^ 40 * 4706165 * 2
def baseEnd_4706165 : Nat := 2416524684366684841494247

theorem tailTrace_4706165 : CollatzResearch.WordTrace tailWord_4706165 prefixEnd_4706165 2416524684366684841494247 := by
  unfold tailWord_4706165
  simp only [CollatzResearch.WordTrace]
  refine ⟨171647938995375428837383949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114431959330250285891589299 171647938995375428837383949)
  ·
    refine ⟨64367977123265785814018981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171647938995375428837383949 64367977123265785814018981)
    ·
      refine ⟨12068995710612334840128559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64367977123265785814018981 12068995710612334840128559)
      ·
        refine ⟨18103493565918502260192839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12068995710612334840128559 18103493565918502260192839)
        ·
          refine ⟨27155240348877753390289259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18103493565918502260192839 27155240348877753390289259)
          ·
            refine ⟨40732860523316630085433889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27155240348877753390289259 40732860523316630085433889)
            ·
              refine ⟨30549645392487472564075417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40732860523316630085433889 30549645392487472564075417)
              ·
                refine ⟨22912234044365604423056563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30549645392487472564075417 22912234044365604423056563)
                ·
                  refine ⟨34368351066548406634584845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22912234044365604423056563 34368351066548406634584845)
                  ·
                    refine ⟨12888131649955652487969317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34368351066548406634584845 12888131649955652487969317)
                    ·
                      refine ⟨2416524684366684841494247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12888131649955652487969317 2416524684366684841494247)
                      ·
                        rfl

theorem cell23_4706165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4706165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706165 prefixEnd_4706165 := by exact prefixLift 4706165
  have htrace : WordTrace (prefixWord ++ tailWord_4706165) baseStart_4706165 baseEnd_4706165 := by
    simpa [prefixWord, tailWord_4706165, baseEnd_4706165] using wordTrace_append hprefix tailTrace_4706165
  have hstable : (prefixWord ++ tailWord_4706165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706165).length < 2 ^ (prefixWord ++ tailWord_4706165).sum := by decide
  have hdescent : baseEnd_4706165 < baseStart_4706165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706185 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 3]
def baseStart_4706185 : Nat := 118140960795 + 4706185 * 2 ^ 59
def prefixEnd_4706185 : Nat := 4983230072969 + 3 ^ 40 * 4706185 * 2
def baseEnd_4706185 : Nat := 2416534953979774763244155

theorem tailTrace_4706185 : CollatzResearch.WordTrace tailWord_4706185 prefixEnd_4706185 2416534953979774763244155 := by
  unfold tailWord_4706185
  simp only [CollatzResearch.WordTrace]
  refine ⟨171648668455302972253112009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114432445636868648168741339 171648668455302972253112009)
  ·
    refine ⟨128736501341477229189834007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171648668455302972253112009 128736501341477229189834007)
    ·
      refine ⟨193104752012215843784751011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128736501341477229189834007 193104752012215843784751011)
      ·
        refine ⟨289657128018323765677126517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193104752012215843784751011 289657128018323765677126517)
        ·
          refine ⟨27155355751717853032230611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 289657128018323765677126517 27155355751717853032230611)
          ·
            refine ⟨40733033627576779548345917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27155355751717853032230611 40733033627576779548345917)
            ·
              refine ⟨15274887610341292330629719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40733033627576779548345917 15274887610341292330629719)
              ·
                refine ⟨22912331415511938495944579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15274887610341292330629719 22912331415511938495944579)
                ·
                  refine ⟨34368497123267907743916869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22912331415511938495944579 34368497123267907743916869)
                  ·
                    refine ⟨6444093210612732701984413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34368497123267907743916869 6444093210612732701984413)
                    ·
                      refine ⟨2416534953979774763244155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6444093210612732701984413 2416534953979774763244155)
                      ·
                        rfl

theorem cell23_4706185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_4706185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706185 prefixEnd_4706185 := by exact prefixLift 4706185
  have htrace : WordTrace (prefixWord ++ tailWord_4706185) baseStart_4706185 baseEnd_4706185 := by
    simpa [prefixWord, tailWord_4706185, baseEnd_4706185] using wordTrace_append hprefix tailTrace_4706185
  have hstable : (prefixWord ++ tailWord_4706185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706185).length < 2 ^ (prefixWord ++ tailWord_4706185).sum := by decide
  have hdescent : baseEnd_4706185 < baseStart_4706185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706188 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 8]
def baseStart_4706188 : Nat := 118140960795 + 4706188 * 2 ^ 59
def prefixEnd_4706188 : Nat := 4983230072969 + 3 ^ 40 * 4706188 * 2
def baseEnd_4706188 : Nat := 268504054935748694611849

theorem tailTrace_4706188 : CollatzResearch.WordTrace tailWord_4706188 prefixEnd_4706188 268504054935748694611849 := by
  unfold tailWord_4706188
  simp only [CollatzResearch.WordTrace]
  refine ⟨85824388937146051882735609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114432518582861402510314145 85824388937146051882735609)
  ·
    refine ⟨64368291702859538912051707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85824388937146051882735609 64368291702859538912051707)
    ·
      refine ⟨96552437554289308368077561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64368291702859538912051707 96552437554289308368077561)
      ·
        refine ⟨72414328165716981276058171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96552437554289308368077561 72414328165716981276058171)
        ·
          refine ⟨108621492248575471914087257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72414328165716981276058171 108621492248575471914087257)
          ·
            refine ⟨81466119186431603935565443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108621492248575471914087257 81466119186431603935565443)
            ·
              refine ⟨122199178779647405903348165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81466119186431603935565443 122199178779647405903348165)
              ·
                refine ⟨22912346021183888606877781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122199178779647405903348165 22912346021183888606877781)
                ·
                  refine ⟨268504054935748694611849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22912346021183888606877781 268504054935748694611849)
                  ·
                    rfl

theorem cell23_4706188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_4706188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706188 prefixEnd_4706188 := by exact prefixLift 4706188
  have htrace : WordTrace (prefixWord ++ tailWord_4706188) baseStart_4706188 baseEnd_4706188 := by
    simpa [prefixWord, tailWord_4706188, baseEnd_4706188] using wordTrace_append hprefix tailTrace_4706188
  have hstable : (prefixWord ++ tailWord_4706188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706188).length < 2 ^ (prefixWord ++ tailWord_4706188).sum := by decide
  have hdescent : baseEnd_4706188 < baseStart_4706188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706192 : List Nat := [2, 1, 1, 1, 1, 1, 2, 9, 1, 4]
def baseStart_4706192 : Nat := 118140960795 + 4706192 * 2 ^ 59
def prefixEnd_4706192 : Nat := 4983230072969 + 3 ^ 40 * 4706192 * 2
def baseEnd_4706192 : Nat := 805512849448118745285541

theorem tailTrace_4706192 : CollatzResearch.WordTrace tailWord_4706192 prefixEnd_4706192 805512849448118745285541 := by
  unfold tailWord_4706192
  simp only [CollatzResearch.WordTrace]
  refine ⟨85824461883138806224308415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114432615844185074965744553 85824461883138806224308415)
  ·
    refine ⟨128736692824708209336462623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85824461883138806224308415 128736692824708209336462623)
    ·
      refine ⟨193105039237062314004693935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128736692824708209336462623 193105039237062314004693935)
      ·
        refine ⟨289657558855593471007040903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193105039237062314004693935 289657558855593471007040903)
        ·
          refine ⟨434486338283390206510561355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289657558855593471007040903 434486338283390206510561355)
          ·
            refine ⟨651729507425085309765842033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434486338283390206510561355 651729507425085309765842033)
            ·
              refine ⟨488797130568813982324381525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651729507425085309765842033 488797130568813982324381525)
              ·
                refine ⟨2864045686926644427681923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 488797130568813982324381525 2864045686926644427681923)
                ·
                  refine ⟨4296068530389966641522885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864045686926644427681923 4296068530389966641522885)
                  ·
                    refine ⟨805512849448118745285541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296068530389966641522885 805512849448118745285541)
                    ·
                      rfl

theorem cell23_4706192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 4].length) (baseStart_4706192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706192 prefixEnd_4706192 := by exact prefixLift 4706192
  have htrace : WordTrace (prefixWord ++ tailWord_4706192) baseStart_4706192 baseEnd_4706192 := by
    simpa [prefixWord, tailWord_4706192, baseEnd_4706192] using wordTrace_append hprefix tailTrace_4706192
  have hstable : (prefixWord ++ tailWord_4706192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706192).length < 2 ^ (prefixWord ++ tailWord_4706192).sum := by decide
  have hdescent : baseEnd_4706192 < baseStart_4706192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706205 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 8]
def baseStart_4706205 : Nat := 118140960795 + 4706205 * 2 ^ 59
def prefixEnd_4706205 : Nat := 4983230072969 + 3 ^ 40 * 4706205 * 2
def baseEnd_4706205 : Nat := 268505024843651631666007

theorem tailTrace_4706205 : CollatzResearch.WordTrace tailWord_4706205 prefixEnd_4706205 268505024843651631666007 := by
  unfold tailWord_4706205
  simp only [CollatzResearch.WordTrace]
  refine ⟨171649397915230515668840069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114432931943487010445893379 171649397915230515668840069)
  ·
    refine ⟨32184262109105721687907513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171649397915230515668840069 32184262109105721687907513)
    ·
      refine ⟨24138196581829291265930635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32184262109105721687907513 24138196581829291265930635)
      ·
        refine ⟨36207294872743936898895953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24138196581829291265930635 36207294872743936898895953)
        ·
          refine ⟨27155471154557952674171965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36207294872743936898895953 27155471154557952674171965)
          ·
            refine ⟨10183301682959232252814487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27155471154557952674171965 10183301682959232252814487)
            ·
              refine ⟨15274952524438848379221731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10183301682959232252814487 15274952524438848379221731)
              ·
                refine ⟨22912428786658272568832597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15274952524438848379221731 22912428786658272568832597)
                ·
                  refine ⟨268505024843651631666007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22912428786658272568832597 268505024843651631666007)
                  ·
                    rfl

theorem cell23_4706205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_4706205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706205 prefixEnd_4706205 := by exact prefixLift 4706205
  have htrace : WordTrace (prefixWord ++ tailWord_4706205) baseStart_4706205 baseEnd_4706205 := by
    simpa [prefixWord, tailWord_4706205, baseEnd_4706205] using wordTrace_append hprefix tailTrace_4706205
  have hstable : (prefixWord ++ tailWord_4706205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706205).length < 2 ^ (prefixWord ++ tailWord_4706205).sum := by decide
  have hdescent : baseEnd_4706205 < baseStart_4706205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706209 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 3, 4]
def baseStart_4706209 : Nat := 118140960795 + 4706209 * 2 ^ 59
def prefixEnd_4706209 : Nat := 4983230072969 + 3 ^ 40 * 4706209 * 2
def baseEnd_4706209 : Nat := 805515759171827556448015

theorem tailTrace_4706209 : CollatzResearch.WordTrace tailWord_4706209 prefixEnd_4706209 805515759171827556448015 := by
  unfold tailWord_4706209
  simp only [CollatzResearch.WordTrace]
  refine ⟨171649543807216024351985681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114433029204810682901323787 171649543807216024351985681)
  ·
    refine ⟨128737157855412018263989261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171649543807216024351985681 128737157855412018263989261)
    ·
      refine ⟨48276434195779506848995973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128737157855412018263989261 48276434195779506848995973)
      ·
        refine ⟨9051831411708657534186745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48276434195779506848995973 9051831411708657534186745)
        ·
          refine ⟨6788873558781493150640059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9051831411708657534186745 6788873558781493150640059)
          ·
            refine ⟨10183310338172239725960089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6788873558781493150640059 10183310338172239725960089)
            ·
              refine ⟨7637482753629179794470067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10183310338172239725960089 7637482753629179794470067)
              ·
                refine ⟨11456224130443769691705101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637482753629179794470067 11456224130443769691705101)
                ·
                  refine ⟨4296084048916413634389413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11456224130443769691705101 4296084048916413634389413)
                  ·
                    refine ⟨805515759171827556448015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296084048916413634389413 805515759171827556448015)
                    ·
                      rfl

theorem cell23_4706209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_4706209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706209 prefixEnd_4706209 := by exact prefixLift 4706209
  have htrace : WordTrace (prefixWord ++ tailWord_4706209) baseStart_4706209 baseEnd_4706209 := by
    simpa [prefixWord, tailWord_4706209, baseEnd_4706209] using wordTrace_append hprefix tailTrace_4706209
  have hstable : (prefixWord ++ tailWord_4706209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706209).length < 2 ^ (prefixWord ++ tailWord_4706209).sum := by decide
  have hdescent : baseEnd_4706209 < baseStart_4706209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706232 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_4706232 : Nat := 118140960795 + 4706232 * 2 ^ 59
def prefixEnd_4706232 : Nat := 4983230072969 + 3 ^ 40 * 4706232 * 2
def baseEnd_4706232 : Nat := 2416559087570536079356439

theorem tailTrace_4706232 : CollatzResearch.WordTrace tailWord_4706232 prefixEnd_4706232 2416559087570536079356439 := by
  unfold tailWord_4706232
  simp only [CollatzResearch.WordTrace]
  refine ⟨85825191343066349640036475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114433588457421799520048633 85825191343066349640036475)
  ·
    refine ⟨128737787014599524460054713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85825191343066349640036475 128737787014599524460054713)
    ·
      refine ⟨96553340260949643345041035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128737787014599524460054713 96553340260949643345041035)
      ·
        refine ⟨144830010391424465017561553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96553340260949643345041035 144830010391424465017561553)
        ·
          refine ⟨108622507793568348763171165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144830010391424465017561553 108622507793568348763171165)
          ·
            refine ⟨40733440422588130786189187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108622507793568348763171165 40733440422588130786189187)
            ·
              refine ⟨61100160633882196179283781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40733440422588130786189187 61100160633882196179283781)
              ·
                refine ⟨11456280118852911783615709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61100160633882196179283781 11456280118852911783615709)
                ·
                  refine ⟨4296105044569841918855891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11456280118852911783615709 4296105044569841918855891)
                  ·
                    refine ⟨6444157566854762878283837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296105044569841918855891 6444157566854762878283837)
                    ·
                      refine ⟨2416559087570536079356439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6444157566854762878283837 2416559087570536079356439)
                      ·
                        rfl

theorem cell23_4706232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_4706232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706232 prefixEnd_4706232 := by exact prefixLift 4706232
  have htrace : WordTrace (prefixWord ++ tailWord_4706232) baseStart_4706232 baseEnd_4706232 := by
    simpa [prefixWord, tailWord_4706232, baseEnd_4706232] using wordTrace_append hprefix tailTrace_4706232
  have hstable : (prefixWord ++ tailWord_4706232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706232).length < 2 ^ (prefixWord ++ tailWord_4706232).sum := by decide
  have hdescent : baseEnd_4706232 < baseStart_4706232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706235 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 1, 5]
def baseStart_4706235 : Nat := 118140960795 + 4706235 * 2 ^ 59
def prefixEnd_4706235 : Nat := 4983230072969 + 3 ^ 40 * 4706235 * 2
def baseEnd_4706235 : Nat := 805520209337499855872975

theorem tailTrace_4706235 : CollatzResearch.WordTrace tailWord_4706235 prefixEnd_4706235 805520209337499855872975 := by
  unfold tailWord_4706235
  simp only [CollatzResearch.WordTrace]
  refine ⟨171650492105121830792432159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114433661403414553861621439 171650492105121830792432159)
  ·
    refine ⟨257475738157682746188648239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171650492105121830792432159 257475738157682746188648239)
    ·
      refine ⟨386213607236524119282972359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257475738157682746188648239 386213607236524119282972359)
      ·
        refine ⟨579320410854786178924458539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386213607236524119282972359 579320410854786178924458539)
        ·
          refine ⟨868980616282179268386687809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579320410854786178924458539 868980616282179268386687809)
          ·
            refine ⟨651735462211634451290015857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 868980616282179268386687809 651735462211634451290015857)
            ·
              refine ⟨488801596658725838467511893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651735462211634451290015857 488801596658725838467511893)
              ·
                refine ⟨5728143710844443419541155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 488801596658725838467511893 5728143710844443419541155)
                ·
                  refine ⟨8592215566266665129311733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728143710844443419541155 8592215566266665129311733)
                  ·
                    refine ⟨805520209337499855872975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8592215566266665129311733 805520209337499855872975)
                    ·
                      rfl

theorem cell23_4706235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 5].length) (baseStart_4706235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706235 prefixEnd_4706235 := by exact prefixLift 4706235
  have htrace : WordTrace (prefixWord ++ tailWord_4706235) baseStart_4706235 baseEnd_4706235 := by
    simpa [prefixWord, tailWord_4706235, baseEnd_4706235] using wordTrace_append hprefix tailTrace_4706235
  have hstable : (prefixWord ++ tailWord_4706235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706235).length < 2 ^ (prefixWord ++ tailWord_4706235).sum := by decide
  have hdescent : baseEnd_4706235 < baseStart_4706235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706252 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_4706252 : Nat := 118140960795 + 4706252 * 2 ^ 59
def prefixEnd_4706252 : Nat := 4983230072969 + 3 ^ 40 * 4706252 * 2
def baseEnd_4706252 : Nat := 805523119061208667035449

theorem tailTrace_4706252 : CollatzResearch.WordTrace tailWord_4706252 prefixEnd_4706252 805523119061208667035449 := by
  unfold tailWord_4706252
  simp only [CollatzResearch.WordTrace]
  refine ⟨85825556073030121347900505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114434074764040161797200673 85825556073030121347900505)
  ·
    refine ⟨64369167054772591010925379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85825556073030121347900505 64369167054772591010925379)
    ·
      refine ⟨96553750582158886516388069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64369167054772591010925379 96553750582158886516388069)
      ·
        refine ⟨18103828234154791221822763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96553750582158886516388069 18103828234154791221822763)
        ·
          refine ⟨27155742351232186832734145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18103828234154791221822763 27155742351232186832734145)
          ·
            refine ⟨20366806763424140124550609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27155742351232186832734145 20366806763424140124550609)
            ·
              refine ⟨15275105072568105093412957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20366806763424140124550609 15275105072568105093412957)
              ·
                refine ⟨5728164402213039410029859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15275105072568105093412957 5728164402213039410029859)
                ·
                  refine ⟨8592246603319559115044789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728164402213039410029859 8592246603319559115044789)
                  ·
                    refine ⟨805523119061208667035449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8592246603319559115044789 805523119061208667035449)
                    ·
                      rfl

theorem cell23_4706252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_4706252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706252 prefixEnd_4706252 := by exact prefixLift 4706252
  have htrace : WordTrace (prefixWord ++ tailWord_4706252) baseStart_4706252 baseEnd_4706252 := by
    simpa [prefixWord, tailWord_4706252, baseEnd_4706252] using wordTrace_append hprefix tailTrace_4706252
  have hstable : (prefixWord ++ tailWord_4706252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706252).length < 2 ^ (prefixWord ++ tailWord_4706252).sum := by decide
  have hdescent : baseEnd_4706252 < baseStart_4706252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706266 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_4706266 : Nat := 118140960795 + 4706266 * 2 ^ 59
def prefixEnd_4706266 : Nat := 4983230072969 + 3 ^ 40 * 4706266 * 2
def baseEnd_4706266 : Nat := 2416576545912788946331283

theorem tailTrace_4706266 : CollatzResearch.WordTrace tailWord_4706266 prefixEnd_4706266 2416576545912788946331283 := by
  unfold tailWord_4706266
  simp only [CollatzResearch.WordTrace]
  refine ⟨42912905692002380771702663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114434415178673015391207101 42912905692002380771702663)
  ·
    refine ⟨64369358538003571157553995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42912905692002380771702663 64369358538003571157553995)
    ·
      refine ⟨96554037807005356736330993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64369358538003571157553995 96554037807005356736330993)
      ·
        refine ⟨72415528355254017552248245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96554037807005356736330993 72415528355254017552248245)
        ·
          refine ⟨6788955783305064145523273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72415528355254017552248245 6788955783305064145523273)
          ·
            refine ⟨5091716837478798109142455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6788955783305064145523273 5091716837478798109142455)
            ·
              refine ⟨7637575256218197163713683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091716837478798109142455 7637575256218197163713683)
              ·
                refine ⟨11456362884327295745570525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637575256218197163713683 11456362884327295745570525)
                ·
                  refine ⟨4296136081622735904588947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11456362884327295745570525 4296136081622735904588947)
                  ·
                    refine ⟨6444204122434103856883421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296136081622735904588947 6444204122434103856883421)
                    ·
                      refine ⟨2416576545912788946331283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6444204122434103856883421 2416576545912788946331283)
                      ·
                        rfl

theorem cell23_4706266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_4706266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706266 prefixEnd_4706266 := by exact prefixLift 4706266
  have htrace : WordTrace (prefixWord ++ tailWord_4706266) baseStart_4706266 baseEnd_4706266 := by
    simpa [prefixWord, tailWord_4706266, baseEnd_4706266] using wordTrace_append hprefix tailTrace_4706266
  have hstable : (prefixWord ++ tailWord_4706266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706266).length < 2 ^ (prefixWord ++ tailWord_4706266).sum := by decide
  have hdescent : baseEnd_4706266 < baseStart_4706266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706317 : List Nat := [1, 7, 1, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4706317 : Nat := 118140960795 + 4706317 * 2 ^ 59
def prefixEnd_4706317 : Nat := 4983230072969 + 3 ^ 40 * 4706317 * 2
def baseEnd_4706317 : Nat := 2416602733426168246793549

theorem tailTrace_4706317 : CollatzResearch.WordTrace tailWord_4706317 prefixEnd_4706317 2416602733426168246793549 := by
  unfold tailWord_4706317
  simp only [CollatzResearch.WordTrace]
  refine ⟨171653482890824758796917205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114435655260549839197944803 171653482890824758796917205)
  ·
    refine ⟨4023128505253705284302747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 171653482890824758796917205 4023128505253705284302747)
    ·
      refine ⟨6034692757880557926454121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4023128505253705284302747 6034692757880557926454121)
      ·
        refine ⟨4526019568410418444840591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6034692757880557926454121 4526019568410418444840591)
        ·
          refine ⟨6789029352615627667260887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526019568410418444840591 6789029352615627667260887)
          ·
            refine ⟨10183544028923441500891331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789029352615627667260887 10183544028923441500891331)
            ·
              refine ⟨15275316043385162251336997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10183544028923441500891331 15275316043385162251336997)
              ·
                refine ⟨2864121758134717922125687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15275316043385162251336997 2864121758134717922125687)
                ·
                  refine ⟨4296182637202076883188531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864121758134717922125687 4296182637202076883188531)
                  ·
                    refine ⟨6444273955803115324782797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296182637202076883188531 6444273955803115324782797)
                    ·
                      refine ⟨2416602733426168246793549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6444273955803115324782797 2416602733426168246793549)
                      ·
                        rfl

theorem cell23_4706317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4706317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706317 prefixEnd_4706317 := by exact prefixLift 4706317
  have htrace : WordTrace (prefixWord ++ tailWord_4706317) baseStart_4706317 baseEnd_4706317 := by
    simpa [prefixWord, tailWord_4706317, baseEnd_4706317] using wordTrace_append hprefix tailTrace_4706317
  have hstable : (prefixWord ++ tailWord_4706317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706317).length < 2 ^ (prefixWord ++ tailWord_4706317).sum := by decide
  have hdescent : baseEnd_4706317 < baseStart_4706317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706323 : List Nat := [1, 1, 1, 2, 1, 4, 6, 2, 1, 2, 2]
def baseStart_4706323 : Nat := 118140960795 + 4706323 * 2 ^ 59
def prefixEnd_4706323 : Nat := 4983230072969 + 3 ^ 40 * 4706323 * 2
def baseEnd_4706323 : Nat := 2416605814310095223318521

theorem tailTrace_4706323 : CollatzResearch.WordTrace tailWord_4706323 prefixEnd_4706323 2416605814310095223318521 := by
  unfold tailWord_4706323
  simp only [CollatzResearch.WordTrace]
  refine ⟨171653701728803021821635623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114435801152535347881090415 171653701728803021821635623)
  ·
    refine ⟨257480552593204532732453435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171653701728803021821635623 257480552593204532732453435)
    ·
      refine ⟨386220828889806799098680153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257480552593204532732453435 386220828889806799098680153)
      ·
        refine ⟨289665621667355099324010115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386220828889806799098680153 289665621667355099324010115)
        ·
          refine ⟨434498432501032648986015173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289665621667355099324010115 434498432501032648986015173)
          ·
            refine ⟨81468456093943621684877845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 434498432501032648986015173 81468456093943621684877845)
            ·
              refine ⟨3818833879403607266478649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81468456093943621684877845 3818833879403607266478649)
              ·
                refine ⟨2864125409552705449858987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818833879403607266478649 2864125409552705449858987)
                ·
                  refine ⟨4296188114329058174788481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864125409552705449858987 4296188114329058174788481)
                  ·
                    refine ⟨3222141085746793631091361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4296188114329058174788481 3222141085746793631091361)
                    ·
                      refine ⟨2416605814310095223318521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222141085746793631091361 2416605814310095223318521)
                      ·
                        rfl

theorem cell23_4706323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 2, 2].length) (baseStart_4706323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706323 prefixEnd_4706323 := by exact prefixLift 4706323
  have htrace : WordTrace (prefixWord ++ tailWord_4706323) baseStart_4706323 baseEnd_4706323 := by
    simpa [prefixWord, tailWord_4706323, baseEnd_4706323] using wordTrace_append hprefix tailTrace_4706323
  have hstable : (prefixWord ++ tailWord_4706323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706323).length < 2 ^ (prefixWord ++ tailWord_4706323).sum := by decide
  have hdescent : baseEnd_4706323 < baseStart_4706323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706339 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 3]
def baseStart_4706339 : Nat := 118140960795 + 4706339 * 2 ^ 59
def prefixEnd_4706339 : Nat := 4983230072969 + 3 ^ 40 * 4706339 * 2
def baseEnd_4706339 : Nat := 2416614030000567160718447

theorem tailTrace_4706339 : CollatzResearch.WordTrace tailWord_4706339 prefixEnd_4706339 2416614030000567160718447 := by
  unfold tailWord_4706339
  simp only [CollatzResearch.WordTrace]
  refine ⟨171654285296745056554218071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114436190197830037702812047 171654285296745056554218071)
  ·
    refine ⟨257481427945117584831327107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171654285296745056554218071 257481427945117584831327107)
    ·
      refine ⟨386222141917676377246990661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257481427945117584831327107 386222141917676377246990661)
      ·
        refine ⟨72416651609564320733810749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 386222141917676377246990661 72416651609564320733810749)
        ·
          refine ⟨27156244353586620275179031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72416651609564320733810749 27156244353586620275179031)
          ·
            refine ⟨40734366530379930412768547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27156244353586620275179031 40734366530379930412768547)
            ·
              refine ⟨61101549795569895619152821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40734366530379930412768547 61101549795569895619152821)
              ·
                refine ⟨5728270293334677714295577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61101549795569895619152821 5728270293334677714295577)
                ·
                  refine ⟨4296202720001008285721683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5728270293334677714295577 4296202720001008285721683)
                  ·
                    refine ⟨6444304080001512428582525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296202720001008285721683 6444304080001512428582525)
                    ·
                      refine ⟨2416614030000567160718447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6444304080001512428582525 2416614030000567160718447)
                      ·
                        rfl

theorem cell23_4706339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_4706339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706339 prefixEnd_4706339 := by exact prefixLift 4706339
  have htrace : WordTrace (prefixWord ++ tailWord_4706339) baseStart_4706339 baseEnd_4706339 := by
    simpa [prefixWord, tailWord_4706339, baseEnd_4706339] using wordTrace_append hprefix tailTrace_4706339
  have hstable : (prefixWord ++ tailWord_4706339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706339).length < 2 ^ (prefixWord ++ tailWord_4706339).sum := by decide
  have hdescent : baseEnd_4706339 < baseStart_4706339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706379 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 4, 2, 2]
def baseStart_4706379 : Nat := 118140960795 + 4706379 * 2 ^ 59
def prefixEnd_4706379 : Nat := 4983230072969 + 3 ^ 40 * 4706379 * 2
def baseEnd_4706379 : Nat := 2416634569226747004218263

theorem tailTrace_4706379 : CollatzResearch.WordTrace tailWord_4706379 prefixEnd_4706379 2416634569226747004218263 := by
  unfold tailWord_4706379
  simp only [CollatzResearch.WordTrace]
  refine ⟨171655744216600143385674191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114437162811066762257116127 171655744216600143385674191)
  ·
    refine ⟨257483616324900215078511287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171655744216600143385674191 257483616324900215078511287)
    ·
      refine ⟨386225424487350322617766931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257483616324900215078511287 386225424487350322617766931)
      ·
        refine ⟨579338136731025483926650397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386225424487350322617766931 579338136731025483926650397)
        ·
          refine ⟨217251801274134556472493899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 579338136731025483926650397 217251801274134556472493899)
          ·
            refine ⟨325877701911201834708740849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217251801274134556472493899 325877701911201834708740849)
            ·
              refine ⟨244408276433401376031555637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325877701911201834708740849 244408276433401376031555637)
              ·
                refine ⟨22913275915631379002958341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244408276433401376031555637 22913275915631379002958341)
                ·
                  refine ⟨4296239234180883563054689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22913275915631379002958341 4296239234180883563054689)
                  ·
                    refine ⟨3222179425635662672291017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4296239234180883563054689 3222179425635662672291017)
                    ·
                      refine ⟨2416634569226747004218263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222179425635662672291017 2416634569226747004218263)
                      ·
                        rfl

theorem cell23_4706379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 2, 2].length) (baseStart_4706379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706379 prefixEnd_4706379 := by exact prefixLift 4706379
  have htrace : WordTrace (prefixWord ++ tailWord_4706379) baseStart_4706379 baseEnd_4706379 := by
    simpa [prefixWord, tailWord_4706379, baseEnd_4706379] using wordTrace_append hprefix tailTrace_4706379
  have hstable : (prefixWord ++ tailWord_4706379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706379).length < 2 ^ (prefixWord ++ tailWord_4706379).sum := by decide
  have hdescent : baseEnd_4706379 < baseStart_4706379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706392 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_4706392 : Nat := 118140960795 + 4706392 * 2 ^ 59
def prefixEnd_4706392 : Nat := 4983230072969 + 3 ^ 40 * 4706392 * 2
def baseEnd_4706392 : Nat := 2416641244475255453355703

theorem tailTrace_4706392 : CollatzResearch.WordTrace tailWord_4706392 prefixEnd_4706392 2416641244475255453355703 := by
  unfold tailWord_4706392
  simp only [CollatzResearch.WordTrace]
  refine ⟨85828109182776523302948715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114437478910368697737264953 85828109182776523302948715)
  ·
    refine ⟨128742163774164784954423073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85828109182776523302948715 128742163774164784954423073)
    ·
      refine ⟨96556622830623588715817305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128742163774164784954423073 96556622830623588715817305)
      ·
        refine ⟨72417467122967691536862979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96556622830623588715817305 72417467122967691536862979)
        ·
          refine ⟨108626200684451537305294469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72417467122967691536862979 108626200684451537305294469)
          ·
            refine ⟨20367412628334663244742713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108626200684451537305294469 20367412628334663244742713)
            ·
              refine ⟨15275559471250997433557035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20367412628334663244742713 15275559471250997433557035)
              ·
                refine ⟨22913339206876496150335553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15275559471250997433557035 22913339206876496150335553)
                ·
                  refine ⟨17185004405157372112751665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22913339206876496150335553 17185004405157372112751665)
                  ·
                    refine ⟨12888753303868029084563749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17185004405157372112751665 12888753303868029084563749)
                    ·
                      refine ⟨2416641244475255453355703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12888753303868029084563749 2416641244475255453355703)
                      ·
                        rfl

theorem cell23_4706392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_4706392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706392 prefixEnd_4706392 := by exact prefixLift 4706392
  have htrace : WordTrace (prefixWord ++ tailWord_4706392) baseStart_4706392 baseEnd_4706392 := by
    simpa [prefixWord, tailWord_4706392, baseEnd_4706392] using wordTrace_append hprefix tailTrace_4706392
  have hstable : (prefixWord ++ tailWord_4706392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706392).length < 2 ^ (prefixWord ++ tailWord_4706392).sum := by decide
  have hdescent : baseEnd_4706392 < baseStart_4706392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706396 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_4706396 : Nat := 118140960795 + 4706396 * 2 ^ 59
def prefixEnd_4706396 : Nat := 4983230072969 + 3 ^ 40 * 4706396 * 2
def baseEnd_4706396 : Nat := 2416643298397873437705685

theorem tailTrace_4706396 : CollatzResearch.WordTrace tailWord_4706396 prefixEnd_4706396 2416643298397873437705685 := by
  unfold tailWord_4706396
  simp only [CollatzResearch.WordTrace]
  refine ⟨85828182128769277644521521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114437576171692370192695361 85828182128769277644521521)
  ·
    refine ⟨64371136596576958233391141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85828182128769277644521521 64371136596576958233391141)
    ·
      refine ⟨12069588111858179668760839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64371136596576958233391141 12069588111858179668760839)
      ·
        refine ⟨18104382167787269503141259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12069588111858179668760839 18104382167787269503141259)
        ·
          refine ⟨27156573251680904254711889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18104382167787269503141259 27156573251680904254711889)
          ·
            refine ⟨20367429938760678191033917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27156573251680904254711889 20367429938760678191033917)
            ·
              refine ⟨7637786227035254321637719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20367429938760678191033917 7637786227035254321637719)
              ·
                refine ⟨11456679340552881482456579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637786227035254321637719 11456679340552881482456579)
                ·
                  refine ⟨17185019010829322223684869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11456679340552881482456579 17185019010829322223684869)
                  ·
                    refine ⟨3222191064530497916940913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17185019010829322223684869 3222191064530497916940913)
                    ·
                      refine ⟨2416643298397873437705685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222191064530497916940913 2416643298397873437705685)
                      ·
                        rfl

theorem cell23_4706396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_4706396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706396 prefixEnd_4706396 := by exact prefixLift 4706396
  have htrace : WordTrace (prefixWord ++ tailWord_4706396) baseStart_4706396 baseEnd_4706396 := by
    simpa [prefixWord, tailWord_4706396, baseEnd_4706396] using wordTrace_append hprefix tailTrace_4706396
  have hstable : (prefixWord ++ tailWord_4706396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706396).length < 2 ^ (prefixWord ++ tailWord_4706396).sum := by decide
  have hdescent : baseEnd_4706396 < baseStart_4706396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706436 : List Nat := [2, 3, 2, 1, 2, 1, 5, 2, 5]
def baseStart_4706436 : Nat := 118140960795 + 4706436 * 2 ^ 59
def prefixEnd_4706436 : Nat := 4983230072969 + 3 ^ 40 * 4706436 * 2
def baseEnd_4706436 : Nat := 268518204180450364578389

theorem tailTrace_4706436 : CollatzResearch.WordTrace tailWord_4706436 prefixEnd_4706436 268518204180450364578389 := by
  unfold tailWord_4706436
  simp only [CollatzResearch.WordTrace]
  refine ⟨85828911588696821060249581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114438548784929094746999441 85828911588696821060249581)
  ·
    refine ⟨32185841845761307897593593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85828911588696821060249581 32185841845761307897593593)
    ·
      refine ⟨24139381384320980923195195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32185841845761307897593593 24139381384320980923195195)
      ·
        refine ⟨36209072076481471384792793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24139381384320980923195195 36209072076481471384792793)
        ·
          refine ⟨27156804057361103538594595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36209072076481471384792793 27156804057361103538594595)
          ·
            refine ⟨40735206086041655307891893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27156804057361103538594595 40735206086041655307891893)
            ·
              refine ⟨3818925570566405185114865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40735206086041655307891893 3818925570566405185114865)
              ·
                refine ⟨2864194177924803888836149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818925570566405185114865 2864194177924803888836149)
                ·
                  refine ⟨268518204180450364578389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2864194177924803888836149 268518204180450364578389)
                  ·
                    rfl

theorem cell23_4706436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_4706436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706436 prefixEnd_4706436 := by exact prefixLift 4706436
  have htrace : WordTrace (prefixWord ++ tailWord_4706436) baseStart_4706436 baseEnd_4706436 := by
    simpa [prefixWord, tailWord_4706436, baseEnd_4706436] using wordTrace_append hprefix tailTrace_4706436
  have hstable : (prefixWord ++ tailWord_4706436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706436).length < 2 ^ (prefixWord ++ tailWord_4706436).sum := by decide
  have hdescent : baseEnd_4706436 < baseStart_4706436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706442 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4706442 : Nat := 118140960795 + 4706442 * 2 ^ 59
def prefixEnd_4706442 : Nat := 4983230072969 + 3 ^ 40 * 4706442 * 2
def baseEnd_4706442 : Nat := 2416666918507980257730473

theorem tailTrace_4706442 : CollatzResearch.WordTrace tailWord_4706442 prefixEnd_4706442 2416666918507980257730473 := by
  unfold tailWord_4706442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42914510503842976286304395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114438694676914603430145053 42914510503842976286304395)
  ·
    refine ⟨64371765755764464429456593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42914510503842976286304395 64371765755764464429456593)
    ·
      refine ⟨48278824316823348322092445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64371765755764464429456593 48278824316823348322092445)
      ·
        refine ⟨18104559118808755620784667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48278824316823348322092445 18104559118808755620784667)
        ·
          refine ⟨27156838678213133431177001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18104559118808755620784667 27156838678213133431177001)
          ·
            refine ⟨20367629008659850073382751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27156838678213133431177001 20367629008659850073382751)
            ·
              refine ⟨30551443512989775110074127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20367629008659850073382751 30551443512989775110074127)
              ·
                refine ⟨45827165269484662665111191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30551443512989775110074127 45827165269484662665111191)
                ·
                  refine ⟨68740747904226993997666787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45827165269484662665111191 68740747904226993997666787)
                  ·
                    refine ⟨103111121856340490996500181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68740747904226993997666787 103111121856340490996500181)
                    ·
                      refine ⟨2416666918507980257730473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103111121856340490996500181 2416666918507980257730473)
                      ·
                        rfl

theorem cell23_4706442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4706442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706442 prefixEnd_4706442 := by exact prefixLift 4706442
  have htrace : WordTrace (prefixWord ++ tailWord_4706442) baseStart_4706442 baseEnd_4706442 := by
    simpa [prefixWord, tailWord_4706442, baseEnd_4706442] using wordTrace_append hprefix tailTrace_4706442
  have hstable : (prefixWord ++ tailWord_4706442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706442).length < 2 ^ (prefixWord ++ tailWord_4706442).sum := by decide
  have hdescent : baseEnd_4706442 < baseStart_4706442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706466 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_4706466 : Nat := 118140960795 + 4706466 * 2 ^ 59
def prefixEnd_4706466 : Nat := 4983230072969 + 3 ^ 40 * 4706466 * 2
def baseEnd_4706466 : Nat := 805559747347896054610121

theorem tailTrace_4706466 : CollatzResearch.WordTrace tailWord_4706466 prefixEnd_4706466 805559747347896054610121 := by
  unfold tailWord_4706466
  simp only [CollatzResearch.WordTrace]
  refine ⟨42914729341821239311022813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114439278244856638162727501 42914729341821239311022813)
  ·
    refine ⟨16093023503182964741633555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42914729341821239311022813 16093023503182964741633555)
    ·
      refine ⟨24139535254774447112450333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16093023503182964741633555 24139535254774447112450333)
      ·
        refine ⟨9052325720540417667168875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24139535254774447112450333 9052325720540417667168875)
        ·
          refine ⟨13578488580810626500753313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9052325720540417667168875 13578488580810626500753313)
          ·
            refine ⟨10183866435607969875564985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13578488580810626500753313 10183866435607969875564985)
            ·
              refine ⟨7637899826705977406673739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10183866435607969875564985 7637899826705977406673739)
              ·
                refine ⟨11456849740058966110010609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637899826705977406673739 11456849740058966110010609)
                ·
                  refine ⟨8592637305044224582507957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11456849740058966110010609 8592637305044224582507957)
                  ·
                    refine ⟨805559747347896054610121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8592637305044224582507957 805559747347896054610121)
                    ·
                      rfl

theorem cell23_4706466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_4706466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706466 prefixEnd_4706466 := by exact prefixLift 4706466
  have htrace : WordTrace (prefixWord ++ tailWord_4706466) baseStart_4706466 baseEnd_4706466 := by
    simpa [prefixWord, tailWord_4706466, baseEnd_4706466] using wordTrace_append hprefix tailTrace_4706466
  have hstable : (prefixWord ++ tailWord_4706466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706466).length < 2 ^ (prefixWord ++ tailWord_4706466).sum := by decide
  have hdescent : baseEnd_4706466 < baseStart_4706466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706469 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_4706469 : Nat := 118140960795 + 4706469 * 2 ^ 59
def prefixEnd_4706469 : Nat := 4983230072969 + 3 ^ 40 * 4706469 * 2
def baseEnd_4706469 : Nat := 2416680782485651652092849

theorem tailTrace_4706469 : CollatzResearch.WordTrace tailWord_4706469 prefixEnd_4706469 2416680782485651652092849 := by
  unfold tailWord_4706469
  simp only [CollatzResearch.WordTrace]
  refine ⟨171659026786274088756450461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114439351190849392504300307 171659026786274088756450461)
  ·
    refine ⟨64372135044852783283668923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171659026786274088756450461 64372135044852783283668923)
    ·
      refine ⟨96558202567279174925503385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64372135044852783283668923 96558202567279174925503385)
      ·
        refine ⟨72418651925459381194127539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96558202567279174925503385 72418651925459381194127539)
        ·
          refine ⟨108627977888189071791191309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72418651925459381194127539 108627977888189071791191309)
          ·
            refine ⟨40735491708070901921696741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108627977888189071791191309 40735491708070901921696741)
            ·
              refine ⟨7637904695263294110318139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40735491708070901921696741 7637904695263294110318139)
              ·
                refine ⟨11456857042894941165477209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637904695263294110318139 11456857042894941165477209)
                ·
                  refine ⟨8592642782171205874107907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11456857042894941165477209 8592642782171205874107907)
                  ·
                    refine ⟨12888964173256808811161861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8592642782171205874107907 12888964173256808811161861)
                    ·
                      refine ⟨2416680782485651652092849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12888964173256808811161861 2416680782485651652092849)
                      ·
                        rfl

theorem cell23_4706469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_4706469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706469 prefixEnd_4706469 := by exact prefixLift 4706469
  have htrace : WordTrace (prefixWord ++ tailWord_4706469) baseStart_4706469 baseEnd_4706469 := by
    simpa [prefixWord, tailWord_4706469, baseEnd_4706469] using wordTrace_append hprefix tailTrace_4706469
  have hstable : (prefixWord ++ tailWord_4706469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706469).length < 2 ^ (prefixWord ++ tailWord_4706469).sum := by decide
  have hdescent : baseEnd_4706469 < baseStart_4706469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706482 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_4706482 : Nat := 118140960795 + 4706482 * 2 ^ 59
def prefixEnd_4706482 : Nat := 4983230072969 + 3 ^ 40 * 4706482 * 2
def baseEnd_4706482 : Nat := 2416687457734160101230289

theorem tailTrace_4706482 : CollatzResearch.WordTrace tailWord_4706482 prefixEnd_4706482 2416687457734160101230289 := by
  unfold tailWord_4706482
  simp only [CollatzResearch.WordTrace]
  refine ⟨42914875233806747994168425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114439667290151327984449133 42914875233806747994168425)
  ·
    refine ⟨32186156425355060995626319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42914875233806747994168425 32186156425355060995626319)
    ·
      refine ⟨48279234638032591493439479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32186156425355060995626319 48279234638032591493439479)
      ·
        refine ⟨72418851957048887240159219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48279234638032591493439479 72418851957048887240159219)
        ·
          refine ⟨108628277935573330860238829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72418851957048887240159219 108628277935573330860238829)
          ·
            refine ⟨40735604225839999072589561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108628277935573330860238829 40735604225839999072589561)
            ·
              refine ⟨30551703169379999304442171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40735604225839999072589561 30551703169379999304442171)
              ·
                refine ⟨45827554754069998956663257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30551703169379999304442171 45827554754069998956663257)
                ·
                  refine ⟨34370666065552499217497443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45827554754069998956663257 34370666065552499217497443)
                  ·
                    refine ⟨51555999098328748826246165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34370666065552499217497443 51555999098328748826246165)
                    ·
                      refine ⟨2416687457734160101230289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51555999098328748826246165 2416687457734160101230289)
                      ·
                        rfl

theorem cell23_4706482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_4706482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706482 prefixEnd_4706482 := by exact prefixLift 4706482
  have htrace : WordTrace (prefixWord ++ tailWord_4706482) baseStart_4706482 baseEnd_4706482 := by
    simpa [prefixWord, tailWord_4706482, baseEnd_4706482] using wordTrace_append hprefix tailTrace_4706482
  have hstable : (prefixWord ++ tailWord_4706482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706482).length < 2 ^ (prefixWord ++ tailWord_4706482).sum := by decide
  have hdescent : baseEnd_4706482 < baseStart_4706482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706489 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4706489 : Nat := 118140960795 + 4706489 * 2 ^ 59
def prefixEnd_4706489 : Nat := 4983230072969 + 3 ^ 40 * 4706489 * 2
def baseEnd_4706489 : Nat := 2416691052098741573842757

theorem tailTrace_4706489 : CollatzResearch.WordTrace tailWord_4706489 prefixEnd_4706489 2416691052098741573842757 := by
  unfold tailWord_4706489
  simp only [CollatzResearch.WordTrace]
  refine ⟨171659756246201632172178521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114439837497467754781452347 171659756246201632172178521)
  ·
    refine ⟨128744817184651224129133891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171659756246201632172178521 128744817184651224129133891)
    ·
      refine ⟨193117225776976836193700837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128744817184651224129133891 193117225776976836193700837)
      ·
        refine ⟨36209479833183156786318907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193117225776976836193700837 36209479833183156786318907)
        ·
          refine ⟨54314219749774735179478361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36209479833183156786318907 54314219749774735179478361)
          ·
            refine ⟨40735664812331051384608771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54314219749774735179478361 40735664812331051384608771)
            ·
              refine ⟨61103497218496577076913157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40735664812331051384608771 61103497218496577076913157)
              ·
                refine ⟨11456905728468108201921217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61103497218496577076913157 11456905728468108201921217)
                ·
                  refine ⟨8592679296351081151440913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11456905728468108201921217 8592679296351081151440913)
                  ·
                    refine ⟨6444509472263310863580685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8592679296351081151440913 6444509472263310863580685)
                    ·
                      refine ⟨2416691052098741573842757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6444509472263310863580685 2416691052098741573842757)
                      ·
                        rfl

theorem cell23_4706489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4706489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706489 prefixEnd_4706489 := by exact prefixLift 4706489
  have htrace : WordTrace (prefixWord ++ tailWord_4706489) baseStart_4706489 baseEnd_4706489 := by
    simpa [prefixWord, tailWord_4706489, baseEnd_4706489] using wordTrace_append hprefix tailTrace_4706489
  have hstable : (prefixWord ++ tailWord_4706489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706489).length < 2 ^ (prefixWord ++ tailWord_4706489).sum := by decide
  have hdescent : baseEnd_4706489 < baseStart_4706489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706532 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_4706532 : Nat := 118140960795 + 4706532 * 2 ^ 59
def prefixEnd_4706532 : Nat := 4983230072969 + 3 ^ 40 * 4706532 * 2
def baseEnd_4706532 : Nat := 2416713131766884905605059

theorem tailTrace_4706532 : CollatzResearch.WordTrace tailWord_4706532 prefixEnd_4706532 2416713131766884905605059 := by
  unfold tailWord_4706532
  simp only [CollatzResearch.WordTrace]
  refine ⟨85830662292522925257996925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114440883056697233677329233 85830662292522925257996925)
  ·
    refine ⟨32186498359696096971748847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85830662292522925257996925 32186498359696096971748847)
    ·
      refine ⟨48279747539544145457623271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32186498359696096971748847 48279747539544145457623271)
      ·
        refine ⟨72419621309316218186434907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48279747539544145457623271 72419621309316218186434907)
        ·
          refine ⟨108629431963974327279652361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72419621309316218186434907 108629431963974327279652361)
          ·
            refine ⟨81472073972980745459739271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108629431963974327279652361 81472073972980745459739271)
            ·
              refine ⟨122208110959471118189608907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81472073972980745459739271 122208110959471118189608907)
              ·
                refine ⟨183312166439206677284413361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122208110959471118189608907 183312166439206677284413361)
                ·
                  refine ⟨137484124829405007963310021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183312166439206677284413361 137484124829405007963310021)
                  ·
                    refine ⟨25778273405513438993120629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137484124829405007963310021 25778273405513438993120629)
                    ·
                      refine ⟨2416713131766884905605059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25778273405513438993120629 2416713131766884905605059)
                      ·
                        rfl

theorem cell23_4706532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_4706532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706532 prefixEnd_4706532 := by exact prefixLift 4706532
  have htrace : WordTrace (prefixWord ++ tailWord_4706532) baseStart_4706532 baseEnd_4706532 := by
    simpa [prefixWord, tailWord_4706532, baseEnd_4706532] using wordTrace_append hprefix tailTrace_4706532
  have hstable : (prefixWord ++ tailWord_4706532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706532).length < 2 ^ (prefixWord ++ tailWord_4706532).sum := by decide
  have hdescent : baseEnd_4706532 < baseStart_4706532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706539 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 1, 5]
def baseStart_4706539 : Nat := 118140960795 + 4706539 * 2 ^ 59
def prefixEnd_4706539 : Nat := 4983230072969 + 3 ^ 40 * 4706539 * 2
def baseEnd_4706539 : Nat := 805572242043822126072509

theorem tailTrace_4706539 : CollatzResearch.WordTrace tailWord_4706539 prefixEnd_4706539 805572242043822126072509 := by
  unfold tailWord_4706539
  simp only [CollatzResearch.WordTrace]
  refine ⟨171661579896020490711498671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114441053264013660474332447 171661579896020490711498671)
  ·
    refine ⟨257492369844030736067248007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171661579896020490711498671 257492369844030736067248007)
    ·
      refine ⟨386238554766046104100872011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257492369844030736067248007 386238554766046104100872011)
      ·
        refine ⟨579357832149069156151308017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386238554766046104100872011 579357832149069156151308017)
        ·
          refine ⟨434518374111801867113481013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 579357832149069156151308017 434518374111801867113481013)
          ·
            refine ⟨40736097572981425041888845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 434518374111801867113481013 40736097572981425041888845)
            ·
              refine ⟨15276036589868034390708317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40736097572981425041888845 15276036589868034390708317)
              ·
                refine ⟨5728513721200512896515619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15276036589868034390708317 5728513721200512896515619)
                ·
                  refine ⟨8592770581800769344773429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728513721200512896515619 8592770581800769344773429)
                  ·
                    refine ⟨805572242043822126072509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8592770581800769344773429 805572242043822126072509)
                    ·
                      rfl

theorem cell23_4706539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 5].length) (baseStart_4706539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706539 prefixEnd_4706539 := by exact prefixLift 4706539
  have htrace : WordTrace (prefixWord ++ tailWord_4706539) baseStart_4706539 baseEnd_4706539 := by
    simpa [prefixWord, tailWord_4706539, baseEnd_4706539] using wordTrace_append hprefix tailTrace_4706539
  have hstable : (prefixWord ++ tailWord_4706539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706539).length < 2 ^ (prefixWord ++ tailWord_4706539).sum := by decide
  have hdescent : baseEnd_4706539 < baseStart_4706539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706552 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 3, 6]
def baseStart_4706552 : Nat := 118140960795 + 4706552 * 2 ^ 59
def prefixEnd_4706552 : Nat := 4983230072969 + 3 ^ 40 * 4706552 * 2
def baseEnd_4706552 : Nat := 805574467126658275784989

theorem tailTrace_4706552 : CollatzResearch.WordTrace tailWord_4706552 prefixEnd_4706552 805574467126658275784989 := by
  unfold tailWord_4706552
  simp only [CollatzResearch.WordTrace]
  refine ⟨85831027022486696965860955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114441369363315595954481273 85831027022486696965860955)
  ·
    refine ⟨128746540533730045448791433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85831027022486696965860955 128746540533730045448791433)
    ·
      refine ⟨96559905400297534086593575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128746540533730045448791433 96559905400297534086593575)
      ·
        refine ⟨144839858100446301129890363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96559905400297534086593575 144839858100446301129890363)
        ·
          refine ⟨217259787150669451694835545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144839858100446301129890363 217259787150669451694835545)
          ·
            refine ⟨162944840363002088771126659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217259787150669451694835545 162944840363002088771126659)
            ·
              refine ⟨244417260544503133156689989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162944840363002088771126659 244417260544503133156689989)
              ·
                refine ⟨45828236352094337466879373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244417260544503133156689989 45828236352094337466879373)
                ·
                  refine ⟨17185588632035376550079765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45828236352094337466879373 17185588632035376550079765)
                  ·
                    refine ⟨805574467126658275784989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17185588632035376550079765 805574467126658275784989)
                    ·
                      rfl

theorem cell23_4706552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_4706552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706552 prefixEnd_4706552 := by exact prefixLift 4706552
  have htrace : WordTrace (prefixWord ++ tailWord_4706552) baseStart_4706552 baseEnd_4706552 := by
    simpa [prefixWord, tailWord_4706552, baseEnd_4706552] using wordTrace_append hprefix tailTrace_4706552
  have hstable : (prefixWord ++ tailWord_4706552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706552).length < 2 ^ (prefixWord ++ tailWord_4706552).sum := by decide
  have hdescent : baseEnd_4706552 < baseStart_4706552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706569 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 1, 6]
def baseStart_4706569 : Nat := 118140960795 + 4706569 * 2 ^ 59
def prefixEnd_4706569 : Nat := 4983230072969 + 3 ^ 40 * 4706569 * 2
def baseEnd_4706569 : Nat := 805577376850367086947463

theorem tailTrace_4706569 : CollatzResearch.WordTrace tailWord_4706569 prefixEnd_4706569 805577376850367086947463 := by
  unfold tailWord_4706569
  simp only [CollatzResearch.WordTrace]
  refine ⟨171662674085911805835090761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114441782723941203890060507 171662674085911805835090761)
  ·
    refine ⟨128747005564433854376318071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171662674085911805835090761 128747005564433854376318071)
    ·
      refine ⟨193120508346650781564477107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128747005564433854376318071 193120508346650781564477107)
      ·
        refine ⟨289680762519976172346715661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193120508346650781564477107 289680762519976172346715661)
        ·
          refine ⟨108630285944991064630018373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289680762519976172346715661 108630285944991064630018373)
          ·
            refine ⟨20368178614685824618128445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108630285944991064630018373 20368178614685824618128445)
            ·
              refine ⟨7638066980507184231798167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20368178614685824618128445 7638066980507184231798167)
              ·
                refine ⟨11457100470760776347697251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638066980507184231798167 11457100470760776347697251)
                ·
                  refine ⟨17185650706141164521545877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11457100470760776347697251 17185650706141164521545877)
                  ·
                    refine ⟨805577376850367086947463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17185650706141164521545877 805577376850367086947463)
                    ·
                      rfl

theorem cell23_4706569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_4706569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706569 prefixEnd_4706569 := by exact prefixLift 4706569
  have htrace : WordTrace (prefixWord ++ tailWord_4706569) baseStart_4706569 baseEnd_4706569 := by
    simpa [prefixWord, tailWord_4706569, baseEnd_4706569] using wordTrace_append hprefix tailTrace_4706569
  have hstable : (prefixWord ++ tailWord_4706569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706569).length < 2 ^ (prefixWord ++ tailWord_4706569).sum := by decide
  have hdescent : baseEnd_4706569 < baseStart_4706569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706579 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 3]
def baseStart_4706579 : Nat := 118140960795 + 4706579 * 2 ^ 59
def prefixEnd_4706579 : Nat := 4983230072969 + 3 ^ 40 * 4706579 * 2
def baseEnd_4706579 : Nat := 2416737265357646221717343

theorem tailTrace_4706579 : CollatzResearch.WordTrace tailWord_4706579 prefixEnd_4706579 2416737265357646221717343 := by
  unfold tailWord_4706579
  simp only [CollatzResearch.WordTrace]
  refine ⟨171663038815875577542954791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114442025877250385028636527 171663038815875577542954791)
  ·
    refine ⟨257494558223813366314432187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171663038815875577542954791 257494558223813366314432187)
    ·
      refine ⟨386241837335720049471648281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257494558223813366314432187 386241837335720049471648281)
      ·
        refine ⟨289681378001790037103736211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386241837335720049471648281 289681378001790037103736211)
        ·
          refine ⟨434522067002685055655604317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289681378001790037103736211 434522067002685055655604317)
          ·
            refine ⟨162945775126006895870851619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434522067002685055655604317 162945775126006895870851619)
            ·
              refine ⟨244418662689010343806277429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162945775126006895870851619 244418662689010343806277429)
              ·
                refine ⟨22914249627094719731838509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244418662689010343806277429 22914249627094719731838509)
                ·
                  refine ⟨8592843610160519899439441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22914249627094719731838509 8592843610160519899439441)
                  ·
                    refine ⟨6444632707620389924579581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8592843610160519899439441 6444632707620389924579581)
                    ·
                      refine ⟨2416737265357646221717343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6444632707620389924579581 2416737265357646221717343)
                      ·
                        rfl

theorem cell23_4706579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_4706579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706579 prefixEnd_4706579 := by exact prefixLift 4706579
  have htrace : WordTrace (prefixWord ++ tailWord_4706579) baseStart_4706579 baseEnd_4706579 := by
    simpa [prefixWord, tailWord_4706579, baseEnd_4706579] using wordTrace_append hprefix tailTrace_4706579
  have hstable : (prefixWord ++ tailWord_4706579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706579).length < 2 ^ (prefixWord ++ tailWord_4706579).sum := by decide
  have hdescent : baseEnd_4706579 < baseStart_4706579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706596 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_4706596 : Nat := 118140960795 + 4706596 * 2 ^ 59
def prefixEnd_4706596 : Nat := 4983230072969 + 3 ^ 40 * 4706596 * 2
def baseEnd_4706596 : Nat := 2416745994528772655204765

theorem tailTrace_4706596 : CollatzResearch.WordTrace tailWord_4706596 prefixEnd_4706596 2416745994528772655204765 := by
  unfold tailWord_4706596
  simp only [CollatzResearch.WordTrace]
  refine ⟨85831829428406994723161821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114442439237875992964215761 85831829428406994723161821)
  ·
    refine ⟨32186936035652623021185683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85831829428406994723161821 32186936035652623021185683)
    ·
      refine ⟨48280404053478934531778525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32186936035652623021185683 48280404053478934531778525)
      ·
        refine ⟨18105151520054600449416947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48280404053478934531778525 18105151520054600449416947)
        ·
          refine ⟨27157727280081900674125421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18105151520054600449416947 27157727280081900674125421)
          ·
            refine ⟨10184147730030712752797033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27157727280081900674125421 10184147730030712752797033)
            ·
              refine ⟨7638110797523034564597775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10184147730030712752797033 7638110797523034564597775)
              ·
                refine ⟨11457166196284551846896663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638110797523034564597775 11457166196284551846896663)
                ·
                  refine ⟨17185749294426827770344995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11457166196284551846896663 17185749294426827770344995)
                  ·
                    refine ⟨25778623941640241655517493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17185749294426827770344995 25778623941640241655517493)
                    ·
                      refine ⟨2416745994528772655204765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25778623941640241655517493 2416745994528772655204765)
                      ·
                        rfl

theorem cell23_4706596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_4706596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706596 prefixEnd_4706596 := by exact prefixLift 4706596
  have htrace : WordTrace (prefixWord ++ tailWord_4706596) baseStart_4706596 baseEnd_4706596 := by
    simpa [prefixWord, tailWord_4706596, baseEnd_4706596] using wordTrace_append hprefix tailTrace_4706596
  have hstable : (prefixWord ++ tailWord_4706596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706596).length < 2 ^ (prefixWord ++ tailWord_4706596).sum := by decide
  have hdescent : baseEnd_4706596 < baseStart_4706596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706659 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 2, 6]
def baseStart_4706659 : Nat := 118140960795 + 4706659 * 2 ^ 59
def prefixEnd_4706659 : Nat := 4983230072969 + 3 ^ 40 * 4706659 * 2
def baseEnd_4706659 : Nat := 805592781270001969572325

theorem tailTrace_4706659 : CollatzResearch.WordTrace tailWord_4706659 prefixEnd_4706659 805592781270001969572325 := by
  unfold tailWord_4706659
  simp only [CollatzResearch.WordTrace]
  refine ⟨171665956655585751205867031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114443971103723834137244687 171665956655585751205867031)
  ·
    refine ⟨257498934983378626808800547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171665956655585751205867031 257498934983378626808800547)
    ·
      refine ⟨386248402475067940213200821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257498934983378626808800547 386248402475067940213200821)
      ·
        refine ⟨36210787732037619394987577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 386248402475067940213200821 36210787732037619394987577)
        ·
          refine ⟨27158090799028214546240683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36210787732037619394987577 27158090799028214546240683)
          ·
            refine ⟨40737136198542321819361025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27158090799028214546240683 40737136198542321819361025)
            ·
              refine ⟨30552852148906741364520769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40737136198542321819361025 30552852148906741364520769)
              ·
                refine ⟨22914639111680056023390577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30552852148906741364520769 22914639111680056023390577)
                ·
                  refine ⟨17185979333760042017542933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22914639111680056023390577 17185979333760042017542933)
                  ·
                    refine ⟨805592781270001969572325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17185979333760042017542933 805592781270001969572325)
                    ·
                      rfl

theorem cell23_4706659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 6].length) (baseStart_4706659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706659 prefixEnd_4706659 := by exact prefixLift 4706659
  have htrace : WordTrace (prefixWord ++ tailWord_4706659) baseStart_4706659 baseEnd_4706659 := by
    simpa [prefixWord, tailWord_4706659, baseEnd_4706659] using wordTrace_append hprefix tailTrace_4706659
  have hstable : (prefixWord ++ tailWord_4706659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706659).length < 2 ^ (prefixWord ++ tailWord_4706659).sum := by decide
  have hdescent : baseEnd_4706659 < baseStart_4706659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706666 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4706666 : Nat := 118140960795 + 4706666 * 2 ^ 59
def prefixEnd_4706666 : Nat := 4983230072969 + 3 ^ 40 * 4706666 * 2
def baseEnd_4706666 : Nat := 2416781938174587381329443

theorem tailTrace_4706666 : CollatzResearch.WordTrace tailWord_4706666 prefixEnd_4706666 2416781938174587381329443 := by
  unfold tailWord_4706666
  simp only [CollatzResearch.WordTrace]
  refine ⟨42916552991640097850342963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114444141311040260934247901 42916552991640097850342963)
  ·
    refine ⟨64374829487460146775514445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42916552991640097850342963 64374829487460146775514445)
    ·
      refine ⟨24140561057797555040817917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64374829487460146775514445 24140561057797555040817917)
      ·
        refine ⟨9052710396674083140306719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24140561057797555040817917 9052710396674083140306719)
        ·
          refine ⟨13579065595011124710460079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9052710396674083140306719 13579065595011124710460079)
          ·
            refine ⟨20368598392516687065690119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13579065595011124710460079 20368598392516687065690119)
            ·
              refine ⟨30552897588775030598535179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20368598392516687065690119 30552897588775030598535179)
              ·
                refine ⟨45829346383162545897802769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30552897588775030598535179 45829346383162545897802769)
                ·
                  refine ⟨34372009787371909423352077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45829346383162545897802769 34372009787371909423352077)
                  ·
                    refine ⟨12889503670264466033757029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34372009787371909423352077 12889503670264466033757029)
                    ·
                      refine ⟨2416781938174587381329443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12889503670264466033757029 2416781938174587381329443)
                      ·
                        rfl

theorem cell23_4706666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4706666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706666 prefixEnd_4706666 := by exact prefixLift 4706666
  have htrace : WordTrace (prefixWord ++ tailWord_4706666) baseStart_4706666 baseEnd_4706666 := by
    simpa [prefixWord, tailWord_4706666, baseEnd_4706666] using wordTrace_append hprefix tailTrace_4706666
  have hstable : (prefixWord ++ tailWord_4706666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706666).length < 2 ^ (prefixWord ++ tailWord_4706666).sum := by decide
  have hdescent : baseEnd_4706666 < baseStart_4706666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706683 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 1, 4, 2]
def baseStart_4706683 : Nat := 118140960795 + 4706683 * 2 ^ 59
def prefixEnd_4706683 : Nat := 4983230072969 + 3 ^ 40 * 4706683 * 2
def baseEnd_4706683 : Nat := 2416790667345713814816865

theorem tailTrace_4706683 : CollatzResearch.WordTrace tailWord_4706683 prefixEnd_4706683 2416790667345713814816865 := by
  unfold tailWord_4706683
  simp only [CollatzResearch.WordTrace]
  refine ⟨171666832007498803304740703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114444554671665868869827135 171666832007498803304740703)
  ·
    refine ⟨257500248011248204957111055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171666832007498803304740703 257500248011248204957111055)
    ·
      refine ⟨386250372016872307435666583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257500248011248204957111055 386250372016872307435666583)
      ·
        refine ⟨579375558025308461153499875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386250372016872307435666583 579375558025308461153499875)
        ·
          refine ⟨869063337037962691730249813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579375558025308461153499875 869063337037962691730249813)
          ·
            refine ⟨10184335980913625293713865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 869063337037962691730249813 10184335980913625293713865)
            ·
              refine ⟨7638251985685218970285399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10184335980913625293713865 7638251985685218970285399)
              ·
                refine ⟨11457377978527828455428099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638251985685218970285399 11457377978527828455428099)
                ·
                  refine ⟨17186066967791742683142149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11457377978527828455428099 17186066967791742683142149)
                  ·
                    refine ⟨3222387556460951753089153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17186066967791742683142149 3222387556460951753089153)
                    ·
                      refine ⟨2416790667345713814816865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222387556460951753089153 2416790667345713814816865)
                      ·
                        rfl

theorem cell23_4706683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4, 2].length) (baseStart_4706683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706683 prefixEnd_4706683 := by exact prefixLift 4706683
  have htrace : WordTrace (prefixWord ++ tailWord_4706683) baseStart_4706683 baseEnd_4706683 := by
    simpa [prefixWord, tailWord_4706683, baseEnd_4706683] using wordTrace_append hprefix tailTrace_4706683
  have hstable : (prefixWord ++ tailWord_4706683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706683).length < 2 ^ (prefixWord ++ tailWord_4706683).sum := by decide
  have hdescent : baseEnd_4706683 < baseStart_4706683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706729 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_4706729 : Nat := 118140960795 + 4706729 * 2 ^ 59
def prefixEnd_4706729 : Nat := 4983230072969 + 3 ^ 40 * 4706729 * 2
def baseEnd_4706729 : Nat := 2416814287455820634841653

theorem tailTrace_4706729 : CollatzResearch.WordTrace tailWord_4706729 prefixEnd_4706729 2416814287455820634841653 := by
  unfold tailWord_4706729
  simp only [CollatzResearch.WordTrace]
  refine ⟨171668509765332153160915241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114445673176888102107276827 171668509765332153160915241)
  ·
    refine ⟨128751382323999114870686431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171668509765332153160915241 128751382323999114870686431)
    ·
      refine ⟨193127073485998672306029647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128751382323999114870686431 193127073485998672306029647)
      ·
        refine ⟨289690610228998008459044471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193127073485998672306029647 289690610228998008459044471)
        ·
          refine ⟨434535915343497012688566707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289690610228998008459044471 434535915343497012688566707)
          ·
            refine ⟨651803873015245519032850061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434535915343497012688566707 651803873015245519032850061)
            ·
              refine ⟨244426452380717069637318773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 651803873015245519032850061 244426452380717069637318773)
              ·
                refine ⟨22914979910692225278498635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244426452380717069637318773 22914979910692225278498635)
                ·
                  refine ⟨34372469866038337917747953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22914979910692225278498635 34372469866038337917747953)
                  ·
                    refine ⟨25779352399528753438310965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34372469866038337917747953 25779352399528753438310965)
                    ·
                      refine ⟨2416814287455820634841653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25779352399528753438310965 2416814287455820634841653)
                      ·
                        rfl

theorem cell23_4706729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_4706729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706729 prefixEnd_4706729 := by exact prefixLift 4706729
  have htrace : WordTrace (prefixWord ++ tailWord_4706729) baseStart_4706729 baseEnd_4706729 := by
    simpa [prefixWord, tailWord_4706729, baseEnd_4706729] using wordTrace_append hprefix tailTrace_4706729
  have hstable : (prefixWord ++ tailWord_4706729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706729).length < 2 ^ (prefixWord ++ tailWord_4706729).sum := by decide
  have hdescent : baseEnd_4706729 < baseStart_4706729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706769 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_4706769 : Nat := 118140960795 + 4706769 * 2 ^ 59
def prefixEnd_4706769 : Nat := 4983230072969 + 3 ^ 40 * 4706769 * 2
def baseEnd_4706769 : Nat := 2416834826682000478341469

theorem tailTrace_4706769 : CollatzResearch.WordTrace tailWord_4706769 prefixEnd_4706769 2416834826682000478341469 := by
  unfold tailWord_4706769
  simp only [CollatzResearch.WordTrace]
  refine ⟨171669968685187239992371361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114446645790124826661580907 171669968685187239992371361)
  ·
    refine ⟨128752476513890429994278521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171669968685187239992371361 128752476513890429994278521)
    ·
      refine ⟨96564357385417822495708891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128752476513890429994278521 96564357385417822495708891)
      ·
        refine ⟨144846536078126733743563337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96564357385417822495708891 144846536078126733743563337)
        ·
          refine ⟨108634902058595050307672503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144846536078126733743563337 108634902058595050307672503)
          ·
            refine ⟨162952353087892575461508755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108634902058595050307672503 162952353087892575461508755)
            ·
              refine ⟨244428529631838863192263133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162952353087892575461508755 244428529631838863192263133)
              ·
                refine ⟨91660698611939573697098675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244428529631838863192263133 91660698611939573697098675)
                ·
                  refine ⟨137491047917909360545648013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91660698611939573697098675 137491047917909360545648013)
                  ·
                    refine ⟨51559142969216010204618005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137491047917909360545648013 51559142969216010204618005)
                    ·
                      refine ⟨2416834826682000478341469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51559142969216010204618005 2416834826682000478341469)
                      ·
                        rfl

theorem cell23_4706769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_4706769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706769 prefixEnd_4706769 := by exact prefixLift 4706769
  have htrace : WordTrace (prefixWord ++ tailWord_4706769) baseStart_4706769 baseEnd_4706769 := by
    simpa [prefixWord, tailWord_4706769, baseEnd_4706769] using wordTrace_append hprefix tailTrace_4706769
  have hstable : (prefixWord ++ tailWord_4706769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706769).length < 2 ^ (prefixWord ++ tailWord_4706769).sum := by decide
  have hdescent : baseEnd_4706769 < baseStart_4706769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706770 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_4706770 : Nat := 118140960795 + 4706770 * 2 ^ 59
def prefixEnd_4706770 : Nat := 4983230072969 + 3 ^ 40 * 4706770 * 2
def baseEnd_4706770 : Nat := 805611780054218324809655

theorem tailTrace_4706770 : CollatzResearch.WordTrace tailWord_4706770 prefixEnd_4706770 805611780054218324809655 := by
  unfold tailWord_4706770
  simp only [CollatzResearch.WordTrace]
  refine ⟨42917501289545904290789441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114446670105455744775438509 42917501289545904290789441)
  ·
    refine ⟨32188125967159428218092081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42917501289545904290789441 32188125967159428218092081)
    ·
      refine ⟨24141094475369571163569061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32188125967159428218092081 24141094475369571163569061)
      ·
        refine ⟨4526455214131794593169199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24141094475369571163569061 4526455214131794593169199)
        ·
          refine ⟨6789682821197691889753799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526455214131794593169199 6789682821197691889753799)
          ·
            refine ⟨10184524231796537834630699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789682821197691889753799 10184524231796537834630699)
            ·
              refine ⟨15276786347694806751946049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10184524231796537834630699 15276786347694806751946049)
              ·
                refine ⟨11457589760771105063959537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15276786347694806751946049 11457589760771105063959537)
                ·
                  refine ⟨8593192320578328797969653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11457589760771105063959537 8593192320578328797969653)
                  ·
                    refine ⟨805611780054218324809655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8593192320578328797969653 805611780054218324809655)
                    ·
                      rfl

theorem cell23_4706770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_4706770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706770 prefixEnd_4706770 := by exact prefixLift 4706770
  have htrace : WordTrace (prefixWord ++ tailWord_4706770) baseStart_4706770 baseEnd_4706770 := by
    simpa [prefixWord, tailWord_4706770, baseEnd_4706770] using wordTrace_append hprefix tailTrace_4706770
  have hstable : (prefixWord ++ tailWord_4706770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706770).length < 2 ^ (prefixWord ++ tailWord_4706770).sum := by decide
  have hdescent : baseEnd_4706770 < baseStart_4706770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706773 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4706773 : Nat := 118140960795 + 4706773 * 2 ^ 59
def prefixEnd_4706773 : Nat := 4983230072969 + 3 ^ 40 * 4706773 * 2
def baseEnd_4706773 : Nat := 2416836880604618462691451

theorem tailTrace_4706773 : CollatzResearch.WordTrace tailWord_4706773 prefixEnd_4706773 2416836880604618462691451 := by
  unfold tailWord_4706773
  simp only [CollatzResearch.WordTrace]
  refine ⟨171670114577172748675516973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114446743051448499117011315 171670114577172748675516973)
  ·
    refine ⟨64376292966439780753318865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171670114577172748675516973 64376292966439780753318865)
    ·
      refine ⟨48282219724829835564989149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64376292966439780753318865 48282219724829835564989149)
      ·
        refine ⟨18105832396811188336870931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48282219724829835564989149 18105832396811188336870931)
        ·
          refine ⟨27158748595216782505306397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18105832396811188336870931 27158748595216782505306397)
          ·
            refine ⟨10184530723206293439489899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27158748595216782505306397 10184530723206293439489899)
            ·
              refine ⟨15276796084809440159234849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10184530723206293439489899 15276796084809440159234849)
              ·
                refine ⟨11457597063607080119426137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15276796084809440159234849 11457597063607080119426137)
                ·
                  refine ⟨8593197797705310089569603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11457597063607080119426137 8593197797705310089569603)
                  ·
                    refine ⟨12889796696557965134354405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8593197797705310089569603 12889796696557965134354405)
                    ·
                      refine ⟨2416836880604618462691451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12889796696557965134354405 2416836880604618462691451)
                      ·
                        rfl

theorem cell23_4706773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4706773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706773 prefixEnd_4706773 := by exact prefixLift 4706773
  have htrace : WordTrace (prefixWord ++ tailWord_4706773) baseStart_4706773 baseEnd_4706773 := by
    simpa [prefixWord, tailWord_4706773, baseEnd_4706773] using wordTrace_append hprefix tailTrace_4706773
  have hstable : (prefixWord ++ tailWord_4706773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706773).length < 2 ^ (prefixWord ++ tailWord_4706773).sum := by decide
  have hdescent : baseEnd_4706773 < baseStart_4706773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706783 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 3, 4]
def baseStart_4706783 : Nat := 118140960795 + 4706783 * 2 ^ 59
def prefixEnd_4706783 : Nat := 4983230072969 + 3 ^ 40 * 4706783 * 2
def baseEnd_4706783 : Nat := 805614005137054474522135

theorem tailTrace_4706783 : CollatzResearch.WordTrace tailWord_4706783 prefixEnd_4706783 805614005137054474522135 := by
  unfold tailWord_4706783
  simp only [CollatzResearch.WordTrace]
  refine ⟨171670479307136520383381003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114446986204757680255587335 171670479307136520383381003)
  ·
    refine ⟨257505718960704780575071505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171670479307136520383381003 257505718960704780575071505)
    ·
      refine ⟨193129289220528585431303629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257505718960704780575071505 193129289220528585431303629)
      ·
        refine ⟨72423483457698219536738861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193129289220528585431303629 72423483457698219536738861)
        ·
          refine ⟨27158806296636832326277073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72423483457698219536738861 27158806296636832326277073)
          ·
            refine ⟨20369104722477624244707805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27158806296636832326277073 20369104722477624244707805)
            ·
              refine ⟨7638414270929109091765427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20369104722477624244707805 7638414270929109091765427)
              ·
                refine ⟨11457621406393663637648141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638414270929109091765427 11457621406393663637648141)
                ·
                  refine ⟨4296608027397623864118053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11457621406393663637648141 4296608027397623864118053)
                  ·
                    refine ⟨805614005137054474522135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296608027397623864118053 805614005137054474522135)
                    ·
                      rfl

theorem cell23_4706783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_4706783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706783 prefixEnd_4706783 := by exact prefixLift 4706783
  have htrace : WordTrace (prefixWord ++ tailWord_4706783) baseStart_4706783 baseEnd_4706783 := by
    simpa [prefixWord, tailWord_4706783, baseEnd_4706783] using wordTrace_append hprefix tailTrace_4706783
  have hstable : (prefixWord ++ tailWord_4706783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706783).length < 2 ^ (prefixWord ++ tailWord_4706783).sum := by decide
  have hdescent : baseEnd_4706783 < baseStart_4706783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706796 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 6]
def baseStart_4706796 : Nat := 118140960795 + 4706796 * 2 ^ 59
def prefixEnd_4706796 : Nat := 4983230072969 + 3 ^ 40 * 4706796 * 2
def baseEnd_4706796 : Nat := 268538743406630208078205

theorem tailTrace_4706796 : CollatzResearch.WordTrace tailWord_4706796 prefixEnd_4706796 268538743406630208078205 := by
  unfold tailWord_4706796
  simp only [CollatzResearch.WordTrace]
  refine ⟨85835476728044711801802121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114447302304059615735736161 85835476728044711801802121)
  ·
    refine ⟨64376607546033533851351591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85835476728044711801802121 64376607546033533851351591)
    ·
      refine ⟨96564911319050300777027387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64376607546033533851351591 96564911319050300777027387)
      ·
        refine ⟨144847366978575451165541081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96564911319050300777027387 144847366978575451165541081)
        ·
          refine ⟨108635525233931588374155811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144847366978575451165541081 108635525233931588374155811)
          ·
            refine ⟨162953287850897382561233717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108635525233931588374155811 162953287850897382561233717)
            ·
              refine ⟨15276870736021629615115661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162953287850897382561233717 15276870736021629615115661)
              ·
                refine ⟨5728826526008111105668373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15276870736021629615115661 5728826526008111105668373)
                ·
                  refine ⟨268538743406630208078205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5728826526008111105668373 268538743406630208078205)
                  ·
                    rfl

theorem cell23_4706796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_4706796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706796 prefixEnd_4706796 := by exact prefixLift 4706796
  have htrace : WordTrace (prefixWord ++ tailWord_4706796) baseStart_4706796 baseEnd_4706796 := by
    simpa [prefixWord, tailWord_4706796, baseEnd_4706796] using wordTrace_append hprefix tailTrace_4706796
  have hstable : (prefixWord ++ tailWord_4706796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706796).length < 2 ^ (prefixWord ++ tailWord_4706796).sum := by decide
  have hdescent : baseEnd_4706796 < baseStart_4706796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706833 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 4, 3, 2]
def baseStart_4706833 : Nat := 118140960795 + 4706833 * 2 ^ 59
def prefixEnd_4706833 : Nat := 4983230072969 + 3 ^ 40 * 4706833 * 2
def baseEnd_4706833 : Nat := 2416867689443888227941175

theorem tailTrace_4706833 : CollatzResearch.WordTrace tailWord_4706833 prefixEnd_4706833 2416867689443888227941175 := by
  unfold tailWord_4706833
  simp only [CollatzResearch.WordTrace]
  refine ⟨171672302956955378922701153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114448201971303585948467435 171672302956955378922701153)
  ·
    refine ⟨128754227217716534192025865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171672302956955378922701153 128754227217716534192025865)
    ·
      refine ⟨96565670413287400644019399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128754227217716534192025865 96565670413287400644019399)
      ·
        refine ⟨144848505619931100966029099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96565670413287400644019399 144848505619931100966029099)
        ·
          refine ⟨217272758429896651449043649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144848505619931100966029099 217272758429896651449043649)
          ·
            refine ⟨162954568822422488586782737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217272758429896651449043649 162954568822422488586782737)
            ·
              refine ⟨122215926616816866440087053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162954568822422488586782737 122215926616816866440087053)
              ·
                refine ⟨45830972481306324915032645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122215926616816866440087053 45830972481306324915032645)
                ·
                  refine ⟨8593307340244935921568621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45830972481306324915032645 8593307340244935921568621)
                  ·
                    refine ⟨3222490252591850970588233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8593307340244935921568621 3222490252591850970588233)
                    ·
                      refine ⟨2416867689443888227941175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222490252591850970588233 2416867689443888227941175)
                      ·
                        rfl

theorem cell23_4706833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_4706833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706833 prefixEnd_4706833 := by exact prefixLift 4706833
  have htrace : WordTrace (prefixWord ++ tailWord_4706833) baseStart_4706833 baseEnd_4706833 := by
    simpa [prefixWord, tailWord_4706833, baseEnd_4706833] using wordTrace_append hprefix tailTrace_4706833
  have hstable : (prefixWord ++ tailWord_4706833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706833).length < 2 ^ (prefixWord ++ tailWord_4706833).sum := by decide
  have hdescent : baseEnd_4706833 < baseStart_4706833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706861 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4706861 : Nat := 118140960795 + 4706861 * 2 ^ 59
def prefixEnd_4706861 : Nat := 4983230072969 + 3 ^ 40 * 4706861 * 2
def baseEnd_4706861 : Nat := 2416882066902214118391047

theorem tailTrace_4706861 : CollatzResearch.WordTrace tailWord_4706861 prefixEnd_4706861 2416882066902214118391047 := by
  unfold tailWord_4706861
  simp only [CollatzResearch.WordTrace]
  refine ⟨171673324200853939704720437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114448882800569293136480291 171673324200853939704720437)
  ·
    refine ⟨16094374143830056847317541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171673324200853939704720437 16094374143830056847317541)
    ·
      refine ⟨3017695151968135658872039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16094374143830056847317541 3017695151968135658872039)
      ·
        refine ⟨4526542727952203488308059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017695151968135658872039 4526542727952203488308059)
        ·
          refine ⟨6789814091928305232462089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526542727952203488308059 6789814091928305232462089)
          ·
            refine ⟨5092360568946228924346567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6789814091928305232462089 5092360568946228924346567)
            ·
              refine ⟨7638540853419343386519851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5092360568946228924346567 7638540853419343386519851)
              ·
                refine ⟨11457811280129015079779777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638540853419343386519851 11457811280129015079779777)
                ·
                  refine ⟨8593358460096761309834833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11457811280129015079779777 8593358460096761309834833)
                  ·
                    refine ⟨6445018845072570982376125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8593358460096761309834833 6445018845072570982376125)
                    ·
                      refine ⟨2416882066902214118391047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445018845072570982376125 2416882066902214118391047)
                      ·
                        rfl

theorem cell23_4706861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4706861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706861 prefixEnd_4706861 := by exact prefixLift 4706861
  have htrace : WordTrace (prefixWord ++ tailWord_4706861) baseStart_4706861 baseEnd_4706861 := by
    simpa [prefixWord, tailWord_4706861, baseEnd_4706861] using wordTrace_append hprefix tailTrace_4706861
  have hstable : (prefixWord ++ tailWord_4706861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706861).length < 2 ^ (prefixWord ++ tailWord_4706861).sum := by decide
  have hdescent : baseEnd_4706861 < baseStart_4706861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706873 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 4, 4]
def baseStart_4706873 : Nat := 118140960795 + 4706873 * 2 ^ 59
def prefixEnd_4706873 : Nat := 4983230072969 + 3 ^ 40 * 4706873 * 2
def baseEnd_4706873 : Nat := 805629409556689357146997

theorem tailTrace_4706873 : CollatzResearch.WordTrace tailWord_4706873 prefixEnd_4706873 805629409556689357146997 := by
  unfold tailWord_4706873
  simp only [CollatzResearch.WordTrace]
  refine ⟨171673761876810465754157273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114449174584540310502771515 171673761876810465754157273)
  ·
    refine ⟨128755321407607849315617955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171673761876810465754157273 128755321407607849315617955)
    ·
      refine ⟨193132982111411773973426933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128755321407607849315617955 193132982111411773973426933)
      ·
        refine ⟨18106217072944853810008775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193132982111411773973426933 18106217072944853810008775)
        ·
          refine ⟨27159325609417280715013163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18106217072944853810008775 27159325609417280715013163)
          ·
            refine ⟨40738988414125921072519745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27159325609417280715013163 40738988414125921072519745)
            ·
              refine ⟨30554241310594440804389809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40738988414125921072519745 30554241310594440804389809)
              ·
                refine ⟨22915680982945830603292357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30554241310594440804389809 22915680982945830603292357)
                ·
                  refine ⟨4296690184302343238117317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22915680982945830603292357 4296690184302343238117317)
                  ·
                    refine ⟨805629409556689357146997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296690184302343238117317 805629409556689357146997)
                    ·
                      rfl

theorem cell23_4706873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_4706873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706873 prefixEnd_4706873 := by exact prefixLift 4706873
  have htrace : WordTrace (prefixWord ++ tailWord_4706873) baseStart_4706873 baseEnd_4706873 := by
    simpa [prefixWord, tailWord_4706873, baseEnd_4706873] using wordTrace_append hprefix tailTrace_4706873
  have hstable : (prefixWord ++ tailWord_4706873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706873).length < 2 ^ (prefixWord ++ tailWord_4706873).sum := by decide
  have hdescent : baseEnd_4706873 < baseStart_4706873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706877 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_4706877 : Nat := 118140960795 + 4706877 * 2 ^ 59
def prefixEnd_4706877 : Nat := 4983230072969 + 3 ^ 40 * 4706877 * 2
def baseEnd_4706877 : Nat := 805630094197562018596991

theorem tailTrace_4706877 : CollatzResearch.WordTrace tailWord_4706877 prefixEnd_4706877 805630094197562018596991 := by
  unfold tailWord_4706877
  simp only [CollatzResearch.WordTrace]
  refine ⟨171673907768795974437302885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114449271845863982958201923 171673907768795974437302885)
  ·
    refine ⟨32188857706649245206994291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171673907768795974437302885 32188857706649245206994291)
    ·
      refine ⟨48283286559973867810491437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32188857706649245206994291 48283286559973867810491437)
      ·
        refine ⟨18106232459990200428934289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48283286559973867810491437 18106232459990200428934289)
        ·
          refine ⟨13579674344992650321700717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18106232459990200428934289 13579674344992650321700717)
          ·
            refine ⟨5092377879372243870637769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13579674344992650321700717 5092377879372243870637769)
            ·
              refine ⟨3819283409529182902978327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5092377879372243870637769 3819283409529182902978327)
              ·
                refine ⟨5728925114293774354467491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819283409529182902978327 5728925114293774354467491)
                ·
                  refine ⟨8593387671440661531701237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728925114293774354467491 8593387671440661531701237)
                  ·
                    refine ⟨805630094197562018596991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8593387671440661531701237 805630094197562018596991)
                    ·
                      rfl

theorem cell23_4706877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_4706877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706877 prefixEnd_4706877 := by exact prefixLift 4706877
  have htrace : WordTrace (prefixWord ++ tailWord_4706877) baseStart_4706877 baseEnd_4706877 := by
    simpa [prefixWord, tailWord_4706877, baseEnd_4706877] using wordTrace_append hprefix tailTrace_4706877
  have hstable : (prefixWord ++ tailWord_4706877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706877).length < 2 ^ (prefixWord ++ tailWord_4706877).sum := by decide
  have hdescent : baseEnd_4706877 < baseStart_4706877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706880 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 1, 1, 4]
def baseStart_4706880 : Nat := 118140960795 + 4706880 * 2 ^ 59
def prefixEnd_4706880 : Nat := 4983230072969 + 3 ^ 40 * 4706880 * 2
def baseEnd_4706880 : Nat := 2416891823034649544053459

theorem tailTrace_4706880 : CollatzResearch.WordTrace tailWord_4706880 prefixEnd_4706880 2416891823034649544053459 := by
  unfold tailWord_4706880
  simp only [CollatzResearch.WordTrace]
  refine ⟨85837008593892552974831047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114449344791856737299774729 85837008593892552974831047)
  ·
    refine ⟨128755512890838829462246571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85837008593892552974831047 128755512890838829462246571)
    ·
      refine ⟨193133269336258244193369857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128755512890838829462246571 193133269336258244193369857)
      ·
        refine ⟨144849952002193683145027393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193133269336258244193369857 144849952002193683145027393)
        ·
          refine ⟨108637464001645262358770545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144849952002193683145027393 108637464001645262358770545)
          ·
            refine ⟨81478098001233946769077909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108637464001645262358770545 81478098001233946769077909)
            ·
              refine ⟨3819285843807841254800527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81478098001233946769077909 3819285843807841254800527)
              ·
                refine ⟨5728928765711761882200791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819285843807841254800527 5728928765711761882200791)
                ·
                  refine ⟨8593393148567642823301187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728928765711761882200791 8593393148567642823301187)
                  ·
                    refine ⟨12890089722851464234951781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8593393148567642823301187 12890089722851464234951781)
                    ·
                      refine ⟨2416891823034649544053459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12890089722851464234951781 2416891823034649544053459)
                      ·
                        rfl

theorem cell23_4706880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_4706880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706880 prefixEnd_4706880 := by exact prefixLift 4706880
  have htrace : WordTrace (prefixWord ++ tailWord_4706880) baseStart_4706880 baseEnd_4706880 := by
    simpa [prefixWord, tailWord_4706880, baseEnd_4706880] using wordTrace_append hprefix tailTrace_4706880
  have hstable : (prefixWord ++ tailWord_4706880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706880).length < 2 ^ (prefixWord ++ tailWord_4706880).sum := by decide
  have hdescent : baseEnd_4706880 < baseStart_4706880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706890 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_4706890 : Nat := 118140960795 + 4706890 * 2 ^ 59
def prefixEnd_4706890 : Nat := 4983230072969 + 3 ^ 40 * 4706890 * 2
def baseEnd_4706890 : Nat := 805632319280398168309471

theorem tailTrace_4706890 : CollatzResearch.WordTrace tailWord_4706890 prefixEnd_4706890 805632319280398168309471 := by
  unfold tailWord_4706890
  simp only [CollatzResearch.WordTrace]
  refine ⟨42918595479437219414381531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114449587945165918438350749 42918595479437219414381531)
  ·
    refine ⟨64377893219155829121572297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42918595479437219414381531 64377893219155829121572297)
    ·
      refine ⟨48283419914366871841179223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64377893219155829121572297 48283419914366871841179223)
      ·
        refine ⟨72425129871550307761768835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48283419914366871841179223 72425129871550307761768835)
        ·
          refine ⟨108637694807325461642653253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72425129871550307761768835 108637694807325461642653253)
          ·
            refine ⟨20369567776373524057997485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108637694807325461642653253 20369567776373524057997485)
            ·
              refine ⟨7638587916140071521749057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20369567776373524057997485 7638587916140071521749057)
              ·
                refine ⟨5728940937105053641311793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7638587916140071521749057 5728940937105053641311793)
                ·
                  refine ⟨4296705702828790230983845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5728940937105053641311793 4296705702828790230983845)
                  ·
                    refine ⟨805632319280398168309471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296705702828790230983845 805632319280398168309471)
                    ·
                      rfl

theorem cell23_4706890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_4706890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706890 prefixEnd_4706890 := by exact prefixLift 4706890
  have htrace : WordTrace (prefixWord ++ tailWord_4706890) baseStart_4706890 baseEnd_4706890 := by
    simpa [prefixWord, tailWord_4706890, baseEnd_4706890] using wordTrace_append hprefix tailTrace_4706890
  have hstable : (prefixWord ++ tailWord_4706890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706890).length < 2 ^ (prefixWord ++ tailWord_4706890).sum := by decide
  have hdescent : baseEnd_4706890 < baseStart_4706890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706897 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 3, 2, 2]
def baseStart_4706897 : Nat := 118140960795 + 4706897 * 2 ^ 59
def prefixEnd_4706897 : Nat := 4983230072969 + 3 ^ 40 * 4706897 * 2
def baseEnd_4706897 : Nat := 2416900552205775977540881

theorem tailTrace_4706897 : CollatzResearch.WordTrace tailWord_4706897 prefixEnd_4706897 2416900552205775977540881 := by
  unfold tailWord_4706897
  simp only [CollatzResearch.WordTrace]
  refine ⟨171674637228723517853030945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114449758152482345235353963 171674637228723517853030945)
  ·
    refine ⟨128755977921542638389773209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171674637228723517853030945 128755977921542638389773209)
    ·
      refine ⟨96566983441156978792329907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128755977921542638389773209 96566983441156978792329907)
      ·
        refine ⟨144850475161735468188494861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96566983441156978792329907 144850475161735468188494861)
        ·
          refine ⟨54318928185650800570685573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144850475161735468188494861 54318928185650800570685573)
          ·
            refine ⟨10184799034809525107003545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54318928185650800570685573 10184799034809525107003545)
            ·
              refine ⟨7638599276107143830252659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10184799034809525107003545 7638599276107143830252659)
              ·
                refine ⟨11457898914160715745378989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638599276107143830252659 11457898914160715745378989)
                ·
                  refine ⟨4296712092810268404517121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11457898914160715745378989 4296712092810268404517121)
                  ·
                    refine ⟨3222534069607701303387841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4296712092810268404517121 3222534069607701303387841)
                    ·
                      refine ⟨2416900552205775977540881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222534069607701303387841 2416900552205775977540881)
                      ·
                        rfl

theorem cell23_4706897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_4706897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706897 prefixEnd_4706897 := by exact prefixLift 4706897
  have htrace : WordTrace (prefixWord ++ tailWord_4706897) baseStart_4706897 baseEnd_4706897 := by
    simpa [prefixWord, tailWord_4706897, baseEnd_4706897] using wordTrace_append hprefix tailTrace_4706897
  have hstable : (prefixWord ++ tailWord_4706897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706897).length < 2 ^ (prefixWord ++ tailWord_4706897).sum := by decide
  have hdescent : baseEnd_4706897 < baseStart_4706897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706914 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4706914 : Nat := 118140960795 + 4706914 * 2 ^ 59
def prefixEnd_4706914 : Nat := 4983230072969 + 3 ^ 40 * 4706914 * 2
def baseEnd_4706914 : Nat := 2416909281376902411028303

theorem tailTrace_4706914 : CollatzResearch.WordTrace tailWord_4706914 prefixEnd_4706914 2416909281376902411028303 := by
  unfold tailWord_4706914
  simp only [CollatzResearch.WordTrace]
  refine ⟨42918814317415482439099949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114450171513107953170933197 42918814317415482439099949)
  ·
    refine ⟨16094555369030805914662481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42918814317415482439099949 16094555369030805914662481)
    ·
      refine ⟨12070916526773104435996861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16094555369030805914662481 12070916526773104435996861)
      ·
        refine ⟨4526593697539914163498823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12070916526773104435996861 4526593697539914163498823)
        ·
          refine ⟨6789890546309871245248235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526593697539914163498823 6789890546309871245248235)
          ·
            refine ⟨10184835819464806867872353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789890546309871245248235 10184835819464806867872353)
            ·
              refine ⟨7638626864598605150904265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10184835819464806867872353 7638626864598605150904265)
              ·
                refine ⟨5728970148448953863178199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7638626864598605150904265 5728970148448953863178199)
                ·
                  refine ⟨8593455222673430794767299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728970148448953863178199 8593455222673430794767299)
                  ·
                    refine ⟨12890182834010146192150949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8593455222673430794767299 12890182834010146192150949)
                    ·
                      refine ⟨2416909281376902411028303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12890182834010146192150949 2416909281376902411028303)
                      ·
                        rfl

theorem cell23_4706914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4706914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706914 prefixEnd_4706914 := by exact prefixLift 4706914
  have htrace : WordTrace (prefixWord ++ tailWord_4706914) baseStart_4706914 baseEnd_4706914 := by
    simpa [prefixWord, tailWord_4706914, baseEnd_4706914] using wordTrace_append hprefix tailTrace_4706914
  have hstable : (prefixWord ++ tailWord_4706914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706914).length < 2 ^ (prefixWord ++ tailWord_4706914).sum := by decide
  have hdescent : baseEnd_4706914 < baseStart_4706914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706917 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_4706917 : Nat := 118140960795 + 4706917 * 2 ^ 59
def prefixEnd_4706917 : Nat := 4983230072969 + 3 ^ 40 * 4706917 * 2
def baseEnd_4706917 : Nat := 2416910821818865899290789

theorem tailTrace_4706917 : CollatzResearch.WordTrace tailWord_4706917 prefixEnd_4706917 2416910821818865899290789 := by
  unfold tailWord_4706917
  simp only [CollatzResearch.WordTrace]
  refine ⟨171675366688651061268759005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114450244459100707512506003 171675366688651061268759005)
  ·
    refine ⟨64378262508244147975784627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171675366688651061268759005 64378262508244147975784627)
    ·
      refine ⟨96567393762366221963676941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64378262508244147975784627 96567393762366221963676941)
      ·
        refine ⟨36212772660887333236378853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96567393762366221963676941 36212772660887333236378853)
        ·
          refine ⟨6789894873916374981821035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36212772660887333236378853 6789894873916374981821035)
          ·
            refine ⟨10184842310874562472731553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789894873916374981821035 10184842310874562472731553)
            ·
              refine ⟨7638631733155921854548665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10184842310874562472731553 7638631733155921854548665)
              ·
                refine ⟨5728973799866941390911499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7638631733155921854548665 5728973799866941390911499)
                ·
                  refine ⟨8593460699800412086367249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728973799866941390911499 8593460699800412086367249)
                  ·
                    refine ⟨6445095524850309064775437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8593460699800412086367249 6445095524850309064775437)
                    ·
                      refine ⟨2416910821818865899290789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445095524850309064775437 2416910821818865899290789)
                      ·
                        rfl

theorem cell23_4706917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_4706917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706917 prefixEnd_4706917 := by exact prefixLift 4706917
  have htrace : WordTrace (prefixWord ++ tailWord_4706917) baseStart_4706917 baseEnd_4706917 := by
    simpa [prefixWord, tailWord_4706917, baseEnd_4706917] using wordTrace_append hprefix tailTrace_4706917
  have hstable : (prefixWord ++ tailWord_4706917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706917).length < 2 ^ (prefixWord ++ tailWord_4706917).sum := by decide
  have hdescent : baseEnd_4706917 < baseStart_4706917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706964 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4706964 : Nat := 118140960795 + 4706964 * 2 ^ 59
def prefixEnd_4706964 : Nat := 4983230072969 + 3 ^ 40 * 4706964 * 2
def baseEnd_4706964 : Nat := 2416934955409627215403073

theorem tailTrace_4706964 : CollatzResearch.WordTrace tailWord_4706964 prefixEnd_4706964 2416934955409627215403073 := by
  unfold tailWord_4706964
  simp only [CollatzResearch.WordTrace]
  refine ⟨85838540459740394147859973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114451387279653858863813297 85838540459740394147859973)
  ·
    refine ⟨16094726336201323902723745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85838540459740394147859973 16094726336201323902723745)
    ·
      refine ⟨12071044752150992927042809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16094726336201323902723745 12071044752150992927042809)
      ·
        refine ⟨9053283564113244695282107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12071044752150992927042809 9053283564113244695282107)
        ·
          refine ⟨13579925346169867042923161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9053283564113244695282107 13579925346169867042923161)
          ·
            refine ⟨10184944009627400282192371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13579925346169867042923161 10184944009627400282192371)
            ·
              refine ⟨15277416014441100423288557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10184944009627400282192371 15277416014441100423288557)
              ·
                refine ⟨5729031005415412658733209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15277416014441100423288557 5729031005415412658733209)
                ·
                  refine ⟨4296773254061559494049907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5729031005415412658733209 4296773254061559494049907)
                  ·
                    refine ⟨6445159881092339241074861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296773254061559494049907 6445159881092339241074861)
                    ·
                      refine ⟨2416934955409627215403073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445159881092339241074861 2416934955409627215403073)
                      ·
                        rfl

theorem cell23_4706964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4706964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706964 prefixEnd_4706964 := by exact prefixLift 4706964
  have htrace : WordTrace (prefixWord ++ tailWord_4706964) baseStart_4706964 baseEnd_4706964 := by
    simpa [prefixWord, tailWord_4706964, baseEnd_4706964] using wordTrace_append hprefix tailTrace_4706964
  have hstable : (prefixWord ++ tailWord_4706964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706964).length < 2 ^ (prefixWord ++ tailWord_4706964).sum := by decide
  have hdescent : baseEnd_4706964 < baseStart_4706964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4706973 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_4706973 : Nat := 118140960795 + 4706973 * 2 ^ 59
def prefixEnd_4706973 : Nat := 4983230072969 + 3 ^ 40 * 4706973 * 2
def baseEnd_4706973 : Nat := 2416939576735517680190531

theorem tailTrace_4706973 : CollatzResearch.WordTrace tailWord_4706973 prefixEnd_4706973 2416939576735517680190531 := by
  unfold tailWord_4706973
  simp only [CollatzResearch.WordTrace]
  refine ⟨171677409176448182832797573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114451606117632121888531715 171677409176448182832797573)
  ·
    refine ⟨32189514220584034281149545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171677409176448182832797573 32189514220584034281149545)
    ·
      refine ⟨24142135665438025710862159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32189514220584034281149545 24142135665438025710862159)
      ·
        refine ⟨36213203498157038566293239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24142135665438025710862159 36213203498157038566293239)
        ·
          refine ⟨54319805247235557849439859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36213203498157038566293239 54319805247235557849439859)
          ·
            refine ⟨81479707870853336774159789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54319805247235557849439859 81479707870853336774159789)
            ·
              refine ⟨30554890451570001290309921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81479707870853336774159789 30554890451570001290309921)
              ·
                refine ⟨22916167838677500967732441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30554890451570001290309921 22916167838677500967732441)
                ·
                  refine ⟨17187125879008125725799331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22916167838677500967732441 17187125879008125725799331)
                  ·
                    refine ⟨25780688818512188588698997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17187125879008125725799331 25780688818512188588698997)
                    ·
                      refine ⟨2416939576735517680190531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25780688818512188588698997 2416939576735517680190531)
                      ·
                        rfl

theorem cell23_4706973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_4706973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4706973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4706973 prefixEnd_4706973 := by exact prefixLift 4706973
  have htrace : WordTrace (prefixWord ++ tailWord_4706973) baseStart_4706973 baseEnd_4706973 := by
    simpa [prefixWord, tailWord_4706973, baseEnd_4706973] using wordTrace_append hprefix tailTrace_4706973
  have hstable : (prefixWord ++ tailWord_4706973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4706973).length < 2 ^ (prefixWord ++ tailWord_4706973).sum := by decide
  have hdescent : baseEnd_4706973 < baseStart_4706973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4706973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707004 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_4707004 : Nat := 118140960795 + 4707004 * 2 ^ 59
def prefixEnd_4707004 : Nat := 4983230072969 + 3 ^ 40 * 4707004 * 2
def baseEnd_4707004 : Nat := 2416955494635807058902889

theorem tailTrace_4707004 : CollatzResearch.WordTrace tailWord_4707004 prefixEnd_4707004 2416955494635807058902889 := by
  unfold tailWord_4707004
  simp only [CollatzResearch.WordTrace]
  refine ⟨85839269919667937563588033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114452359892890583418117377 85839269919667937563588033)
  ·
    refine ⟨64379452439750953172691025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85839269919667937563588033 64379452439750953172691025)
    ·
      refine ⟨48284589329813214879518269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64379452439750953172691025 48284589329813214879518269)
      ·
        refine ⟨18106720998679955579819351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48284589329813214879518269 18106720998679955579819351)
        ·
          refine ⟨27160081498019933369729027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18106720998679955579819351 27160081498019933369729027)
          ·
            refine ⟨40740122247029900054593541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27160081498019933369729027 40740122247029900054593541)
            ·
              refine ⟨7638772921318106260236289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40740122247029900054593541 7638772921318106260236289)
              ·
                refine ⟨5729079690988579695177217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7638772921318106260236289 5729079690988579695177217)
                ·
                  refine ⟨4296809768241434771382913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5729079690988579695177217 4296809768241434771382913)
                  ·
                    refine ⟨3222607326181076078537185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4296809768241434771382913 3222607326181076078537185)
                    ·
                      refine ⟨2416955494635807058902889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222607326181076078537185 2416955494635807058902889)
                      ·
                        rfl

theorem cell23_4707004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_4707004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707004 prefixEnd_4707004 := by exact prefixLift 4707004
  have htrace : WordTrace (prefixWord ++ tailWord_4707004) baseStart_4707004 baseEnd_4707004 := by
    simpa [prefixWord, tailWord_4707004, baseEnd_4707004] using wordTrace_append hprefix tailTrace_4707004
  have hstable : (prefixWord ++ tailWord_4707004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707004).length < 2 ^ (prefixWord ++ tailWord_4707004).sum := by decide
  have hdescent : baseEnd_4707004 < baseStart_4707004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707014 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4707014 : Nat := 118140960795 + 4707014 * 2 ^ 59
def prefixEnd_4707014 : Nat := 4983230072969 + 3 ^ 40 * 4707014 * 2
def baseEnd_4707014 : Nat := 805653543147450673259281

theorem tailTrace_4707014 : CollatzResearch.WordTrace tailWord_4707014 prefixEnd_4707014 805653543147450673259281 := by
  unfold tailWord_4707014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5364965767790613963595003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114452603046199764556693397 5364965767790613963595003)
  ·
    refine ⟨8047448651685920945392505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5364965767790613963595003 8047448651685920945392505)
    ·
      refine ⟨6035586488764440709044379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8047448651685920945392505 6035586488764440709044379)
      ·
        refine ⟨9053379733146661063566569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035586488764440709044379 9053379733146661063566569)
        ·
          refine ⟨6790034799859995797674927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9053379733146661063566569 6790034799859995797674927)
          ·
            refine ⟨10185052199789993696512391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6790034799859995797674927 10185052199789993696512391)
            ·
              refine ⟨15277578299684990544768587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10185052199789993696512391 15277578299684990544768587)
              ·
                refine ⟨22916367449527485817152881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15277578299684990544768587 22916367449527485817152881)
                ·
                  refine ⟨17187275587145614362864661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22916367449527485817152881 17187275587145614362864661)
                  ·
                    refine ⟨805653543147450673259281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17187275587145614362864661 805653543147450673259281)
                    ·
                      rfl

theorem cell23_4707014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4707014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707014 prefixEnd_4707014 := by exact prefixLift 4707014
  have htrace : WordTrace (prefixWord ++ tailWord_4707014) baseStart_4707014 baseEnd_4707014 := by
    simpa [prefixWord, tailWord_4707014, baseEnd_4707014] using wordTrace_append hprefix tailTrace_4707014
  have hstable : (prefixWord ++ tailWord_4707014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707014).length < 2 ^ (prefixWord ++ tailWord_4707014).sum := by decide
  have hdescent : baseEnd_4707014 < baseStart_4707014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707020 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4707020 : Nat := 118140960795 + 4707020 * 2 ^ 59
def prefixEnd_4707020 : Nat := 4983230072969 + 3 ^ 40 * 4707020 * 2
def baseEnd_4707020 : Nat := 2416963710326278996302815

theorem tailTrace_4707020 : CollatzResearch.WordTrace tailWord_4707020 prefixEnd_4707020 2416963710326278996302815 := by
  unfold tailWord_4707020
  simp only [CollatzResearch.WordTrace]
  refine ⟨85839561703638954929879257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114452748938185273239839009 85839561703638954929879257)
  ·
    refine ⟨64379671277729216197409443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85839561703638954929879257 64379671277729216197409443)
    ·
      refine ⟨96569506916593824296114165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64379671277729216197409443 96569506916593824296114165)
      ·
        refine ⟨9053391273430671027760703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96569506916593824296114165 9053391273430671027760703)
        ·
          refine ⟨13580086910146006541641055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9053391273430671027760703 13580086910146006541641055)
          ·
            refine ⟨20370130365219009812461583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13580086910146006541641055 20370130365219009812461583)
            ·
              refine ⟨30555195547828514718692375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20370130365219009812461583 30555195547828514718692375)
              ·
                refine ⟨45832793321742772078038563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30555195547828514718692375 45832793321742772078038563)
                ·
                  refine ⟨68749189982614158117057845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45832793321742772078038563 68749189982614158117057845)
                  ·
                    refine ⟨6445236560870077323474173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68749189982614158117057845 6445236560870077323474173)
                    ·
                      refine ⟨2416963710326278996302815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445236560870077323474173 2416963710326278996302815)
                      ·
                        rfl

theorem cell23_4707020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4707020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707020 prefixEnd_4707020 := by exact prefixLift 4707020
  have htrace : WordTrace (prefixWord ++ tailWord_4707020) baseStart_4707020 baseEnd_4707020 := by
    simpa [prefixWord, tailWord_4707020, baseEnd_4707020] using wordTrace_append hprefix tailTrace_4707020
  have hstable : (prefixWord ++ tailWord_4707020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707020).length < 2 ^ (prefixWord ++ tailWord_4707020).sum := by decide
  have hdescent : baseEnd_4707020 < baseStart_4707020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707021 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4707021 : Nat := 118140960795 + 4707021 * 2 ^ 59
def prefixEnd_4707021 : Nat := 4983230072969 + 3 ^ 40 * 4707021 * 2
def baseEnd_4707021 : Nat := 2416964223806933492390311

theorem tailTrace_4707021 : CollatzResearch.WordTrace tailWord_4707021 prefixEnd_4707021 2416964223806933492390311 := by
  unfold tailWord_4707021
  simp only [CollatzResearch.WordTrace]
  refine ⟨171679159880274287030544917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114452773253516191353696611 171679159880274287030544917)
  ·
    refine ⟨8047460619387857204556793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 171679159880274287030544917 8047460619387857204556793)
    ·
      refine ⟨6035595464540892903417595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8047460619387857204556793 6035595464540892903417595)
      ·
        refine ⟨9053393196811339355126393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035595464540892903417595 9053393196811339355126393)
        ·
          refine ⟨6790044897608504516344795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9053393196811339355126393 6790044897608504516344795)
          ·
            refine ⟨10185067346412756774517193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6790044897608504516344795 10185067346412756774517193)
            ·
              refine ⟨7638800509809567580887895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10185067346412756774517193 7638800509809567580887895)
              ·
                refine ⟨11458200764714351371331843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638800509809567580887895 11458200764714351371331843)
                ·
                  refine ⟨17187301147071527056997765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11458200764714351371331843 17187301147071527056997765)
                  ·
                    refine ⟨3222618965075911323187081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17187301147071527056997765 3222618965075911323187081)
                    ·
                      refine ⟨2416964223806933492390311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222618965075911323187081 2416964223806933492390311)
                      ·
                        rfl

theorem cell23_4707021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4707021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707021 prefixEnd_4707021 := by exact prefixLift 4707021
  have htrace : WordTrace (prefixWord ++ tailWord_4707021) baseStart_4707021 baseEnd_4707021 := by
    simpa [prefixWord, tailWord_4707021, baseEnd_4707021] using wordTrace_append hprefix tailTrace_4707021
  have hstable : (prefixWord ++ tailWord_4707021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707021).length < 2 ^ (prefixWord ++ tailWord_4707021).sum := by decide
  have hdescent : baseEnd_4707021 < baseStart_4707021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707073 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4707073 : Nat := 118140960795 + 4707073 * 2 ^ 59
def prefixEnd_4707073 : Nat := 4983230072969 + 3 ^ 40 * 4707073 * 2
def baseEnd_4707073 : Nat := 2416990924800967288940071

theorem tailTrace_4707073 : CollatzResearch.WordTrace tailWord_4707073 prefixEnd_4707073 2416990924800967288940071 := by
  unfold tailWord_4707073
  simp only [CollatzResearch.WordTrace]
  refine ⟨171681056476085899911437873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114454037650723933274291915 171681056476085899911437873)
  ·
    refine ⟨128760792357064424933578405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171681056476085899911437873 128760792357064424933578405)
    ·
      refine ⟨24142648566949579675045951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128760792357064424933578405 24142648566949579675045951)
      ·
        refine ⟨36213972850424369512568927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24142648566949579675045951 36213972850424369512568927)
        ·
          refine ⟨54320959275636554268853391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36213972850424369512568927 54320959275636554268853391)
          ·
            refine ⟨81481438913454831403280087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54320959275636554268853391 81481438913454831403280087)
            ·
              refine ⟨122222158370182247104920131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81481438913454831403280087 122222158370182247104920131)
              ·
                refine ⟨183333237555273370657380197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122222158370182247104920131 183333237555273370657380197)
                ·
                  refine ⟨34374982041613756998258787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183333237555273370657380197 34374982041613756998258787)
                  ·
                    refine ⟨51562473062420635497388181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34374982041613756998258787 51562473062420635497388181)
                    ·
                      refine ⟨2416990924800967288940071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51562473062420635497388181 2416990924800967288940071)
                      ·
                        rfl

theorem cell23_4707073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4707073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707073 prefixEnd_4707073 := by exact prefixLift 4707073
  have htrace : WordTrace (prefixWord ++ tailWord_4707073) baseStart_4707073 baseEnd_4707073 := by
    simpa [prefixWord, tailWord_4707073, baseEnd_4707073] using wordTrace_append hprefix tailTrace_4707073
  have hstable : (prefixWord ++ tailWord_4707073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707073).length < 2 ^ (prefixWord ++ tailWord_4707073).sum := by decide
  have hdescent : baseEnd_4707073 < baseStart_4707073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
