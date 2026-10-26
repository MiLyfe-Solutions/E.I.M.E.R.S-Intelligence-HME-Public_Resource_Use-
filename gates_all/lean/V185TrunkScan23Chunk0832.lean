import V185TrunkScan23Chunk0831

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4922686 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4922686 : Nat := 118140960795 + 4922686 * 2 ^ 59
def prefixEnd_4922686 : Nat := 4983230072969 + 3 ^ 40 * 4922686 * 2
def baseEnd_4922686 : Nat := 2527704029158832202085985

theorem tailTrace_4922686 : CollatzResearch.WordTrace tailWord_4922686 prefixEnd_4922686 2527704029158832202085985 := by
  unfold tailWord_4922686
  simp only [CollatzResearch.WordTrace]
  refine ⟨22443138580494603085018489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119696739095971216453431941 22443138580494603085018489)
  ·
    refine ⟨16832353935370952313763867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22443138580494603085018489 16832353935370952313763867)
    ·
      refine ⟨25248530903056428470645801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16832353935370952313763867 25248530903056428470645801)
      ·
        refine ⟨18936398177292321352984351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25248530903056428470645801 18936398177292321352984351)
        ·
          refine ⟨28404597265938482029476527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18936398177292321352984351 28404597265938482029476527)
          ·
            refine ⟨42606895898907723044214791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28404597265938482029476527 42606895898907723044214791)
            ·
              refine ⟨63910343848361584566322187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42606895898907723044214791 63910343848361584566322187)
              ·
                refine ⟨95865515772542376849483281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63910343848361584566322187 95865515772542376849483281)
                ·
                  refine ⟨71899136829406782637112461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95865515772542376849483281 71899136829406782637112461)
                  ·
                    refine ⟨26962176311027543488917173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71899136829406782637112461 26962176311027543488917173)
                    ·
                      refine ⟨2527704029158832202085985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26962176311027543488917173 2527704029158832202085985)
                      ·
                        rfl

theorem cell23_4922686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4922686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922686 prefixEnd_4922686 := by exact prefixLift 4922686
  have htrace : WordTrace (prefixWord ++ tailWord_4922686) baseStart_4922686 baseEnd_4922686 := by
    simpa [prefixWord, tailWord_4922686, baseEnd_4922686] using wordTrace_append hprefix tailTrace_4922686
  have hstable : (prefixWord ++ tailWord_4922686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922686).length < 2 ^ (prefixWord ++ tailWord_4922686).sum := by decide
  have hdescent : baseEnd_4922686 < baseStart_4922686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922717 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4922717 : Nat := 118140960795 + 4922717 * 2 ^ 59
def prefixEnd_4922717 : Nat := 4983230072969 + 3 ^ 40 * 4922717 * 2
def baseEnd_4922717 : Nat := 2527719947059121580798343

theorem tailTrace_4922717 : CollatzResearch.WordTrace tailWord_4922717 prefixEnd_4922717 2527719947059121580798343 := by
  unfold tailWord_4922717
  simp only [CollatzResearch.WordTrace]
  refine ⟨179546239306844516974526405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119697492871229677983017603 179546239306844516974526405)
  ·
    refine ⟨33664919870033346932723701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179546239306844516974526405 33664919870033346932723701)
    ·
      refine ⟨3156086237815626274942847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33664919870033346932723701 3156086237815626274942847)
      ·
        refine ⟨4734129356723439412414271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156086237815626274942847 4734129356723439412414271)
        ·
          refine ⟨7101194035085159118621407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4734129356723439412414271 7101194035085159118621407)
          ·
            refine ⟨10651791052627738677932111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101194035085159118621407 10651791052627738677932111)
            ·
              refine ⟨15977686578941608016898167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10651791052627738677932111 15977686578941608016898167)
              ·
                refine ⟨23966529868412412025347251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15977686578941608016898167 23966529868412412025347251)
                ·
                  refine ⟨35949794802618618038020877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23966529868412412025347251 35949794802618618038020877)
                  ·
                    refine ⟨13481173050981981764257829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35949794802618618038020877 13481173050981981764257829)
                    ·
                      refine ⟨2527719947059121580798343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13481173050981981764257829 2527719947059121580798343)
                      ·
                        rfl

theorem cell23_4922717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4922717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922717 prefixEnd_4922717 := by exact prefixLift 4922717
  have htrace : WordTrace (prefixWord ++ tailWord_4922717) baseStart_4922717 baseEnd_4922717 := by
    simpa [prefixWord, tailWord_4922717, baseEnd_4922717] using wordTrace_append hprefix tailTrace_4922717
  have hstable : (prefixWord ++ tailWord_4922717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922717).length < 2 ^ (prefixWord ++ tailWord_4922717).sum := by decide
  have hdescent : baseEnd_4922717 < baseStart_4922717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922720 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3]
def baseStart_4922720 : Nat := 118140960795 + 4922720 * 2 ^ 59
def prefixEnd_4922720 : Nat := 4983230072969 + 3 ^ 40 * 4922720 * 2
def baseEnd_4922720 : Nat := 2527721487501085069060829

theorem tailTrace_4922720 : CollatzResearch.WordTrace tailWord_4922720 prefixEnd_4922720 2527721487501085069060829 := by
  unfold tailWord_4922720
  simp only [CollatzResearch.WordTrace]
  refine ⟨89773174362916824243442807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119697565817222432324590409 89773174362916824243442807)
  ·
    refine ⟨134659761544375236365164211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89773174362916824243442807 134659761544375236365164211)
    ·
      refine ⟨201989642316562854547746317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134659761544375236365164211 201989642316562854547746317)
      ·
        refine ⟨75746115868711070455404869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201989642316562854547746317 75746115868711070455404869)
        ·
          refine ⟨14202396725383325710388413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75746115868711070455404869 14202396725383325710388413)
          ·
            refine ⟨5325898772018747141395655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14202396725383325710388413 5325898772018747141395655)
            ·
              refine ⟨7988848158028120712093483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5325898772018747141395655 7988848158028120712093483)
              ·
                refine ⟨11983272237042181068140225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7988848158028120712093483 11983272237042181068140225)
                ·
                  refine ⟨8987454177781635801105169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11983272237042181068140225 8987454177781635801105169)
                  ·
                    refine ⟨6740590633336226850828877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8987454177781635801105169 6740590633336226850828877)
                    ·
                      refine ⟨2527721487501085069060829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6740590633336226850828877 2527721487501085069060829)
                      ·
                        rfl

theorem cell23_4922720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_4922720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922720 prefixEnd_4922720 := by exact prefixLift 4922720
  have htrace : WordTrace (prefixWord ++ tailWord_4922720) baseStart_4922720 baseEnd_4922720 := by
    simpa [prefixWord, tailWord_4922720, baseEnd_4922720] using wordTrace_append hprefix tailTrace_4922720
  have hstable : (prefixWord ++ tailWord_4922720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922720).length < 2 ^ (prefixWord ++ tailWord_4922720).sum := by decide
  have hdescent : baseEnd_4922720 < baseStart_4922720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922727 : List Nat := [1, 1, 5, 1, 4, 1, 2, 3, 1, 4]
def baseStart_4922727 : Nat := 118140960795 + 4922727 * 2 ^ 59
def prefixEnd_4922727 : Nat := 4983230072969 + 3 ^ 40 * 4922727 * 2
def baseEnd_4922727 : Nat := 842575027288555513891099

theorem tailTrace_4922727 : CollatzResearch.WordTrace tailWord_4922727 prefixEnd_4922727 842575027288555513891099 := by
  unfold tailWord_4922727
  simp only [CollatzResearch.WordTrace]
  refine ⟨179546604036808288682390435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119697736024538859121593623 179546604036808288682390435)
  ·
    refine ⟨269319906055212433023585653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179546604036808288682390435 269319906055212433023585653)
    ·
      refine ⟨25248741192676165595961155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269319906055212433023585653 25248741192676165595961155)
      ·
        refine ⟨37873111789014248393941733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25248741192676165595961155 37873111789014248393941733)
        ·
          refine ⟨7101208460440171573864075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37873111789014248393941733 7101208460440171573864075)
          ·
            refine ⟨10651812690660257360796113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101208460440171573864075 10651812690660257360796113)
            ·
              refine ⟨7988859517995193020597085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10651812690660257360796113 7988859517995193020597085)
              ·
                refine ⟨2995822319248197382723907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7988859517995193020597085 2995822319248197382723907)
                ·
                  refine ⟨4493733478872296074085861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995822319248197382723907 4493733478872296074085861)
                  ·
                    refine ⟨842575027288555513891099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493733478872296074085861 842575027288555513891099)
                    ·
                      rfl

theorem cell23_4922727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_4922727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922727 prefixEnd_4922727 := by exact prefixLift 4922727
  have htrace : WordTrace (prefixWord ++ tailWord_4922727) baseStart_4922727 baseEnd_4922727 := by
    simpa [prefixWord, tailWord_4922727, baseEnd_4922727] using wordTrace_append hprefix tailTrace_4922727
  have hstable : (prefixWord ++ tailWord_4922727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922727).length < 2 ^ (prefixWord ++ tailWord_4922727).sum := by decide
  have hdescent : baseEnd_4922727 < baseStart_4922727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922743 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 4, 3, 2]
def baseStart_4922743 : Nat := 118140960795 + 4922743 * 2 ^ 59
def prefixEnd_4922743 : Nat := 4983230072969 + 3 ^ 40 * 4922743 * 2
def baseEnd_4922743 : Nat := 2527733297556138479073223

theorem tailTrace_4922743 : CollatzResearch.WordTrace tailWord_4922743 prefixEnd_4922743 2527733297556138479073223 := by
  unfold tailWord_4922743
  simp only [CollatzResearch.WordTrace]
  refine ⟨179547187604750323414972883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119698125069833548943315255 179547187604750323414972883)
  ·
    refine ⟨269320781407125485122459325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179547187604750323414972883 269320781407125485122459325)
    ·
      refine ⟨100995293027672056920922247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269320781407125485122459325 100995293027672056920922247)
      ·
        refine ⟨151492939541508085381383371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100995293027672056920922247 151492939541508085381383371)
        ·
          refine ⟨227239409312262128072075057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151492939541508085381383371 227239409312262128072075057)
          ·
            refine ⟨170429556984196596054056293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227239409312262128072075057 170429556984196596054056293)
            ·
              refine ⟨31955541934536861760135555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170429556984196596054056293 31955541934536861760135555)
              ·
                refine ⟨47933312901805292640203333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31955541934536861760135555 47933312901805292640203333)
                ·
                  refine ⟨8987496169088492370038125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47933312901805292640203333 8987496169088492370038125)
                  ·
                    refine ⟨3370311063408184638764297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8987496169088492370038125 3370311063408184638764297)
                    ·
                      refine ⟨2527733297556138479073223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370311063408184638764297 2527733297556138479073223)
                      ·
                        rfl

theorem cell23_4922743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_4922743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922743 prefixEnd_4922743 := by exact prefixLift 4922743
  have htrace : WordTrace (prefixWord ++ tailWord_4922743) baseStart_4922743 baseEnd_4922743 := by
    simpa [prefixWord, tailWord_4922743, baseEnd_4922743] using wordTrace_append hprefix tailTrace_4922743
  have hstable : (prefixWord ++ tailWord_4922743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922743).length < 2 ^ (prefixWord ++ tailWord_4922743).sum := by decide
  have hdescent : baseEnd_4922743 < baseStart_4922743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922773 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_4922773 : Nat := 118140960795 + 4922773 * 2 ^ 59
def prefixEnd_4922773 : Nat := 4983230072969 + 3 ^ 40 * 4922773 * 2
def baseEnd_4922773 : Nat := 2527748701975773361698085

theorem tailTrace_4922773 : CollatzResearch.WordTrace tailWord_4922773 prefixEnd_4922773 2527748701975773361698085 := by
  unfold tailWord_4922773
  simp only [CollatzResearch.WordTrace]
  refine ⟨179548281794641638538564973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119698854529761092359043315 179548281794641638538564973)
  ·
    refine ⟨67330605672990614451961865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179548281794641638538564973 67330605672990614451961865)
    ·
      refine ⟨50497954254742960838971399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67330605672990614451961865 50497954254742960838971399)
      ·
        refine ⟨75746931382114441258457099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50497954254742960838971399 75746931382114441258457099)
        ·
          refine ⟨113620397073171661887685649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75746931382114441258457099 113620397073171661887685649)
          ·
            refine ⟨85215297804878746415764237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113620397073171661887685649 85215297804878746415764237)
            ·
              refine ⟨31955736676829529905911589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85215297804878746415764237 31955736676829529905911589)
              ·
                refine ⟨5991700626905536857358423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31955736676829529905911589 5991700626905536857358423)
                ·
                  refine ⟨8987550940358305286037635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5991700626905536857358423 8987550940358305286037635)
                  ·
                    refine ⟨13481326410537457929056453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8987550940358305286037635 13481326410537457929056453)
                    ·
                      refine ⟨2527748701975773361698085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13481326410537457929056453 2527748701975773361698085)
                      ·
                        rfl

theorem cell23_4922773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_4922773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922773 prefixEnd_4922773 := by exact prefixLift 4922773
  have htrace : WordTrace (prefixWord ++ tailWord_4922773) baseStart_4922773 baseEnd_4922773 := by
    simpa [prefixWord, tailWord_4922773, baseEnd_4922773] using wordTrace_append hprefix tailTrace_4922773
  have hstable : (prefixWord ++ tailWord_4922773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922773).length < 2 ^ (prefixWord ++ tailWord_4922773).sum := by decide
  have hdescent : baseEnd_4922773 < baseStart_4922773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922783 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 4, 4]
def baseStart_4922783 : Nat := 118140960795 + 4922783 * 2 ^ 59
def prefixEnd_4922783 : Nat := 4983230072969 + 3 ^ 40 * 4922783 * 2
def baseEnd_4922783 : Nat := 842584612260772774191013

theorem tailTrace_4922783 : CollatzResearch.WordTrace tailWord_4922783 prefixEnd_4922783 842584612260772774191013 := by
  unfold tailWord_4922783
  simp only [CollatzResearch.WordTrace]
  refine ⟨179548646524605410246429003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119699097683070273497619335 179548646524605410246429003)
  ·
    refine ⟨269322969786908115369643505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179548646524605410246429003 269322969786908115369643505)
    ·
      refine ⟨201992227340181086527232629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269322969786908115369643505 201992227340181086527232629)
      ·
        refine ⟨18936771313141976861928059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201992227340181086527232629 18936771313141976861928059)
        ·
          refine ⟨28405156969712965292892089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18936771313141976861928059 28405156969712965292892089)
          ·
            refine ⟨21303867727284723969669067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28405156969712965292892089 21303867727284723969669067)
            ·
              refine ⟨31955801590927085954503601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21303867727284723969669067 31955801590927085954503601)
              ·
                refine ⟨23966851193195314465877701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31955801590927085954503601 23966851193195314465877701)
                ·
                  refine ⟨4493784598724121462352069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23966851193195314465877701 4493784598724121462352069)
                  ·
                    refine ⟨842584612260772774191013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493784598724121462352069 842584612260772774191013)
                    ·
                      rfl

theorem cell23_4922783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_4922783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922783 prefixEnd_4922783 := by exact prefixLift 4922783
  have htrace : WordTrace (prefixWord ++ tailWord_4922783) baseStart_4922783 baseEnd_4922783 := by
    simpa [prefixWord, tailWord_4922783, baseEnd_4922783] using wordTrace_append hprefix tailTrace_4922783
  have hstable : (prefixWord ++ tailWord_4922783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922783).length < 2 ^ (prefixWord ++ tailWord_4922783).sum := by decide
  have hdescent : baseEnd_4922783 < baseStart_4922783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922823 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_4922823 : Nat := 118140960795 + 4922823 * 2 ^ 59
def prefixEnd_4922823 : Nat := 4983230072969 + 3 ^ 40 * 4922823 * 2
def baseEnd_4922823 : Nat := 2527774376008498166072855

theorem tailTrace_4922823 : CollatzResearch.WordTrace tailWord_4922823 prefixEnd_4922823 2527774376008498166072855 := by
  unfold tailWord_4922823
  simp only [CollatzResearch.WordTrace]
  refine ⟨179550105444460497077885123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119700070296306998051923415 179550105444460497077885123)
  ·
    refine ⟨269325158166690745616827685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179550105444460497077885123 269325158166690745616827685)
    ·
      refine ⟨50498467156254514803155191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269325158166690745616827685 50498467156254514803155191)
      ·
        refine ⟨75747700734381772204732787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50498467156254514803155191 75747700734381772204732787)
        ·
          refine ⟨113621551101572658307099181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75747700734381772204732787 113621551101572658307099181)
          ·
            refine ⟨42608081663089746865162193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113621551101572658307099181 42608081663089746865162193)
            ·
              refine ⟨31956061247317310148871645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42608081663089746865162193 31956061247317310148871645)
              ·
                refine ⟨11983522967743991305826867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31956061247317310148871645 11983522967743991305826867)
                ·
                  refine ⟨17975284451615986958740301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11983522967743991305826867 17975284451615986958740301)
                  ·
                    refine ⟨6740731669355995109527613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17975284451615986958740301 6740731669355995109527613)
                    ·
                      refine ⟨2527774376008498166072855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6740731669355995109527613 2527774376008498166072855)
                      ·
                        rfl

theorem cell23_4922823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_4922823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922823 prefixEnd_4922823 := by exact prefixLift 4922823
  have htrace : WordTrace (prefixWord ++ tailWord_4922823) baseStart_4922823 baseEnd_4922823 := by
    simpa [prefixWord, tailWord_4922823, baseEnd_4922823] using wordTrace_append hprefix tailTrace_4922823
  have hstable : (prefixWord ++ tailWord_4922823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922823).length < 2 ^ (prefixWord ++ tailWord_4922823).sum := by decide
  have hdescent : baseEnd_4922823 < baseStart_4922823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922858 : List Nat := [3, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_4922858 : Nat := 118140960795 + 4922858 * 2 ^ 59
def prefixEnd_4922858 : Nat := 4983230072969 + 3 ^ 40 * 4922858 * 2
def baseEnd_4922858 : Nat := 2527792347831405529135195

theorem tailTrace_4922858 : CollatzResearch.WordTrace tailWord_4922858 prefixEnd_4922858 2527792347831405529135195 := by
  unfold tailWord_4922858
  simp only [CollatzResearch.WordTrace]
  refine ⟨44887845499833424513852307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119700921332889132036939485 44887845499833424513852307)
  ·
    refine ⟨67331768249750136770778461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44887845499833424513852307 67331768249750136770778461)
    ·
      refine ⟨25249413093656301289041923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67331768249750136770778461 25249413093656301289041923)
      ·
        refine ⟨37874119640484451933562885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25249413093656301289041923 37874119640484451933562885)
        ·
          refine ⟨7101397432590834737543041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37874119640484451933562885 7101397432590834737543041)
          ·
            refine ⟨5326048074443126053157281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7101397432590834737543041 5326048074443126053157281)
            ·
              refine ⟨3994536055832344539867961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326048074443126053157281 3994536055832344539867961)
              ·
                refine ⟨2995902041874258404900971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994536055832344539867961 2995902041874258404900971)
                ·
                  refine ⟨4493853062811387607351457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995902041874258404900971 4493853062811387607351457)
                  ·
                    refine ⟨3370389797108540705513593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4493853062811387607351457 3370389797108540705513593)
                    ·
                      refine ⟨2527792347831405529135195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370389797108540705513593 2527792347831405529135195)
                      ·
                        rfl

theorem cell23_4922858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_4922858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922858 prefixEnd_4922858 := by exact prefixLift 4922858
  have htrace : WordTrace (prefixWord ++ tailWord_4922858) baseStart_4922858 baseEnd_4922858 := by
    simpa [prefixWord, tailWord_4922858, baseEnd_4922858] using wordTrace_append hprefix tailTrace_4922858
  have hstable : (prefixWord ++ tailWord_4922858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922858).length < 2 ^ (prefixWord ++ tailWord_4922858).sum := by decide
  have hdescent : baseEnd_4922858 < baseStart_4922858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922914 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_4922914 : Nat := 118140960795 + 4922914 * 2 ^ 59
def prefixEnd_4922914 : Nat := 4983230072969 + 3 ^ 40 * 4922914 * 2
def baseEnd_4922914 : Nat := 2527821102748057310034937

theorem tailTrace_4922914 : CollatzResearch.WordTrace tailWord_4922914 prefixEnd_4922914 2527821102748057310034937 := by
  unfold tailWord_4922914
  simp only [CollatzResearch.WordTrace]
  refine ⟨44888356121782704904861949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119702282991420546412965197 44888356121782704904861949)
  ·
    refine ⟨16833133545668514339323231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44888356121782704904861949 16833133545668514339323231)
    ·
      refine ⟨25249700318502771508984847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16833133545668514339323231 25249700318502771508984847)
      ·
        refine ⟨37874550477754157263477271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25249700318502771508984847 37874550477754157263477271)
        ·
          refine ⟨56811825716631235895215907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37874550477754157263477271 56811825716631235895215907)
          ·
            refine ⟨85217738574946853842823861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56811825716631235895215907 85217738574946853842823861)
            ·
              refine ⟨7989162991401267547764737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85217738574946853842823861 7989162991401267547764737)
              ·
                refine ⟨5991872243550950660823553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7989162991401267547764737 5991872243550950660823553)
                ·
                  refine ⟨4493904182663212995617665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5991872243550950660823553 4493904182663212995617665)
                  ·
                    refine ⟨3370428136997409746713249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4493904182663212995617665 3370428136997409746713249)
                    ·
                      refine ⟨2527821102748057310034937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370428136997409746713249 2527821102748057310034937)
                      ·
                        rfl

theorem cell23_4922914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_4922914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922914 prefixEnd_4922914 := by exact prefixLift 4922914
  have htrace : WordTrace (prefixWord ++ tailWord_4922914) baseStart_4922914 baseEnd_4922914 := by
    simpa [prefixWord, tailWord_4922914, baseEnd_4922914] using wordTrace_append hprefix tailTrace_4922914
  have hstable : (prefixWord ++ tailWord_4922914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922914).length < 2 ^ (prefixWord ++ tailWord_4922914).sum := by decide
  have hdescent : baseEnd_4922914 < baseStart_4922914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922933 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_4922933 : Nat := 118140960795 + 4922933 * 2 ^ 59
def prefixEnd_4922933 : Nat := 4983230072969 + 3 ^ 40 * 4922933 * 2
def baseEnd_4922933 : Nat := 842610286293497578565783

theorem tailTrace_4922933 : CollatzResearch.WordTrace tailWord_4922933 prefixEnd_4922933 842610286293497578565783 := by
  unfold tailWord_4922933
  simp only [CollatzResearch.WordTrace]
  refine ⟨179554117474061985864389453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119702744982707990576259635 179554117474061985864389453)
  ·
    refine ⟨67332794052773244699146045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179554117474061985864389453 67332794052773244699146045)
    ·
      refine ⟨25249797769789966762179767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67332794052773244699146045 25249797769789966762179767)
      ·
        refine ⟨37874696654684950143269651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25249797769789966762179767 37874696654684950143269651)
        ·
          refine ⟨56812044982027425214904477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37874696654684950143269651 56812044982027425214904477)
          ·
            refine ⟨21304516868260284455589179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56812044982027425214904477 21304516868260284455589179)
            ·
              refine ⟨31956775302390426683383769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21304516868260284455589179 31956775302390426683383769)
              ·
                refine ⟨23967581476792820012537827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31956775302390426683383769 23967581476792820012537827)
                ·
                  refine ⟨35951372215189230018806741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23967581476792820012537827 35951372215189230018806741)
                  ·
                    refine ⟨842610286293497578565783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35951372215189230018806741 842610286293497578565783)
                    ·
                      rfl

theorem cell23_4922933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_4922933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922933 prefixEnd_4922933 := by exact prefixLift 4922933
  have htrace : WordTrace (prefixWord ++ tailWord_4922933) baseStart_4922933 baseEnd_4922933 := by
    simpa [prefixWord, tailWord_4922933, baseEnd_4922933] using wordTrace_append hprefix tailTrace_4922933
  have hstable : (prefixWord ++ tailWord_4922933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922933).length < 2 ^ (prefixWord ++ tailWord_4922933).sum := by decide
  have hdescent : baseEnd_4922933 < baseStart_4922933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922953 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_4922953 : Nat := 118140960795 + 4922953 * 2 ^ 59
def prefixEnd_4922953 : Nat := 4983230072969 + 3 ^ 40 * 4922953 * 2
def baseEnd_4922953 : Nat := 2527841128493582657447257

theorem tailTrace_4922953 : CollatzResearch.WordTrace tailWord_4922953 prefixEnd_4922953 2527841128493582657447257 := by
  unfold tailWord_4922953
  simp only [CollatzResearch.WordTrace]
  refine ⟨179554846933989529280117513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119703231289326352853411675 179554846933989529280117513)
  ·
    refine ⟨134666135200492146960088135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179554846933989529280117513 134666135200492146960088135)
    ·
      refine ⟨201999202800738220440132203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134666135200492146960088135 201999202800738220440132203)
      ·
        refine ⟨302998804201107330660198305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201999202800738220440132203 302998804201107330660198305)
        ·
          refine ⟨227249103150830497995148729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302998804201107330660198305 227249103150830497995148729)
          ·
            refine ⟨170436827363122873496361547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227249103150830497995148729 170436827363122873496361547)
            ·
              refine ⟨255655241044684310244542321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170436827363122873496361547 255655241044684310244542321)
              ·
                refine ⟨191741430783513232683406741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255655241044684310244542321 191741430783513232683406741)
                ·
                  refine ⟨8987879567977182782034691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 191741430783513232683406741 8987879567977182782034691)
                  ·
                    refine ⟨13481819351965774173052037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8987879567977182782034691 13481819351965774173052037)
                    ·
                      refine ⟨2527841128493582657447257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13481819351965774173052037 2527841128493582657447257)
                      ·
                        rfl

theorem cell23_4922953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_4922953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922953 prefixEnd_4922953 := by exact prefixLift 4922953
  have htrace : WordTrace (prefixWord ++ tailWord_4922953) baseStart_4922953 baseEnd_4922953 := by
    simpa [prefixWord, tailWord_4922953, baseEnd_4922953] using wordTrace_append hprefix tailTrace_4922953
  have hstable : (prefixWord ++ tailWord_4922953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922953).length < 2 ^ (prefixWord ++ tailWord_4922953).sum := by decide
  have hdescent : baseEnd_4922953 < baseStart_4922953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922970 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2]
def baseStart_4922970 : Nat := 118140960795 + 4922970 * 2 ^ 59
def prefixEnd_4922970 : Nat := 4983230072969 + 3 ^ 40 * 4922970 * 2
def baseEnd_4922970 : Nat := 2527849857664709090934679

theorem tailTrace_4922970 : CollatzResearch.WordTrace tailWord_4922970 prefixEnd_4922970 2527849857664709090934679 := by
  unfold tailWord_4922970
  simp only [CollatzResearch.WordTrace]
  refine ⟨44888866743731985295871591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119703644649951960788990909 44888866743731985295871591)
  ·
    refine ⟨67333300115597977943807387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44888866743731985295871591 67333300115597977943807387)
    ·
      refine ⟨100999950173396966915711081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67333300115597977943807387 100999950173396966915711081)
      ·
        refine ⟨75749962630047725186783311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100999950173396966915711081 75749962630047725186783311)
        ·
          refine ⟨113624943945071587780174967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75749962630047725186783311 113624943945071587780174967)
          ·
            refine ⟨170437415917607381670262451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113624943945071587780174967 170437415917607381670262451)
            ·
              refine ⟨255656123876411072505393677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170437415917607381670262451 255656123876411072505393677)
              ·
                refine ⟨95871046453654152189522629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255656123876411072505393677 95871046453654152189522629)
                ·
                  refine ⟨17975821210060153535535493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95871046453654152189522629 17975821210060153535535493)
                  ·
                    refine ⟨3370466476886278787912905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17975821210060153535535493 3370466476886278787912905)
                    ·
                      refine ⟨2527849857664709090934679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370466476886278787912905 2527849857664709090934679)
                      ·
                        rfl

theorem cell23_4922970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_4922970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922970 prefixEnd_4922970 := by exact prefixLift 4922970
  have htrace : WordTrace (prefixWord ++ tailWord_4922970) baseStart_4922970 baseEnd_4922970 := by
    simpa [prefixWord, tailWord_4922970, baseEnd_4922970] using wordTrace_append hprefix tailTrace_4922970
  have hstable : (prefixWord ++ tailWord_4922970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922970).length < 2 ^ (prefixWord ++ tailWord_4922970).sum := by decide
  have hdescent : baseEnd_4922970 < baseStart_4922970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922983 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4922983 : Nat := 118140960795 + 4922983 * 2 ^ 59
def prefixEnd_4922983 : Nat := 4983230072969 + 3 ^ 40 * 4922983 * 2
def baseEnd_4922983 : Nat := 2527856532913217540072119

theorem tailTrace_4922983 : CollatzResearch.WordTrace tailWord_4922983 prefixEnd_4922983 2527856532913217540072119 := by
  unfold tailWord_4922983
  simp only [CollatzResearch.WordTrace]
  refine ⟨179555941123880844403709603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119703960749253896269139735 179555941123880844403709603)
  ·
    refine ⟨269333911685821266605564405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179555941123880844403709603 269333911685821266605564405)
    ·
      refine ⟨25250054220545743744271663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269333911685821266605564405 25250054220545743744271663)
      ·
        refine ⟨37875081330818615616407495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25250054220545743744271663 37875081330818615616407495)
        ·
          refine ⟨56812621996227923424611243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37875081330818615616407495 56812621996227923424611243)
          ·
            refine ⟨85218932994341885136916865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56812621996227923424611243 85218932994341885136916865)
            ·
              refine ⟨63914199745756413852687649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85218932994341885136916865 63914199745756413852687649)
              ·
                refine ⟨47935649809317310389515737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63914199745756413852687649 47935649809317310389515737)
                ·
                  refine ⟨35951737356987982792136803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47935649809317310389515737 35951737356987982792136803)
                  ·
                    refine ⟨53927606035481974188205205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35951737356987982792136803 53927606035481974188205205)
                    ·
                      refine ⟨2527856532913217540072119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53927606035481974188205205 2527856532913217540072119)
                      ·
                        rfl

theorem cell23_4922983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4922983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922983 prefixEnd_4922983 := by exact prefixLift 4922983
  have htrace : WordTrace (prefixWord ++ tailWord_4922983) baseStart_4922983 baseEnd_4922983 := by
    simpa [prefixWord, tailWord_4922983, baseEnd_4922983] using wordTrace_append hprefix tailTrace_4922983
  have hstable : (prefixWord ++ tailWord_4922983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922983).length < 2 ^ (prefixWord ++ tailWord_4922983).sum := by decide
  have hdescent : baseEnd_4922983 < baseStart_4922983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923023 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 7, 5]
def baseStart_4923023 : Nat := 118140960795 + 4923023 * 2 ^ 59
def prefixEnd_4923023 : Nat := 4983230072969 + 3 ^ 40 * 4923023 * 2
def baseEnd_4923023 : Nat := 842625690713132461190645

theorem tailTrace_4923023 : CollatzResearch.WordTrace tailWord_4923023 prefixEnd_4923023 842625690713132461190645 := by
  unfold tailWord_4923023
  simp only [CollatzResearch.WordTrace]
  refine ⟨179557400043735931235165723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119704933362490620823443815 179557400043735931235165723)
  ·
    refine ⟨269336100065603896852748585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179557400043735931235165723 269336100065603896852748585)
    ·
      refine ⟨202002075049202922639561439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269336100065603896852748585 202002075049202922639561439)
      ·
        refine ⟨303003112573804383959342159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202002075049202922639561439 303003112573804383959342159)
        ·
          refine ⟨454504668860706575939013239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303003112573804383959342159 454504668860706575939013239)
          ·
            refine ⟨681757003291059863908519859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454504668860706575939013239 681757003291059863908519859)
            ·
              refine ⟨1022635504936589795862779789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681757003291059863908519859 1022635504936589795862779789)
              ·
                refine ⟨383488314351221173448542421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022635504936589795862779789 383488314351221173448542421)
                ·
                  refine ⟨8988007367606746252700213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 383488314351221173448542421 8988007367606746252700213)
                  ·
                    refine ⟨842625690713132461190645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8988007367606746252700213 842625690713132461190645)
                    ·
                      rfl

theorem cell23_4923023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_4923023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923023 prefixEnd_4923023 := by exact prefixLift 4923023
  have htrace : WordTrace (prefixWord ++ tailWord_4923023) baseStart_4923023 baseEnd_4923023 := by
    simpa [prefixWord, tailWord_4923023, baseEnd_4923023] using wordTrace_append hprefix tailTrace_4923023
  have hstable : (prefixWord ++ tailWord_4923023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923023).length < 2 ^ (prefixWord ++ tailWord_4923023).sum := by decide
  have hdescent : baseEnd_4923023 < baseStart_4923023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923031 : List Nat := [1, 1, 3, 3, 2, 4, 2, 2, 1, 4]
def baseStart_4923031 : Nat := 118140960795 + 4923031 * 2 ^ 59
def prefixEnd_4923031 : Nat := 4983230072969 + 3 ^ 40 * 4923031 * 2
def baseEnd_4923031 : Nat := 842627059994877784090633

theorem tailTrace_4923031 : CollatzResearch.WordTrace tailWord_4923031 prefixEnd_4923031 842627059994877784090633 := by
  unfold tailWord_4923031
  simp only [CollatzResearch.WordTrace]
  refine ⟨179557691827706948601456947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119705127885137965734304631 179557691827706948601456947)
  ·
    refine ⟨269336537741560422902185421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179557691827706948601456947 269336537741560422902185421)
    ·
      refine ⟨101001201653085158588319533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269336537741560422902185421 101001201653085158588319533)
      ·
        refine ⟨37875450619906934470619825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101001201653085158588319533 37875450619906934470619825)
        ·
          refine ⟨28406587964930200852964869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37875450619906934470619825 28406587964930200852964869)
          ·
            refine ⟨5326235243424412659930913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28406587964930200852964869 5326235243424412659930913)
            ·
              refine ⟨3994676432568309494948185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326235243424412659930913 3994676432568309494948185)
              ·
                refine ⟨2996007324426232121211139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994676432568309494948185 2996007324426232121211139)
                ·
                  refine ⟨4494010986639348181816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996007324426232121211139 4494010986639348181816709)
                  ·
                    refine ⟨842627059994877784090633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494010986639348181816709 842627059994877784090633)
                    ·
                      rfl

theorem cell23_4923031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_4923031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923031 prefixEnd_4923031 := by exact prefixLift 4923031
  have htrace : WordTrace (prefixWord ++ tailWord_4923031) baseStart_4923031 baseEnd_4923031 := by
    simpa [prefixWord, tailWord_4923031, baseEnd_4923031] using wordTrace_append hprefix tailTrace_4923031
  have hstable : (prefixWord ++ tailWord_4923031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923031).length < 2 ^ (prefixWord ++ tailWord_4923031).sum := by decide
  have hdescent : baseEnd_4923031 < baseStart_4923031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923037 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_4923037 : Nat := 118140960795 + 4923037 * 2 ^ 59
def prefixEnd_4923037 : Nat := 4983230072969 + 3 ^ 40 * 4923037 * 2
def baseEnd_4923037 : Nat := 2527884260868560328796871

theorem tailTrace_4923037 : CollatzResearch.WordTrace tailWord_4923037 prefixEnd_4923037 2527884260868560328796871 := by
  unfold tailWord_4923037
  simp only [CollatzResearch.WordTrace]
  refine ⟨179557910665685211626175365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119705273777123474417450243 179557910665685211626175365)
  ·
    refine ⟨33667108249815977179907881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179557910665685211626175365 33667108249815977179907881)
    ·
      refine ⟨25250331187361982884930911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33667108249815977179907881 25250331187361982884930911)
      ·
        refine ⟨37875496781042974327396367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25250331187361982884930911 37875496781042974327396367)
        ·
          refine ⟨56813245171564461491094551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37875496781042974327396367 56813245171564461491094551)
          ·
            refine ⟨85219867757346692236641827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56813245171564461491094551 85219867757346692236641827)
            ·
              refine ⟨127829801636020038354962741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85219867757346692236641827 127829801636020038354962741)
              ·
                refine ⟨11984043903376878595777757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127829801636020038354962741 11984043903376878595777757)
                ·
                  refine ⟨4494016463766329473416659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11984043903376878595777757 4494016463766329473416659)
                  ·
                    refine ⟨6741024695649494210124989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4494016463766329473416659 6741024695649494210124989)
                    ·
                      refine ⟨2527884260868560328796871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741024695649494210124989 2527884260868560328796871)
                      ·
                        rfl

theorem cell23_4923037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_4923037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923037 prefixEnd_4923037 := by exact prefixLift 4923037
  have htrace : WordTrace (prefixWord ++ tailWord_4923037) baseStart_4923037 baseEnd_4923037 := by
    simpa [prefixWord, tailWord_4923037, baseEnd_4923037] using wordTrace_append hprefix tailTrace_4923037
  have hstable : (prefixWord ++ tailWord_4923037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923037).length < 2 ^ (prefixWord ++ tailWord_4923037).sum := by decide
  have hdescent : baseEnd_4923037 < baseStart_4923037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923040 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 3, 5]
def baseStart_4923040 : Nat := 118140960795 + 4923040 * 2 ^ 59
def prefixEnd_4923040 : Nat := 4983230072969 + 3 ^ 40 * 4923040 * 2
def baseEnd_4923040 : Nat := 842628600436841272353119

theorem tailTrace_4923040 : CollatzResearch.WordTrace tailWord_4923040 prefixEnd_4923040 842628600436841272353119 := by
  unfold tailWord_4923040
  simp only [CollatzResearch.WordTrace]
  refine ⟨89779010042337171569267287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119705346723116228759023049 89779010042337171569267287)
  ·
    refine ⟨134668515063505757353900931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89779010042337171569267287 134668515063505757353900931)
    ·
      refine ⟨202002772595258636030851397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134668515063505757353900931 202002772595258636030851397)
      ·
        refine ⟨37875519861610994255784637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202002772595258636030851397 37875519861610994255784637)
        ·
          refine ⟨14203319948104122845919239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37875519861610994255784637 14203319948104122845919239)
          ·
            refine ⟨21304979922156184268878859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14203319948104122845919239 21304979922156184268878859)
            ·
              refine ⟨31957469883234276403318289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21304979922156184268878859 31957469883234276403318289)
              ·
                refine ⟨23968102412425707302488717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31957469883234276403318289 23968102412425707302488717)
                ·
                  refine ⟨8988038404659640238433269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23968102412425707302488717 8988038404659640238433269)
                  ·
                    refine ⟨842628600436841272353119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8988038404659640238433269 842628600436841272353119)
                    ·
                      rfl

theorem cell23_4923040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_4923040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923040 prefixEnd_4923040 := by exact prefixLift 4923040
  have htrace : WordTrace (prefixWord ++ tailWord_4923040) baseStart_4923040 baseEnd_4923040 := by
    simpa [prefixWord, tailWord_4923040, baseEnd_4923040] using wordTrace_append hprefix tailTrace_4923040
  have hstable : (prefixWord ++ tailWord_4923040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923040).length < 2 ^ (prefixWord ++ tailWord_4923040).sum := by decide
  have hdescent : baseEnd_4923040 < baseStart_4923040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923080 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_4923080 : Nat := 118140960795 + 4923080 * 2 ^ 59
def prefixEnd_4923080 : Nat := 4983230072969 + 3 ^ 40 * 4923080 * 2
def baseEnd_4923080 : Nat := 2527906340536703660559173

theorem tailTrace_4923080 : CollatzResearch.WordTrace tailWord_4923080 prefixEnd_4923080 2527906340536703660559173 := by
  unfold tailWord_4923080
  simp only [CollatzResearch.WordTrace]
  refine ⟨89779739502264714984995347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119706319336352953313327129 89779739502264714984995347)
  ·
    refine ⟨134669609253397072477493021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89779739502264714984995347 134669609253397072477493021)
    ·
      refine ⟨50501103470023902179059883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134669609253397072477493021 50501103470023902179059883)
      ·
        refine ⟨75751655205035853268589825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50501103470023902179059883 75751655205035853268589825)
        ·
          refine ⟨56813741403776889951442369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75751655205035853268589825 56813741403776889951442369)
          ·
            refine ⟨42610306052832667463581777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56813741403776889951442369 42610306052832667463581777)
            ·
              refine ⟨31957729539624500597686333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42610306052832667463581777 31957729539624500597686333)
              ·
                refine ⟨11984148577359187724132375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31957729539624500597686333 11984148577359187724132375)
                ·
                  refine ⟨17976222866038781586198563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11984148577359187724132375 17976222866038781586198563)
                  ·
                    refine ⟨26964334299058172379297845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17976222866038781586198563 26964334299058172379297845)
                    ·
                      refine ⟨2527906340536703660559173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26964334299058172379297845 2527906340536703660559173)
                      ·
                        rfl

theorem cell23_4923080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_4923080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923080 prefixEnd_4923080 := by exact prefixLift 4923080
  have htrace : WordTrace (prefixWord ++ tailWord_4923080) baseStart_4923080 baseEnd_4923080 := by
    simpa [prefixWord, tailWord_4923080, baseEnd_4923080] using wordTrace_append hprefix tailTrace_4923080
  have hstable : (prefixWord ++ tailWord_4923080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923080).length < 2 ^ (prefixWord ++ tailWord_4923080).sum := by decide
  have hdescent : baseEnd_4923080 < baseStart_4923080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923107 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4923107 : Nat := 118140960795 + 4923107 * 2 ^ 59
def prefixEnd_4923107 : Nat := 4983230072969 + 3 ^ 40 * 4923107 * 2
def baseEnd_4923107 : Nat := 2527920204514375054921549

theorem tailTrace_4923107 : CollatzResearch.WordTrace tailWord_4923107 prefixEnd_4923107 2527920204514375054921549 := by
  unfold tailWord_4923107
  simp only [CollatzResearch.WordTrace]
  refine ⟨179560463775431613581223575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119706975850287742387482383 179560463775431613581223575)
  ·
    refine ⟨269340695663147420371835363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179560463775431613581223575 269340695663147420371835363)
    ·
      refine ⟨404011043494721130557753045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269340695663147420371835363 404011043494721130557753045)
      ·
        refine ⟨9469008831907526497447337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 404011043494721130557753045 9469008831907526497447337)
        ·
          refine ⟨7101756623930644873085503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9469008831907526497447337 7101756623930644873085503)
          ·
            refine ⟨10652634935895967309628255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101756623930644873085503 10652634935895967309628255)
            ·
              refine ⟨15978952403843950964442383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10652634935895967309628255 15978952403843950964442383)
              ·
                refine ⟨23968428605765926446663575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15978952403843950964442383 23968428605765926446663575)
                ·
                  refine ⟨35952642908648889669995363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23968428605765926446663575 35952642908648889669995363)
                  ·
                    refine ⟨53928964362973334504993045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35952642908648889669995363 53928964362973334504993045)
                    ·
                      refine ⟨2527920204514375054921549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53928964362973334504993045 2527920204514375054921549)
                      ·
                        rfl

theorem cell23_4923107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4923107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923107 prefixEnd_4923107 := by exact prefixLift 4923107
  have htrace : WordTrace (prefixWord ++ tailWord_4923107) baseStart_4923107 baseEnd_4923107 := by
    simpa [prefixWord, tailWord_4923107, baseEnd_4923107] using wordTrace_append hprefix tailTrace_4923107
  have hstable : (prefixWord ++ tailWord_4923107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923107).length < 2 ^ (prefixWord ++ tailWord_4923107).sum := by decide
  have hdescent : baseEnd_4923107 < baseStart_4923107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923111 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4923111 : Nat := 118140960795 + 4923111 * 2 ^ 59
def prefixEnd_4923111 : Nat := 4983230072969 + 3 ^ 40 * 4923111 * 2
def baseEnd_4923111 : Nat := 2527922258436993039271531

theorem tailTrace_4923111 : CollatzResearch.WordTrace tailWord_4923111 prefixEnd_4923111 2527922258436993039271531 := by
  unfold tailWord_4923111
  simp only [CollatzResearch.WordTrace]
  refine ⟨179560609667417122264369187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119707073111611414842912791 179560609667417122264369187)
  ·
    refine ⟨269340914501125683396553781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179560609667417122264369187 269340914501125683396553781)
    ·
      refine ⟨25250710734480532818426917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269340914501125683396553781 25250710734480532818426917)
      ·
        refine ⟨4734508262715099903455047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25250710734480532818426917 4734508262715099903455047)
        ·
          refine ⟨7101762394072649855182571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4734508262715099903455047 7101762394072649855182571)
          ·
            refine ⟨10652643591108974782773857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101762394072649855182571 10652643591108974782773857)
            ·
              refine ⟨7989482693331731087080393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10652643591108974782773857 7989482693331731087080393)
              ·
                refine ⟨5992112019998798315310295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7989482693331731087080393 5992112019998798315310295)
                ·
                  refine ⟨8988168029998197472965443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5992112019998798315310295 8988168029998197472965443)
                  ·
                    refine ⟨13482252044997296209448165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8988168029998197472965443 13482252044997296209448165)
                    ·
                      refine ⟨2527922258436993039271531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13482252044997296209448165 2527922258436993039271531)
                      ·
                        rfl

theorem cell23_4923111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4923111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923111 prefixEnd_4923111 := by exact prefixLift 4923111
  have htrace : WordTrace (prefixWord ++ tailWord_4923111) baseStart_4923111 baseEnd_4923111 := by
    simpa [prefixWord, tailWord_4923111, baseEnd_4923111] using wordTrace_append hprefix tailTrace_4923111
  have hstable : (prefixWord ++ tailWord_4923111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923111).length < 2 ^ (prefixWord ++ tailWord_4923111).sum := by decide
  have hdescent : baseEnd_4923111 < baseStart_4923111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923117 : List Nat := [1, 5, 1, 2, 1, 2, 4, 7]
def baseStart_4923117 : Nat := 118140960795 + 4923117 * 2 ^ 59
def prefixEnd_4923117 : Nat := 4983230072969 + 3 ^ 40 * 4923117 * 2
def baseEnd_4923117 : Nat := 93626864419293333918389

theorem tailTrace_4923117 : CollatzResearch.WordTrace tailWord_4923117 prefixEnd_4923117 93626864419293333918389 := by
  unfold tailWord_4923117
  simp only [CollatzResearch.WordTrace]
  refine ⟨179560828505395385289087605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119707219003596923526058403 179560828505395385289087605)
  ·
    refine ⟨16833827672380817370851963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179560828505395385289087605 16833827672380817370851963)
    ·
      refine ⟨25250741508571226056277945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16833827672380817370851963 25250741508571226056277945)
      ·
        refine ⟨18938056131428419542208459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25250741508571226056277945 18938056131428419542208459)
        ·
          refine ⟨28407084197142629313312689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18938056131428419542208459 28407084197142629313312689)
          ·
            refine ⟨21305313147856971984984517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28407084197142629313312689 21305313147856971984984517)
            ·
              refine ⟨3994746215223182247184597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21305313147856971984984517 3994746215223182247184597)
              ·
                refine ⟨93626864419293333918389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3994746215223182247184597 93626864419293333918389)
                ·
                  rfl

theorem cell23_4923117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 7].length) (baseStart_4923117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923117 prefixEnd_4923117 := by exact prefixLift 4923117
  have htrace : WordTrace (prefixWord ++ tailWord_4923117) baseStart_4923117 baseEnd_4923117 := by
    simpa [prefixWord, tailWord_4923117, baseEnd_4923117] using wordTrace_append hprefix tailTrace_4923117
  have hstable : (prefixWord ++ tailWord_4923117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923117).length < 2 ^ (prefixWord ++ tailWord_4923117).sum := by decide
  have hdescent : baseEnd_4923117 < baseStart_4923117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923127 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_4923127 : Nat := 118140960795 + 4923127 * 2 ^ 59
def prefixEnd_4923127 : Nat := 4983230072969 + 3 ^ 40 * 4923127 * 2
def baseEnd_4923127 : Nat := 2527930474127464976671457

theorem tailTrace_4923127 : CollatzResearch.WordTrace tailWord_4923127 prefixEnd_4923127 2527930474127464976671457 := by
  unfold tailWord_4923127
  simp only [CollatzResearch.WordTrace]
  refine ⟨179561193235359156996951635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119707462156906104664634423 179561193235359156996951635)
  ·
    refine ⟨269341789853038735495427453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179561193235359156996951635 269341789853038735495427453)
    ·
      refine ⟨101003171194889525810785295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269341789853038735495427453 101003171194889525810785295)
      ·
        refine ⟨151504756792334288716177943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101003171194889525810785295 151504756792334288716177943)
        ·
          refine ⟨227257135188501433074266915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151504756792334288716177943 227257135188501433074266915)
          ·
            refine ⟨340885702782752149611400373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227257135188501433074266915 340885702782752149611400373)
            ·
              refine ⟨31958034635883014026068785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 340885702782752149611400373 31958034635883014026068785)
              ·
                refine ⟨23968525976912260519551589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31958034635883014026068785 23968525976912260519551589)
                ·
                  refine ⟨4494098620671048847415923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23968525976912260519551589 4494098620671048847415923)
                  ·
                    refine ⟨6741147931006573271123885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4494098620671048847415923 6741147931006573271123885)
                    ·
                      refine ⟨2527930474127464976671457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741147931006573271123885 2527930474127464976671457)
                      ·
                        rfl

theorem cell23_4923127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_4923127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923127 prefixEnd_4923127 := by exact prefixLift 4923127
  have htrace : WordTrace (prefixWord ++ tailWord_4923127) baseStart_4923127 baseEnd_4923127 := by
    simpa [prefixWord, tailWord_4923127, baseEnd_4923127] using wordTrace_append hprefix tailTrace_4923127
  have hstable : (prefixWord ++ tailWord_4923127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923127).length < 2 ^ (prefixWord ++ tailWord_4923127).sum := by decide
  have hdescent : baseEnd_4923127 < baseStart_4923127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923134 : List Nat := [4, 2, 2, 1, 4, 1, 9]
def baseStart_4923134 : Nat := 118140960795 + 4923134 * 2 ^ 59
def prefixEnd_4923134 : Nat := 4983230072969 + 3 ^ 40 * 4923134 * 2
def baseEnd_4923134 : Nat := 31209062573975882089925

theorem tailTrace_4923134 : CollatzResearch.WordTrace tailWord_4923134 prefixEnd_4923134 31209062573975882089925 := by
  unfold tailWord_4923134
  simp only [CollatzResearch.WordTrace]
  refine ⟨22445181068291724649057057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119707632364222531461637637 22445181068291724649057057)
  ·
    refine ⟨16833885801218793486792793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22445181068291724649057057 16833885801218793486792793)
    ·
      refine ⟨12625414350914095115094595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16833885801218793486792793 12625414350914095115094595)
      ·
        refine ⟨18938121526371142672641893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12625414350914095115094595 18938121526371142672641893)
        ·
          refine ⟨3550897786194589251120355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18938121526371142672641893 3550897786194589251120355)
          ·
            refine ⟨5326346679291883876680533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550897786194589251120355 5326346679291883876680533)
            ·
              refine ⟨31209062573975882089925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5326346679291883876680533 31209062573975882089925)
              ·
                rfl

theorem cell23_4923134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 9].length) (baseStart_4923134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923134 prefixEnd_4923134 := by exact prefixLift 4923134
  have htrace : WordTrace (prefixWord ++ tailWord_4923134) baseStart_4923134 baseEnd_4923134 := by
    simpa [prefixWord, tailWord_4923134, baseEnd_4923134] using wordTrace_append hprefix tailTrace_4923134
  have hstable : (prefixWord ++ tailWord_4923134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923134).length < 2 ^ (prefixWord ++ tailWord_4923134).sum := by decide
  have hdescent : baseEnd_4923134 < baseStart_4923134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923144 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_4923144 : Nat := 118140960795 + 4923144 * 2 ^ 59
def prefixEnd_4923144 : Nat := 4983230072969 + 3 ^ 40 * 4923144 * 2
def baseEnd_4923144 : Nat := 2527939203298591410158879

theorem tailTrace_4923144 : CollatzResearch.WordTrace tailWord_4923144 prefixEnd_4923144 2527939203298591410158879 := by
  unfold tailWord_4923144
  simp only [CollatzResearch.WordTrace]
  refine ⟨89780906638148784450160243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119707875517531712600213657 89780906638148784450160243)
  ·
    refine ⟨134671359957223176675240365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89780906638148784450160243 134671359957223176675240365)
    ·
      refine ⟨50501759983958691253215137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134671359957223176675240365 50501759983958691253215137)
      ·
        refine ⟨37876319987969018439911353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50501759983958691253215137 37876319987969018439911353)
        ·
          refine ⟨28407239990976763829933515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37876319987969018439911353 28407239990976763829933515)
          ·
            refine ⟨42610859986465145744900273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28407239990976763829933515 42610859986465145744900273)
            ·
              refine ⟨31958144989848859308675205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42610859986465145744900273 31958144989848859308675205)
              ·
                refine ⟨5992152185596661120376601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31958144989848859308675205 5992152185596661120376601)
                ·
                  refine ⟨4494114139197495840282451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5992152185596661120376601 4494114139197495840282451)
                  ·
                    refine ⟨6741171208796243760423677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4494114139197495840282451 6741171208796243760423677)
                    ·
                      refine ⟨2527939203298591410158879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741171208796243760423677 2527939203298591410158879)
                      ·
                        rfl

theorem cell23_4923144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_4923144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923144 prefixEnd_4923144 := by exact prefixLift 4923144
  have htrace : WordTrace (prefixWord ++ tailWord_4923144) baseStart_4923144 baseEnd_4923144 := by
    simpa [prefixWord, tailWord_4923144, baseEnd_4923144] using wordTrace_append hprefix tailTrace_4923144
  have hstable : (prefixWord ++ tailWord_4923144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923144).length < 2 ^ (prefixWord ++ tailWord_4923144).sum := by decide
  have hdescent : baseEnd_4923144 < baseStart_4923144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923160 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 2, 6]
def baseStart_4923160 : Nat := 118140960795 + 4923160 * 2 ^ 59
def prefixEnd_4923160 : Nat := 4983230072969 + 3 ^ 40 * 4923160 * 2
def baseEnd_4923160 : Nat := 842649139663021115852935

theorem tailTrace_4923160 : CollatzResearch.WordTrace tailWord_4923160 prefixEnd_4923160 842649139663021115852935 := by
  unfold tailWord_4923160
  simp only [CollatzResearch.WordTrace]
  refine ⟨89781198422119801816451467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119708264562826402421935289 89781198422119801816451467)
  ·
    refine ⟨134671797633179702724677201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89781198422119801816451467 134671797633179702724677201)
    ·
      refine ⟨101003848224884777043507901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134671797633179702724677201 101003848224884777043507901)
      ·
        refine ⟨37876443084331791391315463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101003848224884777043507901 37876443084331791391315463)
        ·
          refine ⟨56814664626497687086973195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37876443084331791391315463 56814664626497687086973195)
          ·
            refine ⟨85221996939746530630459793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56814664626497687086973195 85221996939746530630459793)
            ·
              refine ⟨63916497704809897972844845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85221996939746530630459793 63916497704809897972844845)
              ·
                refine ⟨23968686639303711739816817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63916497704809897972844845 23968686639303711739816817)
                ·
                  refine ⟨17976514979477783804862613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23968686639303711739816817 17976514979477783804862613)
                  ·
                    refine ⟨842649139663021115852935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17976514979477783804862613 842649139663021115852935)
                    ·
                      rfl

theorem cell23_4923160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_4923160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923160 prefixEnd_4923160 := by exact prefixLift 4923160
  have htrace : WordTrace (prefixWord ++ tailWord_4923160) baseStart_4923160 baseEnd_4923160 := by
    simpa [prefixWord, tailWord_4923160, baseEnd_4923160] using wordTrace_append hprefix tailTrace_4923160
  have hstable : (prefixWord ++ tailWord_4923160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923160).length < 2 ^ (prefixWord ++ tailWord_4923160).sum := by decide
  have hdescent : baseEnd_4923160 < baseStart_4923160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923217 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_4923217 : Nat := 118140960795 + 4923217 * 2 ^ 59
def prefixEnd_4923217 : Nat := 4983230072969 + 3 ^ 40 * 4923217 * 2
def baseEnd_4923217 : Nat := 2527976687386369624546043

theorem tailTrace_4923217 : CollatzResearch.WordTrace tailWord_4923217 prefixEnd_4923217 2527976687386369624546043 := by
  unfold tailWord_4923217
  simp only [CollatzResearch.WordTrace]
  refine ⟨179564475805033102367727905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119709650536688734911818603 179564475805033102367727905)
  ·
    refine ⟨134673356853774826775795929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179564475805033102367727905 134673356853774826775795929)
    ·
      refine ⟨101005017640331120081846947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134673356853774826775795929 101005017640331120081846947)
      ·
        refine ⟨151507526460496680122770421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101005017640331120081846947 151507526460496680122770421)
        ·
          refine ⟨14203830605671563761509727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151507526460496680122770421 14203830605671563761509727)
          ·
            refine ⟨21305745908507345642264591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14203830605671563761509727 21305745908507345642264591)
            ·
              refine ⟨31958618862761018463396887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21305745908507345642264591 31958618862761018463396887)
              ·
                refine ⟨47937928294141527695095331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31958618862761018463396887 47937928294141527695095331)
                ·
                  refine ⟨71906892441212291542642997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47937928294141527695095331 71906892441212291542642997)
                  ·
                    refine ⟨6741271166363652332122781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71906892441212291542642997 6741271166363652332122781)
                    ·
                      refine ⟨2527976687386369624546043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741271166363652332122781 2527976687386369624546043)
                      ·
                        rfl

theorem cell23_4923217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_4923217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923217 prefixEnd_4923217 := by exact prefixLift 4923217
  have htrace : WordTrace (prefixWord ++ tailWord_4923217) baseStart_4923217 baseEnd_4923217 := by
    simpa [prefixWord, tailWord_4923217, baseEnd_4923217] using wordTrace_append hprefix tailTrace_4923217
  have hstable : (prefixWord ++ tailWord_4923217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923217).length < 2 ^ (prefixWord ++ tailWord_4923217).sum := by decide
  have hdescent : baseEnd_4923217 < baseStart_4923217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923257 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_4923257 : Nat := 118140960795 + 4923257 * 2 ^ 59
def prefixEnd_4923257 : Nat := 4983230072969 + 3 ^ 40 * 4923257 * 2
def baseEnd_4923257 : Nat := 2527997226612549468045859

theorem tailTrace_4923257 : CollatzResearch.WordTrace tailWord_4923257 prefixEnd_4923257 2527997226612549468045859 := by
  unfold tailWord_4923257
  simp only [CollatzResearch.WordTrace]
  refine ⟨179565934724888189199184025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119710623149925459466122683 179565934724888189199184025)
  ·
    refine ⟨134674451043666141899388019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179565934724888189199184025 134674451043666141899388019)
    ·
      refine ⟨202011676565499212849082029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134674451043666141899388019 202011676565499212849082029)
      ·
        refine ⟨75754378712062204818405761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202011676565499212849082029 75754378712062204818405761)
        ·
          refine ⟨56815784034046653613804321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75754378712062204818405761 56815784034046653613804321)
          ·
            refine ⟨42611838025534990210353241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56815784034046653613804321 42611838025534990210353241)
            ·
              refine ⟨31958878519151242657764931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42611838025534990210353241 31958878519151242657764931)
              ·
                refine ⟨47938317778726863986647397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31958878519151242657764931 47938317778726863986647397)
                ·
                  refine ⟨8988434583511286997496387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47938317778726863986647397 8988434583511286997496387)
                  ·
                    refine ⟨13482651875266930496244581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8988434583511286997496387 13482651875266930496244581)
                    ·
                      refine ⟨2527997226612549468045859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13482651875266930496244581 2527997226612549468045859)
                      ·
                        rfl

theorem cell23_4923257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_4923257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923257 prefixEnd_4923257 := by exact prefixLift 4923257
  have htrace : WordTrace (prefixWord ++ tailWord_4923257) baseStart_4923257 baseEnd_4923257 := by
    simpa [prefixWord, tailWord_4923257, baseEnd_4923257] using wordTrace_append hprefix tailTrace_4923257
  have hstable : (prefixWord ++ tailWord_4923257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923257).length < 2 ^ (prefixWord ++ tailWord_4923257).sum := by decide
  have hdescent : baseEnd_4923257 < baseStart_4923257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923280 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 10]
def baseStart_4923280 : Nat := 118140960795 + 4923280 * 2 ^ 59
def prefixEnd_4923280 : Nat := 4983230072969 + 3 ^ 40 * 4923280 * 2
def baseEnd_4923280 : Nat := 280889892963066986450917

theorem tailTrace_4923280 : CollatzResearch.WordTrace tailWord_4923280 prefixEnd_4923280 280889892963066986450917 := by
  unfold tailWord_4923280
  simp only [CollatzResearch.WordTrace]
  refine ⟨89783386801902432063635647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119711182402536576084847529 89783386801902432063635647)
  ·
    refine ⟨134675080202853648095453471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89783386801902432063635647 134675080202853648095453471)
    ·
      refine ⟨202012620304280472143180207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134675080202853648095453471 202012620304280472143180207)
      ·
        refine ⟨303018930456420708214770311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202012620304280472143180207 303018930456420708214770311)
        ·
          refine ⟨454528395684631062322155467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303018930456420708214770311 454528395684631062322155467)
          ·
            refine ⟨681792593526946593483233201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454528395684631062322155467 681792593526946593483233201)
            ·
              refine ⟨511344445145209945112424901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681792593526946593483233201 511344445145209945112424901)
              ·
                refine ⟨95877083464726864708579669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511344445145209945112424901 95877083464726864708579669)
                ·
                  refine ⟨280889892963066986450917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 95877083464726864708579669 280889892963066986450917)
                  ·
                    rfl

theorem cell23_4923280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_4923280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923280 prefixEnd_4923280 := by exact prefixLift 4923280
  have htrace : WordTrace (prefixWord ++ tailWord_4923280) baseStart_4923280 baseEnd_4923280 := by
    simpa [prefixWord, tailWord_4923280, baseEnd_4923280] using wordTrace_append hprefix tailTrace_4923280
  have hstable : (prefixWord ++ tailWord_4923280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923280).length < 2 ^ (prefixWord ++ tailWord_4923280).sum := by decide
  have hdescent : baseEnd_4923280 < baseStart_4923280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923327 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 3, 5]
def baseStart_4923327 : Nat := 118140960795 + 4923327 * 2 ^ 59
def prefixEnd_4923327 : Nat := 4983230072969 + 3 ^ 40 * 4923327 * 2
def baseEnd_4923327 : Nat := 842677723419454731390179

theorem tailTrace_4923327 : CollatzResearch.WordTrace tailWord_4923327 prefixEnd_4923327 842677723419454731390179 := by
  unfold tailWord_4923327
  simp only [CollatzResearch.WordTrace]
  refine ⟨179568487834634591154232235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119712325223089727436154823 179568487834634591154232235)
  ·
    refine ⟨269352731751951886731348353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179568487834634591154232235 269352731751951886731348353)
    ·
      refine ⟨202014548813963915048511265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269352731751951886731348353 202014548813963915048511265)
      ·
        refine ⟨151510911610472936286383449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202014548813963915048511265 151510911610472936286383449)
        ·
          refine ⟨113633183707854702214787587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151510911610472936286383449 113633183707854702214787587)
          ·
            refine ⟨170449775561782053322181381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113633183707854702214787587 170449775561782053322181381)
            ·
              refine ⟨31959332917834134997909009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170449775561782053322181381 31959332917834134997909009)
              ·
                refine ⟨23969499688375601248431757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31959332917834134997909009 23969499688375601248431757)
                ·
                  refine ⟨8988562383140850468161909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23969499688375601248431757 8988562383140850468161909)
                  ·
                    refine ⟨842677723419454731390179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8988562383140850468161909 842677723419454731390179)
                    ·
                      rfl

theorem cell23_4923327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_4923327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923327 prefixEnd_4923327 := by exact prefixLift 4923327
  have htrace : WordTrace (prefixWord ++ tailWord_4923327) baseStart_4923327 baseEnd_4923327 := by
    simpa [prefixWord, tailWord_4923327, baseEnd_4923327] using wordTrace_append hprefix tailTrace_4923327
  have hstable : (prefixWord ++ tailWord_4923327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923327).length < 2 ^ (prefixWord ++ tailWord_4923327).sum := by decide
  have hdescent : baseEnd_4923327 < baseStart_4923327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923344 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 1, 5]
def baseStart_4923344 : Nat := 118140960795 + 4923344 * 2 ^ 59
def prefixEnd_4923344 : Nat := 4983230072969 + 3 ^ 40 * 4923344 * 2
def baseEnd_4923344 : Nat := 842680633143163542552653

theorem tailTrace_4923344 : CollatzResearch.WordTrace tailWord_4923344 prefixEnd_4923344 842680633143163542552653 := by
  unfold tailWord_4923344
  simp only [CollatzResearch.WordTrace]
  refine ⟨89784553937786501528800543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119712738583715335371734057 89784553937786501528800543)
  ·
    refine ⟨134676830906679752293200815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89784553937786501528800543 134676830906679752293200815)
    ·
      refine ⟨202015246360019628439801223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134676830906679752293200815 202015246360019628439801223)
      ·
        refine ⟨303022869540029442659701835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202015246360019628439801223 303022869540029442659701835)
        ·
          refine ⟨454534304310044163989552753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303022869540029442659701835 454534304310044163989552753)
          ·
            refine ⟨340900728232533122992164565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454534304310044163989552753 340900728232533122992164565)
            ·
              refine ⟨7989860817949995070128857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 340900728232533122992164565 7989860817949995070128857)
              ·
                refine ⟨5992395613462496302596643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7989860817949995070128857 5992395613462496302596643)
                ·
                  refine ⟨8988593420193744453894965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5992395613462496302596643 8988593420193744453894965)
                  ·
                    refine ⟨842680633143163542552653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8988593420193744453894965 842680633143163542552653)
                    ·
                      rfl

theorem cell23_4923344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_4923344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923344 prefixEnd_4923344 := by exact prefixLift 4923344
  have htrace : WordTrace (prefixWord ++ tailWord_4923344) baseStart_4923344 baseEnd_4923344 := by
    simpa [prefixWord, tailWord_4923344, baseEnd_4923344] using wordTrace_append hprefix tailTrace_4923344
  have hstable : (prefixWord ++ tailWord_4923344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923344).length < 2 ^ (prefixWord ++ tailWord_4923344).sum := by decide
  have hdescent : baseEnd_4923344 < baseStart_4923344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923351 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 2, 3, 2]
def baseStart_4923351 : Nat := 118140960795 + 4923351 * 2 ^ 59
def prefixEnd_4923351 : Nat := 4983230072969 + 3 ^ 40 * 4923351 * 2
def baseEnd_4923351 : Nat := 2528045493794072100270427

theorem tailTrace_4923351 : CollatzResearch.WordTrace tailWord_4923351 prefixEnd_4923351 2528045493794072100270427 := by
  unfold tailWord_4923351
  simp only [CollatzResearch.WordTrace]
  refine ⟨179569363186547643253105907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119712908791031762168737271 179569363186547643253105907)
  ·
    refine ⟨269354044779821464879658861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179569363186547643253105907 269354044779821464879658861)
    ·
      refine ⟨101007766792433049329872073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269354044779821464879658861 101007766792433049329872073)
      ·
        refine ⟨75755825094324786997404055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101007766792433049329872073 75755825094324786997404055)
        ·
          refine ⟨113633737641487180496106083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75755825094324786997404055 113633737641487180496106083)
          ·
            refine ⟨170450606462230770744159125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113633737641487180496106083 170450606462230770744159125)
            ·
              refine ⟨7989872177917067378632459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 170450606462230770744159125 7989872177917067378632459)
              ·
                refine ⟨11984808266875601067948689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7989872177917067378632459 11984808266875601067948689)
                ·
                  refine ⟨8988606200156700800961517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11984808266875601067948689 8988606200156700800961517)
                  ·
                    refine ⟨3370727325058762800360569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8988606200156700800961517 3370727325058762800360569)
                    ·
                      refine ⟨2528045493794072100270427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370727325058762800360569 2528045493794072100270427)
                      ·
                        rfl

theorem cell23_4923351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_4923351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923351 prefixEnd_4923351 := by exact prefixLift 4923351
  have htrace : WordTrace (prefixWord ++ tailWord_4923351) baseStart_4923351 baseEnd_4923351 := by
    simpa [prefixWord, tailWord_4923351, baseEnd_4923351] using wordTrace_append hprefix tailTrace_4923351
  have hstable : (prefixWord ++ tailWord_4923351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923351).length < 2 ^ (prefixWord ++ tailWord_4923351).sum := by decide
  have hdescent : baseEnd_4923351 < baseStart_4923351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923384 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_4923384 : Nat := 118140960795 + 4923384 * 2 ^ 59
def prefixEnd_4923384 : Nat := 4983230072969 + 3 ^ 40 * 4923384 * 2
def baseEnd_4923384 : Nat := 2528062438655670471157775

theorem tailTrace_4923384 : CollatzResearch.WordTrace tailWord_4923384 prefixEnd_4923384 2528062438655670471157775 := by
  unfold tailWord_4923384
  simp only [CollatzResearch.WordTrace]
  refine ⟨89785283397714044944528603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119713711196952059926038137 89785283397714044944528603)
  ·
    refine ⟨134677925096571067416792905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89785283397714044944528603 134677925096571067416792905)
    ·
      refine ⟨101008443822428300562594679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134677925096571067416792905 101008443822428300562594679)
      ·
        refine ⟨151512665733642450843892019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101008443822428300562594679 151512665733642450843892019)
        ·
          refine ⟨227268998600463676265838029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151512665733642450843892019 227268998600463676265838029)
          ·
            refine ⟨85225874475173878599689261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227268998600463676265838029 85225874475173878599689261)
            ·
              refine ⟨31959702928190204474883473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85225874475173878599689261 31959702928190204474883473)
              ·
                refine ⟨23969777196142653356162605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31959702928190204474883473 23969777196142653356162605)
                ·
                  refine ⟨8988666448553495008560977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23969777196142653356162605 8988666448553495008560977)
                  ·
                    refine ⟨6741499836415121256420733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8988666448553495008560977 6741499836415121256420733)
                    ·
                      refine ⟨2528062438655670471157775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741499836415121256420733 2528062438655670471157775)
                      ·
                        rfl

theorem cell23_4923384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_4923384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923384 prefixEnd_4923384 := by exact prefixLift 4923384
  have htrace : WordTrace (prefixWord ++ tailWord_4923384) baseStart_4923384 baseEnd_4923384 := by
    simpa [prefixWord, tailWord_4923384, baseEnd_4923384] using wordTrace_append hprefix tailTrace_4923384
  have hstable : (prefixWord ++ tailWord_4923384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923384).length < 2 ^ (prefixWord ++ tailWord_4923384).sum := by decide
  have hdescent : baseEnd_4923384 < baseStart_4923384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923387 : List Nat := [1, 1, 1, 1, 1, 3, 7, 8]
def baseStart_4923387 : Nat := 118140960795 + 4923387 * 2 ^ 59
def prefixEnd_4923387 : Nat := 4983230072969 + 3 ^ 40 * 4923387 * 2
def baseEnd_4923387 : Nat := 93631999225838294793343

theorem tailTrace_4923387 : CollatzResearch.WordTrace tailWord_4923387 prefixEnd_4923387 93631999225838294793343 := by
  unfold tailWord_4923387
  simp only [CollatzResearch.WordTrace]
  refine ⟨179570676214417221401416415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119713784142944814267610943 179570676214417221401416415)
  ·
    refine ⟨269356014321625832102124623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179570676214417221401416415 269356014321625832102124623)
    ·
      refine ⟨404034021482438748153186935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269356014321625832102124623 404034021482438748153186935)
      ·
        refine ⟨606051032223658122229780403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404034021482438748153186935 606051032223658122229780403)
        ·
          refine ⟨909076548335487183344670605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606051032223658122229780403 909076548335487183344670605)
          ·
            refine ⟨340903705625807693754251477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 909076548335487183344670605 340903705625807693754251477)
            ·
              refine ⟨7989930600604867822365269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 340903705625807693754251477 7989930600604867822365269)
              ·
                refine ⟨93631999225838294793343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7989930600604867822365269 93631999225838294793343)
                ·
                  rfl

theorem cell23_4923387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 8].length) (baseStart_4923387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923387 prefixEnd_4923387 := by exact prefixLift 4923387
  have htrace : WordTrace (prefixWord ++ tailWord_4923387) baseStart_4923387 baseEnd_4923387 := by
    simpa [prefixWord, tailWord_4923387, baseEnd_4923387] using wordTrace_append hprefix tailTrace_4923387
  have hstable : (prefixWord ++ tailWord_4923387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923387).length < 2 ^ (prefixWord ++ tailWord_4923387).sum := by decide
  have hdescent : baseEnd_4923387 < baseStart_4923387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923404 : List Nat := [2, 2, 1, 2, 3, 1, 5, 7]
def baseStart_4923404 : Nat := 118140960795 + 4923404 * 2 ^ 59
def prefixEnd_4923404 : Nat := 4983230072969 + 3 ^ 40 * 4923404 * 2
def baseEnd_4923404 : Nat := 93632322528472607144729

theorem tailTrace_4923404 : CollatzResearch.WordTrace tailWord_4923404 prefixEnd_4923404 93632322528472607144729 := by
  unfold tailWord_4923404
  simp only [CollatzResearch.WordTrace]
  refine ⟨89785648127677816652392633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119714197503570422203190177 89785648127677816652392633)
  ·
    refine ⟨67339236095758362489294475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89785648127677816652392633 67339236095758362489294475)
    ·
      refine ⟨101008854143637543733941713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67339236095758362489294475 101008854143637543733941713)
      ·
        refine ⟨75756640607728157800456285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101008854143637543733941713 75756640607728157800456285)
        ·
          refine ⟨28408740227898059175171107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75756640607728157800456285 28408740227898059175171107)
          ·
            refine ⟨42613110341847088762756661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28408740227898059175171107 42613110341847088762756661)
            ·
              refine ⟨3994979094548164571508437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42613110341847088762756661 3994979094548164571508437)
              ·
                refine ⟨93632322528472607144729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3994979094548164571508437 93632322528472607144729)
                ·
                  rfl

theorem cell23_4923404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 7].length) (baseStart_4923404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923404 prefixEnd_4923404 := by exact prefixLift 4923404
  have htrace : WordTrace (prefixWord ++ tailWord_4923404) baseStart_4923404 baseEnd_4923404 := by
    simpa [prefixWord, tailWord_4923404, baseEnd_4923404] using wordTrace_append hprefix tailTrace_4923404
  have hstable : (prefixWord ++ tailWord_4923404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923404).length < 2 ^ (prefixWord ++ tailWord_4923404).sum := by decide
  have hdescent : baseEnd_4923404 < baseStart_4923404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923412 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4923412 : Nat := 118140960795 + 4923412 * 2 ^ 59
def prefixEnd_4923412 : Nat := 4983230072969 + 3 ^ 40 * 4923412 * 2
def baseEnd_4923412 : Nat := 842692272037998787202549

theorem tailTrace_4923412 : CollatzResearch.WordTrace tailWord_4923412 prefixEnd_4923412 842692272037998787202549 := by
  unfold tailWord_4923412
  simp only [CollatzResearch.WordTrace]
  refine ⟨89785794019663325335538245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119714392026217767114050993 89785794019663325335538245)
  ·
    refine ⟨16834836378686873500413421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89785794019663325335538245 16834836378686873500413421)
    ·
      refine ⟨6313063642007577562655033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16834836378686873500413421 6313063642007577562655033)
      ·
        refine ⟨4734797731505683171991275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6313063642007577562655033 4734797731505683171991275)
        ·
          refine ⟨7102196597258524757986913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4734797731505683171991275 7102196597258524757986913)
          ·
            refine ⟨5326647447943893568490185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7102196597258524757986913 5326647447943893568490185)
            ·
              refine ⟨3994985585957920176367639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326647447943893568490185 3994985585957920176367639)
              ·
                refine ⟨5992478378936880264551459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994985585957920176367639 5992478378936880264551459)
                ·
                  refine ⟨8988717568405320396827189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5992478378936880264551459 8988717568405320396827189)
                  ·
                    refine ⟨842692272037998787202549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8988717568405320396827189 842692272037998787202549)
                    ·
                      rfl

theorem cell23_4923412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4923412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923412 prefixEnd_4923412 := by exact prefixLift 4923412
  have htrace : WordTrace (prefixWord ++ tailWord_4923412) baseStart_4923412 baseEnd_4923412 := by
    simpa [prefixWord, tailWord_4923412, baseEnd_4923412] using wordTrace_append hprefix tailTrace_4923412
  have hstable : (prefixWord ++ tailWord_4923412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923412).length < 2 ^ (prefixWord ++ tailWord_4923412).sum := by decide
  have hdescent : baseEnd_4923412 < baseStart_4923412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923415 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4923415 : Nat := 118140960795 + 4923415 * 2 ^ 59
def prefixEnd_4923415 : Nat := 4983230072969 + 3 ^ 40 * 4923415 * 2
def baseEnd_4923415 : Nat := 2528078356555959849870133

theorem tailTrace_4923415 : CollatzResearch.WordTrace tailWord_4923415 prefixEnd_4923415 2528078356555959849870133 := by
  unfold tailWord_4923415
  simp only [CollatzResearch.WordTrace]
  refine ⟨179571697458315782183435699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119714464972210521455623799 179571697458315782183435699)
  ·
    refine ⟨269357546187473673275153549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179571697458315782183435699 269357546187473673275153549)
    ·
      refine ⟨101009079820302627478182581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269357546187473673275153549 101009079820302627478182581)
      ·
        refine ⟨9469601233153371326079617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101009079820302627478182581 9469601233153371326079617)
        ·
          refine ⟨7102200924865028494559713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9469601233153371326079617 7102200924865028494559713)
          ·
            refine ⟨5326650693648771370919785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7102200924865028494559713 5326650693648771370919785)
            ·
              refine ⟨3994988020236578528189839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326650693648771370919785 3994988020236578528189839)
              ·
                refine ⟨5992482030354867792284759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994988020236578528189839 5992482030354867792284759)
                ·
                  refine ⟨8988723045532301688427139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5992482030354867792284759 8988723045532301688427139)
                  ·
                    refine ⟨13483084568298452532640709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8988723045532301688427139 13483084568298452532640709)
                    ·
                      refine ⟨2528078356555959849870133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13483084568298452532640709 2528078356555959849870133)
                      ·
                        rfl

theorem cell23_4923415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4923415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923415 prefixEnd_4923415 := by exact prefixLift 4923415
  have htrace : WordTrace (prefixWord ++ tailWord_4923415) baseStart_4923415 baseEnd_4923415 := by
    simpa [prefixWord, tailWord_4923415, baseEnd_4923415] using wordTrace_append hprefix tailTrace_4923415
  have hstable : (prefixWord ++ tailWord_4923415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923415).length < 2 ^ (prefixWord ++ tailWord_4923415).sum := by decide
  have hdescent : baseEnd_4923415 < baseStart_4923415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923418 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3]
def baseStart_4923418 : Nat := 118140960795 + 4923418 * 2 ^ 59
def prefixEnd_4923418 : Nat := 4983230072969 + 3 ^ 40 * 4923418 * 2
def baseEnd_4923418 : Nat := 2528079896997923338132619

theorem tailTrace_4923418 : CollatzResearch.WordTrace tailWord_4923418 prefixEnd_4923418 2528079896997923338132619 := by
  unfold tailWord_4923418
  simp only [CollatzResearch.WordTrace]
  refine ⟨44892951719326228423948727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119714537918203275797196605 44892951719326228423948727)
  ·
    refine ⟨67339427578989342635923091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44892951719326228423948727 67339427578989342635923091)
    ·
      refine ⟨101009141368484013953884637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67339427578989342635923091 101009141368484013953884637)
      ·
        refine ⟨37878428013181505232706739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101009141368484013953884637 37878428013181505232706739)
        ·
          refine ⟨56817642019772257849060109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37878428013181505232706739 56817642019772257849060109)
          ·
            refine ⟨21306615757414596693397541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56817642019772257849060109 21306615757414596693397541)
            ·
              refine ⟨3994990454515236880012039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21306615757414596693397541 3994990454515236880012039)
              ·
                refine ⟨5992485681772855320018059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994990454515236880012039 5992485681772855320018059)
                ·
                  refine ⟨8988728522659282980027089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5992485681772855320018059 8988728522659282980027089)
                  ·
                    refine ⟨6741546391994462235020317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8988728522659282980027089 6741546391994462235020317)
                    ·
                      refine ⟨2528079896997923338132619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741546391994462235020317 2528079896997923338132619)
                      ·
                        rfl

theorem cell23_4923418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_4923418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923418 prefixEnd_4923418 := by exact prefixLift 4923418
  have htrace : WordTrace (prefixWord ++ tailWord_4923418) baseStart_4923418 baseEnd_4923418 := by
    simpa [prefixWord, tailWord_4923418, baseEnd_4923418] using wordTrace_append hprefix tailTrace_4923418
  have hstable : (prefixWord ++ tailWord_4923418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923418).length < 2 ^ (prefixWord ++ tailWord_4923418).sum := by decide
  have hdescent : baseEnd_4923418 < baseStart_4923418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923425 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 2, 4]
def baseStart_4923425 : Nat := 118140960795 + 4923425 * 2 ^ 59
def prefixEnd_4923425 : Nat := 4983230072969 + 3 ^ 40 * 4923425 * 2
def baseEnd_4923425 : Nat := 842694497120834936915029

theorem tailTrace_4923425 : CollatzResearch.WordTrace tailWord_4923425 prefixEnd_4923425 842694497120834936915029 := by
  unfold tailWord_4923425
  simp only [CollatzResearch.WordTrace]
  refine ⟨179572062188279553891299729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119714708125519702594199819 179572062188279553891299729)
  ·
    refine ⟨134679046641209665418474797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179572062188279553891299729 134679046641209665418474797)
    ·
      refine ⟨50504642490453624531928049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134679046641209665418474797 50504642490453624531928049)
      ·
        refine ⟨37878481867840218398946037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50504642490453624531928049 37878481867840218398946037)
        ·
          refine ⟨3551107675110020474901191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37878481867840218398946037 3551107675110020474901191)
          ·
            refine ⟨5326661512665030712351787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551107675110020474901191 5326661512665030712351787)
            ·
              refine ⟨7989992268997546068527681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326661512665030712351787 7989992268997546068527681)
              ·
                refine ⟨5992494201748159551395761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7989992268997546068527681 5992494201748159551395761)
                ·
                  refine ⟨4494370651311119663546821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5992494201748159551395761 4494370651311119663546821)
                  ·
                    refine ⟨842694497120834936915029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494370651311119663546821 842694497120834936915029)
                    ·
                      rfl

theorem cell23_4923425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_4923425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923425 prefixEnd_4923425 := by exact prefixLift 4923425
  have htrace : WordTrace (prefixWord ++ tailWord_4923425) baseStart_4923425 baseEnd_4923425 := by
    simpa [prefixWord, tailWord_4923425, baseEnd_4923425] using wordTrace_append hprefix tailTrace_4923425
  have hstable : (prefixWord ++ tailWord_4923425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923425).length < 2 ^ (prefixWord ++ tailWord_4923425).sum := by decide
  have hdescent : baseEnd_4923425 < baseStart_4923425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923432 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4923432 : Nat := 118140960795 + 4923432 * 2 ^ 59
def prefixEnd_4923432 : Nat := 4983230072969 + 3 ^ 40 * 4923432 * 2
def baseEnd_4923432 : Nat := 2528087085727086283357555

theorem tailTrace_4923432 : CollatzResearch.WordTrace tailWord_4923432 prefixEnd_4923432 2528087085727086283357555 := by
  unfold tailWord_4923432
  simp only [CollatzResearch.WordTrace]
  refine ⟨89786158749627097043402275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119714878332836129391203033 89786158749627097043402275)
  ·
    refine ⟨134679238124440645565103413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89786158749627097043402275 134679238124440645565103413)
    ·
      refine ⟨12626178574166310521728445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134679238124440645565103413 12626178574166310521728445)
      ·
        refine ⟨4734816965312366445648167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12626178574166310521728445 4734816965312366445648167)
        ·
          refine ⟨7102225447968549668472251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4734816965312366445648167 7102225447968549668472251)
          ·
            refine ⟨10653338171952824502708377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102225447968549668472251 10653338171952824502708377)
            ·
              refine ⟨7990003628964618377031283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10653338171952824502708377 7990003628964618377031283)
              ·
                refine ⟨11985005443446927565546925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990003628964618377031283 11985005443446927565546925)
                ·
                  refine ⟨4494377041292597837080097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11985005443446927565546925 4494377041292597837080097)
                  ·
                    refine ⟨3370782780969448377810073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4494377041292597837080097 3370782780969448377810073)
                    ·
                      refine ⟨2528087085727086283357555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370782780969448377810073 2528087085727086283357555)
                      ·
                        rfl

theorem cell23_4923432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4923432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923432 prefixEnd_4923432 := by exact prefixLift 4923432
  have htrace : WordTrace (prefixWord ++ tailWord_4923432) baseStart_4923432 baseEnd_4923432 := by
    simpa [prefixWord, tailWord_4923432, baseEnd_4923432] using wordTrace_append hprefix tailTrace_4923432
  have hstable : (prefixWord ++ tailWord_4923432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923432).length < 2 ^ (prefixWord ++ tailWord_4923432).sum := by decide
  have hdescent : baseEnd_4923432 < baseStart_4923432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923448 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_4923448 : Nat := 118140960795 + 4923448 * 2 ^ 59
def prefixEnd_4923448 : Nat := 4983230072969 + 3 ^ 40 * 4923448 * 2
def baseEnd_4923448 : Nat := 2528095301417558220757481

theorem tailTrace_4923448 : CollatzResearch.WordTrace tailWord_4923448 prefixEnd_4923448 2528095301417558220757481 := by
  unfold tailWord_4923448
  simp only [CollatzResearch.WordTrace]
  refine ⟨89786450533598114409693499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119715267378130819212924665 89786450533598114409693499)
  ·
    refine ⟨134679675800397171614540249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89786450533598114409693499 134679675800397171614540249)
    ·
      refine ⟨101009756850297878710905187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134679675800397171614540249 101009756850297878710905187)
      ·
        refine ⟨151514635275446818066357781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101009756850297878710905187 151514635275446818066357781)
        ·
          refine ⟨7102248528536569596860521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151514635275446818066357781 7102248528536569596860521)
          ·
            refine ⟨5326686396402427197645391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7102248528536569596860521 5326686396402427197645391)
            ·
              refine ⟨7990029594603640796468087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326686396402427197645391 7990029594603640796468087)
              ·
                refine ⟨11985044391905461194702131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990029594603640796468087 11985044391905461194702131)
                ·
                  refine ⟨17977566587858191792053197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11985044391905461194702131 17977566587858191792053197)
                  ·
                    refine ⟨6741587470446821922019949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17977566587858191792053197 6741587470446821922019949)
                    ·
                      refine ⟨2528095301417558220757481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741587470446821922019949 2528095301417558220757481)
                      ·
                        rfl

theorem cell23_4923448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_4923448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923448 prefixEnd_4923448 := by exact prefixLift 4923448
  have htrace : WordTrace (prefixWord ++ tailWord_4923448) baseStart_4923448 baseEnd_4923448 := by
    simpa [prefixWord, tailWord_4923448, baseEnd_4923448] using wordTrace_append hprefix tailTrace_4923448
  have hstable : (prefixWord ++ tailWord_4923448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923448).length < 2 ^ (prefixWord ++ tailWord_4923448).sum := by decide
  have hdescent : baseEnd_4923448 < baseStart_4923448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923488 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 4, 2, 2]
def baseStart_4923488 : Nat := 118140960795 + 4923488 * 2 ^ 59
def prefixEnd_4923488 : Nat := 4983230072969 + 3 ^ 40 * 4923488 * 2
def baseEnd_4923488 : Nat := 2528115840643738064257297

theorem tailTrace_4923488 : CollatzResearch.WordTrace tailWord_4923488 prefixEnd_4923488 2528115840643738064257297 := by
  unfold tailWord_4923488
  simp only [CollatzResearch.WordTrace]
  refine ⟨89787179993525657825421559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119716239991367543767228745 89787179993525657825421559)
  ·
    refine ⟨134680769990288486738132339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89787179993525657825421559 134680769990288486738132339)
    ·
      refine ⟨202021154985432730107198509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134680769990288486738132339 202021154985432730107198509)
      ·
        refine ⟨75757933119537273790199441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202021154985432730107198509 75757933119537273790199441)
        ·
          refine ⟨56818449839652955342649581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75757933119537273790199441 56818449839652955342649581)
          ·
            refine ⟨21306918689869858253493593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56818449839652955342649581 21306918689869858253493593)
            ·
              refine ⟨15980189017402393690120195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21306918689869858253493593 15980189017402393690120195)
              ·
                refine ⟨23970283526103590535180293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15980189017402393690120195 23970283526103590535180293)
                ·
                  refine ⟨4494428161144423225346305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23970283526103590535180293 4494428161144423225346305)
                  ·
                    refine ⟨3370821120858317419009729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4494428161144423225346305 3370821120858317419009729)
                    ·
                      refine ⟨2528115840643738064257297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370821120858317419009729 2528115840643738064257297)
                      ·
                        rfl

theorem cell23_4923488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_4923488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923488 prefixEnd_4923488 := by exact prefixLift 4923488
  have htrace : WordTrace (prefixWord ++ tailWord_4923488) baseStart_4923488 baseEnd_4923488 := by
    simpa [prefixWord, tailWord_4923488, baseEnd_4923488] using wordTrace_append hprefix tailTrace_4923488
  have hstable : (prefixWord ++ tailWord_4923488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923488).length < 2 ^ (prefixWord ++ tailWord_4923488).sum := by decide
  have hdescent : baseEnd_4923488 < baseStart_4923488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923551 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4923551 : Nat := 118140960795 + 4923551 * 2 ^ 59
def prefixEnd_4923551 : Nat := 4983230072969 + 3 ^ 40 * 4923551 * 2
def baseEnd_4923551 : Nat := 2528148189924971317769507

theorem tailTrace_4923551 : CollatzResearch.WordTrace tailWord_4923551 prefixEnd_4923551 2528148189924971317769507 := by
  unfold tailWord_4923551
  simp only [CollatzResearch.WordTrace]
  refine ⟨179576657785823077410386507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119717771857215384940257671 179576657785823077410386507)
  ·
    refine ⟨269364986678734616115579761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179576657785823077410386507 269364986678734616115579761)
    ·
      refine ⟨202023740009050962086684821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269364986678734616115579761 202023740009050962086684821)
      ·
        refine ⟨9469862812924263847813351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 202023740009050962086684821 9469862812924263847813351)
        ·
          refine ⟨14204794219386395771720027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9469862812924263847813351 14204794219386395771720027)
          ·
            refine ⟨21307191329079593657580041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14204794219386395771720027 21307191329079593657580041)
            ·
              refine ⟨15980393496809695243185031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21307191329079593657580041 15980393496809695243185031)
              ·
                refine ⟨23970590245214542864777547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15980393496809695243185031 23970590245214542864777547)
                ·
                  refine ⟨35955885367821814297166321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23970590245214542864777547 35955885367821814297166321)
                  ·
                    refine ⟨26966914025866360722874741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35955885367821814297166321 26966914025866360722874741)
                    ·
                      refine ⟨2528148189924971317769507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26966914025866360722874741 2528148189924971317769507)
                      ·
                        rfl

theorem cell23_4923551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4923551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923551 prefixEnd_4923551 := by exact prefixLift 4923551
  have htrace : WordTrace (prefixWord ++ tailWord_4923551) baseStart_4923551 baseEnd_4923551 := by
    simpa [prefixWord, tailWord_4923551, baseEnd_4923551] using wordTrace_append hprefix tailTrace_4923551
  have hstable : (prefixWord ++ tailWord_4923551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923551).length < 2 ^ (prefixWord ++ tailWord_4923551).sum := by decide
  have hdescent : baseEnd_4923551 < baseStart_4923551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923601 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 6]
def baseStart_4923601 : Nat := 118140960795 + 4923601 * 2 ^ 59
def prefixEnd_4923601 : Nat := 4983230072969 + 3 ^ 40 * 4923601 * 2
def baseEnd_4923601 : Nat := 280908207106410680238253

theorem tailTrace_4923601 : CollatzResearch.WordTrace tailWord_4923601 prefixEnd_4923601 280908207106410680238253 := by
  unfold tailWord_4923601
  simp only [CollatzResearch.WordTrace]
  refine ⟨179578481435641935949706657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119718987623761290633137771 179578481435641935949706657)
  ·
    refine ⟨134683861076731451962279993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179578481435641935949706657 134683861076731451962279993)
    ·
      refine ⟨101012895807548588971709995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134683861076731451962279993 101012895807548588971709995)
      ·
        refine ⟨151519343711322883457564993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101012895807548588971709995 151519343711322883457564993)
        ·
          refine ⟨113639507783492162593173745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151519343711322883457564993 113639507783492162593173745)
          ·
            refine ⟨85229630837619121944880309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113639507783492162593173745 85229630837619121944880309)
            ·
              refine ⟨7990277891026792682332529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85229630837619121944880309 7990277891026792682332529)
              ·
                refine ⟨5992708418270094511749397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7990277891026792682332529 5992708418270094511749397)
                ·
                  refine ⟨280908207106410680238253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5992708418270094511749397 280908207106410680238253)
                  ·
                    rfl

theorem cell23_4923601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 6].length) (baseStart_4923601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923601 prefixEnd_4923601 := by exact prefixLift 4923601
  have htrace : WordTrace (prefixWord ++ tailWord_4923601) baseStart_4923601 baseEnd_4923601 := by
    simpa [prefixWord, tailWord_4923601, baseEnd_4923601] using wordTrace_append hprefix tailTrace_4923601
  have hstable : (prefixWord ++ tailWord_4923601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923601).length < 2 ^ (prefixWord ++ tailWord_4923601).sum := by decide
  have hdescent : baseEnd_4923601 < baseStart_4923601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923605 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_4923605 : Nat := 118140960795 + 4923605 * 2 ^ 59
def prefixEnd_4923605 : Nat := 4983230072969 + 3 ^ 40 * 4923605 * 2
def baseEnd_4923605 : Nat := 842725305960104702164753

theorem tailTrace_4923605 : CollatzResearch.WordTrace tailWord_4923605 prefixEnd_4923605 842725305960104702164753 := by
  unfold tailWord_4923605
  simp only [CollatzResearch.WordTrace]
  refine ⟨179578627327627444632852269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119719084885084963088568179 179578627327627444632852269)
  ·
    refine ⟨67341985247860291737319601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179578627327627444632852269 67341985247860291737319601)
    ·
      refine ⟨50506488935895218802989701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67341985247860291737319601 50506488935895218802989701)
      ·
        refine ⟨9469966675480353525560569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50506488935895218802989701 9469966675480353525560569)
        ·
          refine ⟨7102475006610265144170427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9469966675480353525560569 7102475006610265144170427)
          ·
            refine ⟨10653712509915397716255641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102475006610265144170427 10653712509915397716255641)
            ·
              refine ⟨7990284382436548287191731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10653712509915397716255641 7990284382436548287191731)
              ·
                refine ⟨11985426573654822430787597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990284382436548287191731 11985426573654822430787597)
                ·
                  refine ⟨4494534965120558411545349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11985426573654822430787597 4494534965120558411545349)
                  ·
                    refine ⟨842725305960104702164753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494534965120558411545349 842725305960104702164753)
                    ·
                      rfl

theorem cell23_4923605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_4923605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923605 prefixEnd_4923605 := by exact prefixLift 4923605
  have htrace : WordTrace (prefixWord ++ tailWord_4923605) baseStart_4923605 baseEnd_4923605 := by
    simpa [prefixWord, tailWord_4923605, baseEnd_4923605] using wordTrace_append hprefix tailTrace_4923605
  have hstable : (prefixWord ++ tailWord_4923605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923605).length < 2 ^ (prefixWord ++ tailWord_4923605).sum := by decide
  have hdescent : baseEnd_4923605 < baseStart_4923605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923628 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_4923628 : Nat := 118140960795 + 4923628 * 2 ^ 59
def prefixEnd_4923628 : Nat := 4983230072969 + 3 ^ 40 * 4923628 * 2
def baseEnd_4923628 : Nat := 2528187727935367516506653

theorem tailTrace_4923628 : CollatzResearch.WordTrace tailWord_4923628 prefixEnd_4923628 2528187727935367516506653 := by
  unfold tailWord_4923628
  simp only [CollatzResearch.WordTrace]
  refine ⟨89789733103272059780469769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119719644137696079707293025 89789733103272059780469769)
  ·
    refine ⟨67342299827454044835352327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89789733103272059780469769 67342299827454044835352327)
    ·
      refine ⟨101013449741181067253028491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67342299827454044835352327 101013449741181067253028491)
      ·
        refine ⟨151520174611771600879542737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101013449741181067253028491 151520174611771600879542737)
        ·
          refine ⟨113640130958828700659657053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151520174611771600879542737 113640130958828700659657053)
          ·
            refine ⟨42615049109560762747371395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113640130958828700659657053 42615049109560762747371395)
            ·
              refine ⟨63922573664341144121057093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42615049109560762747371395 63922573664341144121057093)
              ·
                refine ⟨11985482562063964522698205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63922573664341144121057093 11985482562063964522698205)
                ·
                  refine ⟨4494555960773986696011827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11985482562063964522698205 4494555960773986696011827)
                  ·
                    refine ⟨6741833941160980044017741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4494555960773986696011827 6741833941160980044017741)
                    ·
                      refine ⟨2528187727935367516506653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741833941160980044017741 2528187727935367516506653)
                      ·
                        rfl

theorem cell23_4923628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_4923628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923628 prefixEnd_4923628 := by exact prefixLift 4923628
  have htrace : WordTrace (prefixWord ++ tailWord_4923628) baseStart_4923628 baseEnd_4923628 := by
    simpa [prefixWord, tailWord_4923628, baseEnd_4923628] using wordTrace_append hprefix tailTrace_4923628
  have hstable : (prefixWord ++ tailWord_4923628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923628).length < 2 ^ (prefixWord ++ tailWord_4923628).sum := by decide
  have hdescent : baseEnd_4923628 < baseStart_4923628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923681 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4923681 : Nat := 118140960795 + 4923681 * 2 ^ 59
def prefixEnd_4923681 : Nat := 4983230072969 + 3 ^ 40 * 4923681 * 2
def baseEnd_4923681 : Nat := 2528214942410055809143909

theorem tailTrace_4923681 : CollatzResearch.WordTrace tailWord_4923681 prefixEnd_4923681 2528214942410055809143909 := by
  unfold tailWord_4923681
  simp only [CollatzResearch.WordTrace]
  refine ⟨179581399275352109612618897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119720932850234739741745931 179581399275352109612618897)
  ·
    refine ⟨134686049456514082209464173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179581399275352109612618897 134686049456514082209464173)
    ·
      refine ⟨50507268546192780828549065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134686049456514082209464173 50507268546192780828549065)
      ·
        refine ⟨37880451409644585621411799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50507268546192780828549065 37880451409644585621411799)
        ·
          refine ⟨56820677114466878432117699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37880451409644585621411799 56820677114466878432117699)
          ·
            refine ⟨85231015671700317648176549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56820677114466878432117699 85231015671700317648176549)
            ·
              refine ⟨15980815438443809559033103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85231015671700317648176549 15980815438443809559033103)
              ·
                refine ⟨23971223157665714338549655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15980815438443809559033103 23971223157665714338549655)
                ·
                  refine ⟨35956834736498571507824483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23971223157665714338549655 35956834736498571507824483)
                  ·
                    refine ⟨53935252104747857261736725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35956834736498571507824483 53935252104747857261736725)
                    ·
                      refine ⟨2528214942410055809143909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53935252104747857261736725 2528214942410055809143909)
                      ·
                        rfl

theorem cell23_4923681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4923681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923681 prefixEnd_4923681 := by exact prefixLift 4923681
  have htrace : WordTrace (prefixWord ++ tailWord_4923681) baseStart_4923681 baseEnd_4923681 := by
    simpa [prefixWord, tailWord_4923681, baseEnd_4923681] using wordTrace_append hprefix tailTrace_4923681
  have hstable : (prefixWord ++ tailWord_4923681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923681).length < 2 ^ (prefixWord ++ tailWord_4923681).sum := by decide
  have hdescent : baseEnd_4923681 < baseStart_4923681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923705 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4923705 : Nat := 118140960795 + 4923705 * 2 ^ 59
def prefixEnd_4923705 : Nat := 4983230072969 + 3 ^ 40 * 4923705 * 2
def baseEnd_4923705 : Nat := 2528227265945763715243799

theorem tailTrace_4923705 : CollatzResearch.WordTrace tailWord_4923705 prefixEnd_4923705 2528227265945763715243799 := by
  unfold tailWord_4923705
  simp only [CollatzResearch.WordTrace]
  refine ⟨179582274627265161711492569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119721516418176774474328379 179582274627265161711492569)
  ·
    refine ⟨134686705970448871283619427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179582274627265161711492569 134686705970448871283619427)
    ·
      refine ⟨202030058955673306925429141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134686705970448871283619427 202030058955673306925429141)
      ·
        refine ⟨9470159013547186262129491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 202030058955673306925429141 9470159013547186262129491)
        ·
          refine ⟨14205238520320779393194237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9470159013547186262129491 14205238520320779393194237)
          ·
            refine ⟨5326964445120292272447839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14205238520320779393194237 5326964445120292272447839)
            ·
              refine ⟨7990446667680438408671759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326964445120292272447839 7990446667680438408671759)
              ·
                refine ⟨11985670001520657613007639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990446667680438408671759 11985670001520657613007639)
                ·
                  refine ⟨17978505002280986419511459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11985670001520657613007639 17978505002280986419511459)
                  ·
                    refine ⟨26967757503421479629267189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17978505002280986419511459 26967757503421479629267189)
                    ·
                      refine ⟨2528227265945763715243799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26967757503421479629267189 2528227265945763715243799)
                      ·
                        rfl

theorem cell23_4923705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4923705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923705 prefixEnd_4923705 := by exact prefixLift 4923705
  have htrace : WordTrace (prefixWord ++ tailWord_4923705) baseStart_4923705 baseEnd_4923705 := by
    simpa [prefixWord, tailWord_4923705, baseEnd_4923705] using wordTrace_append hprefix tailTrace_4923705
  have hstable : (prefixWord ++ tailWord_4923705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923705).length < 2 ^ (prefixWord ++ tailWord_4923705).sum := by decide
  have hdescent : baseEnd_4923705 < baseStart_4923705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923713 : List Nat := [1, 2, 5, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4923713 : Nat := 118140960795 + 4923713 * 2 ^ 59
def prefixEnd_4923713 : Nat := 4983230072969 + 3 ^ 40 * 4923713 * 2
def baseEnd_4923713 : Nat := 2528231373790999683943763

theorem tailTrace_4923713 : CollatzResearch.WordTrace tailWord_4923713 prefixEnd_4923713 2528231373790999683943763 := by
  unfold tailWord_4923713
  simp only [CollatzResearch.WordTrace]
  refine ⟨179582566411236179077783793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119721710940824119385189195 179582566411236179077783793)
  ·
    refine ⟨134686924808427134308337845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179582566411236179077783793 134686924808427134308337845)
    ·
      refine ⟨12626899200790043841406673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134686924808427134308337845 12626899200790043841406673)
      ·
        refine ⟨9470174400592532881055005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12626899200790043841406673 9470174400592532881055005)
        ·
          refine ⟨3551315400222199830395627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9470174400592532881055005 3551315400222199830395627)
          ·
            refine ⟨5326973100333299745593441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551315400222199830395627 5326973100333299745593441)
            ·
              refine ⟨3995229825249974809195081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326973100333299745593441 3995229825249974809195081)
              ·
                refine ⟨2996422368937481106896311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3995229825249974809195081 2996422368937481106896311)
                ·
                  refine ⟨4494633553406221660344467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996422368937481106896311 4494633553406221660344467)
                  ·
                    refine ⟨6741950330109332490516701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4494633553406221660344467 6741950330109332490516701)
                    ·
                      refine ⟨2528231373790999683943763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741950330109332490516701 2528231373790999683943763)
                      ·
                        rfl

theorem cell23_4923713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4923713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923713 prefixEnd_4923713 := by exact prefixLift 4923713
  have htrace : WordTrace (prefixWord ++ tailWord_4923713) baseStart_4923713 baseEnd_4923713 := by
    simpa [prefixWord, tailWord_4923713, baseEnd_4923713] using wordTrace_append hprefix tailTrace_4923713
  have hstable : (prefixWord ++ tailWord_4923713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923713).length < 2 ^ (prefixWord ++ tailWord_4923713).sum := by decide
  have hdescent : baseEnd_4923713 < baseStart_4923713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923735 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_4923735 : Nat := 118140960795 + 4923735 * 2 ^ 59
def prefixEnd_4923735 : Nat := 4983230072969 + 3 ^ 40 * 4923735 * 2
def baseEnd_4923735 : Nat := 2528242670365398597868661

theorem tailTrace_4923735 : CollatzResearch.WordTrace tailWord_4923735 prefixEnd_4923735 2528242670365398597868661 := by
  unfold tailWord_4923735
  simp only [CollatzResearch.WordTrace]
  refine ⟨179583368817156476835084659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119722245878104317890056439 179583368817156476835084659)
  ·
    refine ⟨269375053225734715252626989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179583368817156476835084659 269375053225734715252626989)
    ·
      refine ⟨101015644959650518219735121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269375053225734715252626989 101015644959650518219735121)
      ·
        refine ⟨75761733719737888664801341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101015644959650518219735121 75761733719737888664801341)
        ·
          refine ⟨28410650144901708249300503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75761733719737888664801341 28410650144901708249300503)
          ·
            refine ⟨42615975217352562373950755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28410650144901708249300503 42615975217352562373950755)
            ·
              refine ⟨63923962826028843560926133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42615975217352562373950755 63923962826028843560926133)
              ·
                refine ⟨5992871514940204083836825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63923962826028843560926133 5992871514940204083836825)
                ·
                  refine ⟨4494653636205153062877619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5992871514940204083836825 4494653636205153062877619)
                  ·
                    refine ⟨6741980454307729594316429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4494653636205153062877619 6741980454307729594316429)
                    ·
                      refine ⟨2528242670365398597868661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6741980454307729594316429 2528242670365398597868661)
                      ·
                        rfl

theorem cell23_4923735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_4923735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923735 prefixEnd_4923735 := by exact prefixLift 4923735
  have htrace : WordTrace (prefixWord ++ tailWord_4923735) baseStart_4923735 baseEnd_4923735 := by
    simpa [prefixWord, tailWord_4923735, baseEnd_4923735] using wordTrace_append hprefix tailTrace_4923735
  have hstable : (prefixWord ++ tailWord_4923735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923735).length < 2 ^ (prefixWord ++ tailWord_4923735).sum := by decide
  have hdescent : baseEnd_4923735 < baseStart_4923735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923761 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_4923761 : Nat := 118140960795 + 4923761 * 2 ^ 59
def prefixEnd_4923761 : Nat := 4983230072969 + 3 ^ 40 * 4923761 * 2
def baseEnd_4923761 : Nat := 2528256020862415496143541

theorem tailTrace_4923761 : CollatzResearch.WordTrace tailWord_4923761 prefixEnd_4923761 2528256020862415496143541 := by
  unfold tailWord_4923761
  simp only [CollatzResearch.WordTrace]
  refine ⟨179584317115062283275531137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119722878076708188850354091 179584317115062283275531137)
  ·
    refine ⟨134688237836296712456648353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179584317115062283275531137 134688237836296712456648353)
    ·
      refine ⟨101016178377222534342486265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134688237836296712456648353 101016178377222534342486265)
      ·
        refine ⟨75762133782916900756864699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101016178377222534342486265 75762133782916900756864699)
        ·
          refine ⟨113643200674375351135297049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75762133782916900756864699 113643200674375351135297049)
          ·
            refine ⟨85232400505781513351472787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113643200674375351135297049 85232400505781513351472787)
            ·
              refine ⟨127848600758672270027209181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85232400505781513351472787 127848600758672270027209181)
              ·
                refine ⟨47943225284502101260203443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127848600758672270027209181 47943225284502101260203443)
                ·
                  refine ⟨71914837926753151890305165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47943225284502101260203443 71914837926753151890305165)
                  ·
                    refine ⟨26968064222532431958864437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71914837926753151890305165 26968064222532431958864437)
                    ·
                      refine ⟨2528256020862415496143541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26968064222532431958864437 2528256020862415496143541)
                      ·
                        rfl

theorem cell23_4923761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_4923761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923761 prefixEnd_4923761 := by exact prefixLift 4923761
  have htrace : WordTrace (prefixWord ++ tailWord_4923761) baseStart_4923761 baseEnd_4923761 := by
    simpa [prefixWord, tailWord_4923761, baseEnd_4923761] using wordTrace_append hprefix tailTrace_4923761
  have hstable : (prefixWord ++ tailWord_4923761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923761).length < 2 ^ (prefixWord ++ tailWord_4923761).sum := by decide
  have hdescent : baseEnd_4923761 < baseStart_4923761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923762 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_4923762 : Nat := 118140960795 + 4923762 * 2 ^ 59
def prefixEnd_4923762 : Nat := 4983230072969 + 3 ^ 40 * 4923762 * 2
def baseEnd_4923762 : Nat := 2528256534343069992231037

theorem tailTrace_4923762 : CollatzResearch.WordTrace tailWord_4923762 prefixEnd_4923762 2528256534343069992231037 := by
  unfold tailWord_4923762
  simp only [CollatzResearch.WordTrace]
  refine ⟨44896088397014665111579385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119722902392039106964211693 44896088397014665111579385)
  ·
    refine ⟨33672066297760998833684539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44896088397014665111579385 33672066297760998833684539)
    ·
      refine ⟨50508099446641498250526809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33672066297760998833684539 50508099446641498250526809)
      ·
        refine ⟨37881074584981123687895107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50508099446641498250526809 37881074584981123687895107)
        ·
          refine ⟨56821611877471685531842661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37881074584981123687895107 56821611877471685531842661)
          ·
            refine ⟨10654052227025941037220499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56821611877471685531842661 10654052227025941037220499)
            ·
              refine ⟨15981078340538911555830749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10654052227025941037220499 15981078340538911555830749)
              ·
                refine ⟨5992904377702091833436531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15981078340538911555830749 5992904377702091833436531)
                ·
                  refine ⟨8989356566553137750154797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5992904377702091833436531 8989356566553137750154797)
                  ·
                    refine ⟨3371008712457426656308049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8989356566553137750154797 3371008712457426656308049)
                    ·
                      refine ⟨2528256534343069992231037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371008712457426656308049 2528256534343069992231037)
                      ·
                        rfl

theorem cell23_4923762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_4923762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923762 prefixEnd_4923762 := by exact prefixLift 4923762
  have htrace : WordTrace (prefixWord ++ tailWord_4923762) baseStart_4923762 baseEnd_4923762 := by
    simpa [prefixWord, tailWord_4923762, baseEnd_4923762] using wordTrace_append hprefix tailTrace_4923762
  have hstable : (prefixWord ++ tailWord_4923762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923762).length < 2 ^ (prefixWord ++ tailWord_4923762).sum := by decide
  have hdescent : baseEnd_4923762 < baseStart_4923762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923775 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 4, 2, 2]
def baseStart_4923775 : Nat := 118140960795 + 4923775 * 2 ^ 59
def prefixEnd_4923775 : Nat := 4983230072969 + 3 ^ 40 * 4923775 * 2
def baseEnd_4923775 : Nat := 2528263209591578441368477

theorem tailTrace_4923775 : CollatzResearch.WordTrace tailWord_4923775 prefixEnd_4923775 2528263209591578441368477 := by
  unfold tailWord_4923775
  simp only [CollatzResearch.WordTrace]
  refine ⟨179584827737011563666540779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119723218491341042444360519 179584827737011563666540779)
  ·
    refine ⟨269377241605517345499811169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179584827737011563666540779 269377241605517345499811169)
    ·
      refine ⟨202032931204138009124858377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269377241605517345499811169 202032931204138009124858377)
      ·
        refine ⟨151524698403103506843643783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202032931204138009124858377 151524698403103506843643783)
        ·
          refine ⟨227287047604655260265465675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151524698403103506843643783 227287047604655260265465675)
          ·
            refine ⟨340930571406982890398198513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227287047604655260265465675 340930571406982890398198513)
            ·
              refine ⟨255697928555237167798648885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340930571406982890398198513 255697928555237167798648885)
              ·
                refine ⟨23971680802053484481123333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 255697928555237167798648885 23971680802053484481123333)
                ·
                  refine ⟨4494690150385028340210625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23971680802053484481123333 4494690150385028340210625)
                  ·
                    refine ⟨3371017612788771255157969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4494690150385028340210625 3371017612788771255157969)
                    ·
                      refine ⟨2528263209591578441368477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371017612788771255157969 2528263209591578441368477)
                      ·
                        rfl

theorem cell23_4923775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_4923775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923775 prefixEnd_4923775 := by exact prefixLift 4923775
  have htrace : WordTrace (prefixWord ++ tailWord_4923775) baseStart_4923775 baseEnd_4923775 := by
    simpa [prefixWord, tailWord_4923775, baseEnd_4923775] using wordTrace_append hprefix tailTrace_4923775
  have hstable : (prefixWord ++ tailWord_4923775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923775).length < 2 ^ (prefixWord ++ tailWord_4923775).sum := by decide
  have hdescent : baseEnd_4923775 < baseStart_4923775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923786 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4923786 : Nat := 118140960795 + 4923786 * 2 ^ 59
def prefixEnd_4923786 : Nat := 4983230072969 + 3 ^ 40 * 4923786 * 2
def baseEnd_4923786 : Nat := 2528268857878777898330927

theorem tailTrace_4923786 : CollatzResearch.WordTrace tailWord_4923786 prefixEnd_4923786 2528268857878777898330927 := by
  unfold tailWord_4923786
  simp only [CollatzResearch.WordTrace]
  refine ⟨44896307234992928136297803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119723485959981141696794141 44896307234992928136297803)
  ·
    refine ⟨67344460852489392204446705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44896307234992928136297803 67344460852489392204446705)
    ·
      refine ⟨50508345639367044153335029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67344460852489392204446705 50508345639367044153335029)
      ·
        refine ⟨4735157403690660389375159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50508345639367044153335029 4735157403690660389375159)
        ·
          refine ⟨7102736105535990584062739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735157403690660389375159 7102736105535990584062739)
          ·
            refine ⟨10654104158303985876094109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102736105535990584062739 10654104158303985876094109)
            ·
              refine ⟨3995289059363994703535291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10654104158303985876094109 3995289059363994703535291)
              ·
                refine ⟨5992933589045992055302937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3995289059363994703535291 5992933589045992055302937)
                ·
                  refine ⟨4494700191784494041477203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5992933589045992055302937 4494700191784494041477203)
                  ·
                    refine ⟨6742050287676741062215805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4494700191784494041477203 6742050287676741062215805)
                    ·
                      refine ⟨2528268857878777898330927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6742050287676741062215805 2528268857878777898330927)
                      ·
                        rfl

theorem cell23_4923786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4923786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923786 prefixEnd_4923786 := by exact prefixLift 4923786
  have htrace : WordTrace (prefixWord ++ tailWord_4923786) baseStart_4923786 baseEnd_4923786 := by
    simpa [prefixWord, tailWord_4923786, baseEnd_4923786] using wordTrace_append hprefix tailTrace_4923786
  have hstable : (prefixWord ++ tailWord_4923786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923786).length < 2 ^ (prefixWord ++ tailWord_4923786).sum := by decide
  have hdescent : baseEnd_4923786 < baseStart_4923786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923788 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_4923788 : Nat := 118140960795 + 4923788 * 2 ^ 59
def prefixEnd_4923788 : Nat := 4983230072969 + 3 ^ 40 * 4923788 * 2
def baseEnd_4923788 : Nat := 2528269884840086890505917

theorem tailTrace_4923788 : CollatzResearch.WordTrace tailWord_4923788 prefixEnd_4923788 2528269884840086890505917 := by
  unfold tailWord_4923788
  simp only [CollatzResearch.WordTrace]
  refine ⟨89792650942982233443382009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119723534590642977924509345 89792650942982233443382009)
  ·
    refine ⟨67344488207236675082536507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89792650942982233443382009 67344488207236675082536507)
    ·
      refine ⟨101016732310855012623804761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67344488207236675082536507 101016732310855012623804761)
      ·
        refine ⟨75762549233141259467853571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101016732310855012623804761 75762549233141259467853571)
        ·
          refine ⟨113643823849711889201780357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75762549233141259467853571 113643823849711889201780357)
          ·
            refine ⟨21308216971820979225333817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113643823849711889201780357 21308216971820979225333817)
            ·
              refine ⟨15981162728865734419000363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21308216971820979225333817 15981162728865734419000363)
              ·
                refine ⟨23971744093298601628500545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15981162728865734419000363 23971744093298601628500545)
                ·
                  refine ⟨17978808069973951221375409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23971744093298601628500545 17978808069973951221375409)
                  ·
                    refine ⟨13484106052480463416031557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17978808069973951221375409 13484106052480463416031557)
                    ·
                      refine ⟨2528269884840086890505917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13484106052480463416031557 2528269884840086890505917)
                      ·
                        rfl

theorem cell23_4923788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_4923788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923788 prefixEnd_4923788 := by exact prefixLift 4923788
  have htrace : WordTrace (prefixWord ++ tailWord_4923788) baseStart_4923788 baseEnd_4923788 := by
    simpa [prefixWord, tailWord_4923788, baseEnd_4923788] using wordTrace_append hprefix tailTrace_4923788
  have hstable : (prefixWord ++ tailWord_4923788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923788).length < 2 ^ (prefixWord ++ tailWord_4923788).sum := by decide
  have hdescent : baseEnd_4923788 < baseStart_4923788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923838 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4923838 : Nat := 118140960795 + 4923838 * 2 ^ 59
def prefixEnd_4923838 : Nat := 4983230072969 + 3 ^ 40 * 4923838 * 2
def baseEnd_4923838 : Nat := 2528295558872811694880687

theorem tailTrace_4923838 : CollatzResearch.WordTrace tailWord_4923838 prefixEnd_4923838 2528295558872811694880687 := by
  unfold tailWord_4923838
  simp only [CollatzResearch.WordTrace]
  refine ⟨22448390691972915678260521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119724750357188883617389445 22448390691972915678260521)
  ·
    refine ⟨16836293018979686758695391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22448390691972915678260521 16836293018979686758695391)
    ·
      refine ⟨25254439528469530138043087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16836293018979686758695391 25254439528469530138043087)
      ·
        refine ⟨37881659292704295207064631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25254439528469530138043087 37881659292704295207064631)
        ·
          refine ⟨56822488939056442810596947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37881659292704295207064631 56822488939056442810596947)
          ·
            refine ⟨85233733408584664215895421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56822488939056442810596947 85233733408584664215895421)
            ·
              refine ⟨31962650028219249080960783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85233733408584664215895421 31962650028219249080960783)
              ·
                refine ⟨47943975042328873621441175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31962650028219249080960783 47943975042328873621441175)
                ·
                  refine ⟨71915962563493310432161763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47943975042328873621441175 71915962563493310432161763)
                  ·
                    refine ⟨107873943845239965648242645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71915962563493310432161763 107873943845239965648242645)
                    ·
                      refine ⟨2528295558872811694880687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107873943845239965648242645 2528295558872811694880687)
                      ·
                        rfl

theorem cell23_4923838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4923838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923838 prefixEnd_4923838 := by exact prefixLift 4923838
  have htrace : WordTrace (prefixWord ++ tailWord_4923838) baseStart_4923838 baseEnd_4923838 := by
    simpa [prefixWord, tailWord_4923838, baseEnd_4923838] using wordTrace_append hprefix tailTrace_4923838
  have hstable : (prefixWord ++ tailWord_4923838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923838).length < 2 ^ (prefixWord ++ tailWord_4923838).sum := by decide
  have hdescent : baseEnd_4923838 < baseStart_4923838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923862 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_4923862 : Nat := 118140960795 + 4923862 * 2 ^ 59
def prefixEnd_4923862 : Nat := 4983230072969 + 3 ^ 40 * 4923862 * 2
def baseEnd_4923862 : Nat := 842769294136173200326859

theorem tailTrace_4923862 : CollatzResearch.WordTrace tailWord_4923862 prefixEnd_4923862 842769294136173200326859 := by
  unfold tailWord_4923862
  simp only [CollatzResearch.WordTrace]
  refine ⟨11224250055481023595309865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119725333925130918349971893 11224250055481023595309865)
  ·
    refine ⟨8418187541610767696482399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11224250055481023595309865 8418187541610767696482399)
    ·
      refine ⟨12627281312416151544723599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418187541610767696482399 12627281312416151544723599)
      ·
        refine ⟨18940921968624227317085399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12627281312416151544723599 18940921968624227317085399)
        ·
          refine ⟨28411382952936340975628099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18940921968624227317085399 28411382952936340975628099)
          ·
            refine ⟨42617074429404511463442149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28411382952936340975628099 42617074429404511463442149)
            ·
              refine ⟨7990701455513345899395403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42617074429404511463442149 7990701455513345899395403)
              ·
                refine ⟨11986052183270018849093105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990701455513345899395403 11986052183270018849093105)
                ·
                  refine ⟨8989539137452514136819829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11986052183270018849093105 8989539137452514136819829)
                  ·
                    refine ⟨842769294136173200326859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8989539137452514136819829 842769294136173200326859)
                    ·
                      rfl

theorem cell23_4923862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_4923862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923862 prefixEnd_4923862 := by exact prefixLift 4923862
  have htrace : WordTrace (prefixWord ++ tailWord_4923862) baseStart_4923862 baseEnd_4923862 := by
    simpa [prefixWord, tailWord_4923862, baseEnd_4923862] using wordTrace_append hprefix tailTrace_4923862
  have hstable : (prefixWord ++ tailWord_4923862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923862).length < 2 ^ (prefixWord ++ tailWord_4923862).sum := by decide
  have hdescent : baseEnd_4923862 < baseStart_4923862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923865 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 4]
def baseStart_4923865 : Nat := 118140960795 + 4923865 * 2 ^ 59
def prefixEnd_4923865 : Nat := 4983230072969 + 3 ^ 40 * 4923865 * 2
def baseEnd_4923865 : Nat := 2528309422850483089243063

theorem tailTrace_4923865 : CollatzResearch.WordTrace tailWord_4923865 prefixEnd_4923865 2528309422850483089243063 := by
  unfold tailWord_4923865
  simp only [CollatzResearch.WordTrace]
  refine ⟨179588110306685509037317049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119725406871123672691544699 179588110306685509037317049)
  ·
    refine ⟨134691082730014131777987787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179588110306685509037317049 134691082730014131777987787)
    ·
      refine ⟨202036624095021197666981681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134691082730014131777987787 202036624095021197666981681)
      ·
        refine ⟨151527468071265898250236261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202036624095021197666981681 151527468071265898250236261)
        ·
          refine ⟨28411400263362355921919299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151527468071265898250236261 28411400263362355921919299)
          ·
            refine ⟨42617100395043533882878949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28411400263362355921919299 42617100395043533882878949)
            ·
              refine ⟨7990706324070662603039803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42617100395043533882878949 7990706324070662603039803)
              ·
                refine ⟨11986059486105993904559705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990706324070662603039803 11986059486105993904559705)
                ·
                  refine ⟨8989544614579495428419779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11986059486105993904559705 8989544614579495428419779)
                  ·
                    refine ⟨13484316921869243142629669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8989544614579495428419779 13484316921869243142629669)
                    ·
                      refine ⟨2528309422850483089243063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13484316921869243142629669 2528309422850483089243063)
                      ·
                        rfl

theorem cell23_4923865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_4923865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923865 prefixEnd_4923865 := by exact prefixLift 4923865
  have htrace : WordTrace (prefixWord ++ tailWord_4923865) baseStart_4923865 baseEnd_4923865 := by
    simpa [prefixWord, tailWord_4923865, baseEnd_4923865] using wordTrace_append hprefix tailTrace_4923865
  have hstable : (prefixWord ++ tailWord_4923865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923865).length < 2 ^ (prefixWord ++ tailWord_4923865).sum := by decide
  have hdescent : baseEnd_4923865 < baseStart_4923865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923905 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 6]
def baseStart_4923905 : Nat := 118140960795 + 4923905 * 2 ^ 59
def prefixEnd_4923905 : Nat := 4983230072969 + 3 ^ 40 * 4923905 * 2
def baseEnd_4923905 : Nat := 280925551341851436971431

theorem tailTrace_4923905 : CollatzResearch.WordTrace tailWord_4923905 prefixEnd_4923905 280925551341851436971431 := by
  unfold tailWord_4923905
  simp only [CollatzResearch.WordTrace]
  refine ⟨179589569226540595868773169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119726379484360397245848779 179589569226540595868773169)
  ·
    refine ⟨134692176919905446901579877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179589569226540595868773169 134692176919905446901579877)
    ·
      refine ⟨25254783172482271294046227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134692176919905446901579877 25254783172482271294046227)
      ·
        refine ⟨37882174758723406941069341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25254783172482271294046227 37882174758723406941069341)
        ·
          refine ⟨14205815534521277602901003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37882174758723406941069341 14205815534521277602901003)
          ·
            refine ⟨21308723301781916404351505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14205815534521277602901003 21308723301781916404351505)
            ·
              refine ⟨15981542476336437303263629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21308723301781916404351505 15981542476336437303263629)
              ·
                refine ⟨5993078428626163988723861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15981542476336437303263629 5993078428626163988723861)
                ·
                  refine ⟨280925551341851436971431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5993078428626163988723861 280925551341851436971431)
                  ·
                    rfl

theorem cell23_4923905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 6].length) (baseStart_4923905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923905 prefixEnd_4923905 := by exact prefixLift 4923905
  have htrace : WordTrace (prefixWord ++ tailWord_4923905) baseStart_4923905 baseEnd_4923905 := by
    simpa [prefixWord, tailWord_4923905, baseEnd_4923905] using wordTrace_append hprefix tailTrace_4923905
  have hstable : (prefixWord ++ tailWord_4923905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923905).length < 2 ^ (prefixWord ++ tailWord_4923905).sum := by decide
  have hdescent : baseEnd_4923905 < baseStart_4923905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923948 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_4923948 : Nat := 118140960795 + 4923948 * 2 ^ 59
def prefixEnd_4923948 : Nat := 4983230072969 + 3 ^ 40 * 4923948 * 2
def baseEnd_4923948 : Nat := 842784013914935421501727

theorem tailTrace_4923948 : CollatzResearch.WordTrace tailWord_4923948 prefixEnd_4923948 842784013914935421501727 := by
  unfold tailWord_4923948
  simp only [CollatzResearch.WordTrace]
  refine ⟨89795568782692407106294249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119727425043589876141725665 89795568782692407106294249)
  ·
    refine ⟨67346676587019305329720687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89795568782692407106294249 67346676587019305329720687)
    ·
      refine ⟨101020014880528957994581031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67346676587019305329720687 101020014880528957994581031)
      ·
        refine ⟨151530022320793436991871547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101020014880528957994581031 151530022320793436991871547)
        ·
          refine ⟨227295033481190155487807321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151530022320793436991871547 227295033481190155487807321)
          ·
            refine ⟨170471275110892616615855491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227295033481190155487807321 170471275110892616615855491)
            ·
              refine ⟨255706912666338924923783237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170471275110892616615855491 255706912666338924923783237)
              ·
                refine ⟨47945046124938548423209357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255706912666338924923783237 47945046124938548423209357)
                ·
                  refine ⟨17979392296851955658703509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47945046124938548423209357 17979392296851955658703509)
                  ·
                    refine ⟨842784013914935421501727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17979392296851955658703509 842784013914935421501727)
                    ·
                      rfl

theorem cell23_4923948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_4923948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923948 prefixEnd_4923948 := by exact prefixLift 4923948
  have htrace : WordTrace (prefixWord ++ tailWord_4923948) baseStart_4923948 baseEnd_4923948 := by
    simpa [prefixWord, tailWord_4923948, baseEnd_4923948] using wordTrace_append hprefix tailTrace_4923948
  have hstable : (prefixWord ++ tailWord_4923948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923948).length < 2 ^ (prefixWord ++ tailWord_4923948).sum := by decide
  have hdescent : baseEnd_4923948 < baseStart_4923948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923956 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 6]
def baseStart_4923956 : Nat := 118140960795 + 4923956 * 2 ^ 59
def prefixEnd_4923956 : Nat := 4983230072969 + 3 ^ 40 * 4923956 * 2
def baseEnd_4923956 : Nat := 280928461065560248133905

theorem tailTrace_4923956 : CollatzResearch.WordTrace tailWord_4923956 prefixEnd_4923956 280928461065560248133905 := by
  unfold tailWord_4923956
  simp only [CollatzResearch.WordTrace]
  refine ⟨89795714674677915789439861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119727619566237221052586481 89795714674677915789439861)
  ·
    refine ⟨8418348250751054605259987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89795714674677915789439861 8418348250751054605259987)
    ·
      refine ⟨12627522376126581907889981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418348250751054605259987 12627522376126581907889981)
      ·
        refine ⟨4735320891047468215458743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12627522376126581907889981 4735320891047468215458743)
        ·
          refine ⟨7102981336571202323188115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735320891047468215458743 7102981336571202323188115)
          ·
            refine ⟨10654472004856803484782173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102981336571202323188115 10654472004856803484782173)
            ·
              refine ⟨3995427001821301306793315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10654472004856803484782173 3995427001821301306793315)
              ·
                refine ⟨5993140502731951960189973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3995427001821301306793315 5993140502731951960189973)
                ·
                  refine ⟨280928461065560248133905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5993140502731951960189973 280928461065560248133905)
                  ·
                    rfl

theorem cell23_4923956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_4923956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923956 prefixEnd_4923956 := by exact prefixLift 4923956
  have htrace : WordTrace (prefixWord ++ tailWord_4923956) baseStart_4923956 baseEnd_4923956 := by
    simpa [prefixWord, tailWord_4923956, baseEnd_4923956] using wordTrace_append hprefix tailTrace_4923956
  have hstable : (prefixWord ++ tailWord_4923956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923956).length < 2 ^ (prefixWord ++ tailWord_4923956).sum := by decide
  have hdescent : baseEnd_4923956 < baseStart_4923956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4923992 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_4923992 : Nat := 118140960795 + 4923992 * 2 ^ 59
def prefixEnd_4923992 : Nat := 4983230072969 + 3 ^ 40 * 4923992 * 2
def baseEnd_4923992 : Nat := 2528374634893604092354979

theorem tailTrace_4923992 : CollatzResearch.WordTrace tailWord_4923992 prefixEnd_4923992 2528374634893604092354979 := by
  unfold tailWord_4923992
  simp only [CollatzResearch.WordTrace]
  refine ⟨89796371188612704863595115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119728494918150273151460153 89796371188612704863595115)
  ·
    refine ⟨134694556782919057295392673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89796371188612704863595115 134694556782919057295392673)
    ·
      refine ⟨101020917587189292971544505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134694556782919057295392673 101020917587189292971544505)
      ·
        refine ⟨75765688190391969728658379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101020917587189292971544505 75765688190391969728658379)
        ·
          refine ⟨113648532285587954592987569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75765688190391969728658379 113648532285587954592987569)
          ·
            refine ⟨85236399214190965944740677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113648532285587954592987569 85236399214190965944740677)
            ·
              refine ⟨15981824852660806114638877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85236399214190965944740677 15981824852660806114638877)
              ·
                refine ⟨5993184319747802292989579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15981824852660806114638877 5993184319747802292989579)
                ·
                  refine ⟨8989776479621703439484369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5993184319747802292989579 8989776479621703439484369)
                  ·
                    refine ⟨6742332359716277579613277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8989776479621703439484369 6742332359716277579613277)
                    ·
                      refine ⟨2528374634893604092354979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6742332359716277579613277 2528374634893604092354979)
                      ·
                        rfl

theorem cell23_4923992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_4923992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4923992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4923992 prefixEnd_4923992 := by exact prefixLift 4923992
  have htrace : WordTrace (prefixWord ++ tailWord_4923992) baseStart_4923992 baseEnd_4923992 := by
    simpa [prefixWord, tailWord_4923992, baseEnd_4923992] using wordTrace_append hprefix tailTrace_4923992
  have hstable : (prefixWord ++ tailWord_4923992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4923992).length < 2 ^ (prefixWord ++ tailWord_4923992).sum := by decide
  have hdescent : baseEnd_4923992 < baseStart_4923992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4923992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924016 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 2, 4]
def baseStart_4924016 : Nat := 118140960795 + 4924016 * 2 ^ 59
def prefixEnd_4924016 : Nat := 4983230072969 + 3 ^ 40 * 4924016 * 2
def baseEnd_4924016 : Nat := 842795652809770666151623

theorem tailTrace_4924016 : CollatzResearch.WordTrace tailWord_4924016 prefixEnd_4924016 842795652809770666151623 := by
  unfold tailWord_4924016
  simp only [CollatzResearch.WordTrace]
  refine ⟨89796808864569230913031951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119729078486092307884042601 89796808864569230913031951)
  ·
    refine ⟨134695213296853846369547927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89796808864569230913031951 134695213296853846369547927)
    ·
      refine ⟨202042819945280769554321891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134695213296853846369547927 202042819945280769554321891)
      ·
        refine ⟨303064229917921154331482837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202042819945280769554321891 303064229917921154331482837)
        ·
          refine ⟨7103067888701277054644129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 303064229917921154331482837 7103067888701277054644129)
          ·
            refine ⟨5327300916525957790983097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7103067888701277054644129 5327300916525957790983097)
            ·
              refine ⟨3995475687394468343237323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5327300916525957790983097 3995475687394468343237323)
              ·
                refine ⟨5993213531091702514855985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3995475687394468343237323 5993213531091702514855985)
                ·
                  refine ⟨4494910148318776886141989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5993213531091702514855985 4494910148318776886141989)
                  ·
                    refine ⟨842795652809770666151623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494910148318776886141989 842795652809770666151623)
                    ·
                      rfl

theorem cell23_4924016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 4].length) (baseStart_4924016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924016 prefixEnd_4924016 := by exact prefixLift 4924016
  have htrace : WordTrace (prefixWord ++ tailWord_4924016) baseStart_4924016 baseEnd_4924016 := by
    simpa [prefixWord, tailWord_4924016, baseEnd_4924016] using wordTrace_append hprefix tailTrace_4924016
  have hstable : (prefixWord ++ tailWord_4924016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924016).length < 2 ^ (prefixWord ++ tailWord_4924016).sum := by decide
  have hdescent : baseEnd_4924016 < baseStart_4924016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924055 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 2, 6]
def baseStart_4924055 : Nat := 118140960795 + 4924055 * 2 ^ 59
def prefixEnd_4924055 : Nat := 4983230072969 + 3 ^ 40 * 4924055 * 2
def baseEnd_4924055 : Nat := 842802328058279115289063

theorem tailTrace_4924055 : CollatzResearch.WordTrace tailWord_4924055 prefixEnd_4924055 842802328058279115289063 := by
  unfold tailWord_4924055
  simp only [CollatzResearch.WordTrace]
  refine ⟨179595040175997171486733619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119730026783998114324489079 179595040175997171486733619)
  ·
    refine ⟨269392560263995757230100429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179595040175997171486733619 269392560263995757230100429)
    ·
      refine ⟨101022210098998408961287661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269392560263995757230100429 101022210098998408961287661)
      ·
        refine ⟨37883328787124403360482873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101022210098998408961287661 37883328787124403360482873)
        ·
          refine ⟨28412496590343302520362155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37883328787124403360482873 28412496590343302520362155)
          ·
            refine ⟨42618744885514953780543233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28412496590343302520362155 42618744885514953780543233)
            ·
              refine ⟨31964058664136215335407425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42618744885514953780543233 31964058664136215335407425)
              ·
                refine ⟨23973043998102161501555569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31964058664136215335407425 23973043998102161501555569)
                ·
                  refine ⟨17979782998576621126166677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23973043998102161501555569 17979782998576621126166677)
                  ·
                    refine ⟨842802328058279115289063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17979782998576621126166677 842802328058279115289063)
                    ·
                      rfl

theorem cell23_4924055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_4924055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924055 prefixEnd_4924055 := by exact prefixLift 4924055
  have htrace : WordTrace (prefixWord ++ tailWord_4924055) baseStart_4924055 baseEnd_4924055 := by
    simpa [prefixWord, tailWord_4924055, baseEnd_4924055] using wordTrace_append hprefix tailTrace_4924055
  have hstable : (prefixWord ++ tailWord_4924055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924055).length < 2 ^ (prefixWord ++ tailWord_4924055).sum := by decide
  have hdescent : baseEnd_4924055 < baseStart_4924055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924062 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4924062 : Nat := 118140960795 + 4924062 * 2 ^ 59
def prefixEnd_4924062 : Nat := 4983230072969 + 3 ^ 40 * 4924062 * 2
def baseEnd_4924062 : Nat := 2528410578539418818479657

theorem tailTrace_4924062 : CollatzResearch.WordTrace tailWord_4924062 prefixEnd_4924062 2528410578539418818479657 := by
  unfold tailWord_4924062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22449411935871476460279805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119730196991314541121492293 22449411935871476460279805)
  ·
    refine ⟨8418529475951803672604927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22449411935871476460279805 8418529475951803672604927)
    ·
      refine ⟨12627794213927705508907391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418529475951803672604927 12627794213927705508907391)
      ·
        refine ⟨18941691320891558263361087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12627794213927705508907391 18941691320891558263361087)
        ·
          refine ⟨28412536981337337395041631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18941691320891558263361087 28412536981337337395041631)
          ·
            refine ⟨42618805472006006092562447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28412536981337337395041631 42618805472006006092562447)
            ·
              refine ⟨63928208208009009138843671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42618805472006006092562447 63928208208009009138843671)
              ·
                refine ⟨95892312312013513708265507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63928208208009009138843671 95892312312013513708265507)
                ·
                  refine ⟨143838468468020270562398261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95892312312013513708265507 143838468468020270562398261)
                  ·
                    refine ⟨13484856418876900365224837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 143838468468020270562398261 13484856418876900365224837)
                    ·
                      refine ⟨2528410578539418818479657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13484856418876900365224837 2528410578539418818479657)
                      ·
                        rfl

theorem cell23_4924062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4924062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924062 prefixEnd_4924062 := by exact prefixLift 4924062
  have htrace : WordTrace (prefixWord ++ tailWord_4924062) baseStart_4924062 baseEnd_4924062 := by
    simpa [prefixWord, tailWord_4924062, baseEnd_4924062] using wordTrace_append hprefix tailTrace_4924062
  have hstable : (prefixWord ++ tailWord_4924062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924062).length < 2 ^ (prefixWord ++ tailWord_4924062).sum := by decide
  have hdescent : baseEnd_4924062 < baseStart_4924062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924079 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 1, 4, 2]
def baseStart_4924079 : Nat := 118140960795 + 4924079 * 2 ^ 59
def prefixEnd_4924079 : Nat := 4983230072969 + 3 ^ 40 * 4924079 * 2
def baseEnd_4924079 : Nat := 2528419307710545251967079

theorem tailTrace_4924079 : CollatzResearch.WordTrace tailWord_4924079 prefixEnd_4924079 2528419307710545251967079 := by
  unfold tailWord_4924079
  simp only [CollatzResearch.WordTrace]
  refine ⟨179595915527910223585607291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119730610351940149057071527 179595915527910223585607291)
  ·
    refine ⟨269393873291865335378410937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179595915527910223585607291 269393873291865335378410937)
    ·
      refine ⟨202045404968899001533808203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269393873291865335378410937 202045404968899001533808203)
      ·
        refine ⟨303068107453348502300712305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202045404968899001533808203 303068107453348502300712305)
        ·
          refine ⟨227301080590011376725534229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303068107453348502300712305 227301080590011376725534229)
          ·
            refine ⟨10654738152656783284009417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 227301080590011376725534229 10654738152656783284009417)
            ·
              refine ⟨7991053614492587463007063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10654738152656783284009417 7991053614492587463007063)
              ·
                refine ⟨11986580421738881194510595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7991053614492587463007063 11986580421738881194510595)
                ·
                  refine ⟨17979870632608321791765893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11986580421738881194510595 17979870632608321791765893)
                  ·
                    refine ⟨3371225743614060335956105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17979870632608321791765893 3371225743614060335956105)
                    ·
                      refine ⟨2528419307710545251967079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371225743614060335956105 2528419307710545251967079)
                      ·
                        rfl

theorem cell23_4924079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4, 2].length) (baseStart_4924079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924079 prefixEnd_4924079 := by exact prefixLift 4924079
  have htrace : WordTrace (prefixWord ++ tailWord_4924079) baseStart_4924079 baseEnd_4924079 := by
    simpa [prefixWord, tailWord_4924079, baseEnd_4924079] using wordTrace_append hprefix tailTrace_4924079
  have hstable : (prefixWord ++ tailWord_4924079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924079).length < 2 ^ (prefixWord ++ tailWord_4924079).sum := by decide
  have hdescent : baseEnd_4924079 < baseStart_4924079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924145 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 2, 8]
def baseStart_4924145 : Nat := 118140960795 + 4924145 * 2 ^ 59
def prefixEnd_4924145 : Nat := 4983230072969 + 3 ^ 40 * 4924145 * 2
def baseEnd_4924145 : Nat := 842817732477913997913925

theorem tailTrace_4924145 : CollatzResearch.WordTrace tailWord_4924145 prefixEnd_4924145 842817732477913997913925 := by
  unfold tailWord_4924145
  simp only [CollatzResearch.WordTrace]
  refine ⟨179598322745671116857509889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119732215163780744571673259 179598322745671116857509889)
  ·
    refine ⟨134698742059253337643132417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179598322745671116857509889 134698742059253337643132417)
    ·
      refine ⟨101024056544440003232349313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134698742059253337643132417 101024056544440003232349313)
      ·
        refine ⟨75768042408330002424261985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101024056544440003232349313 75768042408330002424261985)
        ·
          refine ⟨56826031806247501818196489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75768042408330002424261985 56826031806247501818196489)
          ·
            refine ⟨42619523854685626363647367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56826031806247501818196489 42619523854685626363647367)
            ·
              refine ⟨63929285782028439545471051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42619523854685626363647367 63929285782028439545471051)
              ·
                refine ⟨95893928673042659318206577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63929285782028439545471051 95893928673042659318206577)
                ·
                  refine ⟨71920446504781994488654933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95893928673042659318206577 71920446504781994488654933)
                  ·
                    refine ⟨842817732477913997913925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71920446504781994488654933 842817732477913997913925)
                    ·
                      rfl

theorem cell23_4924145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_4924145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924145 prefixEnd_4924145 := by exact prefixLift 4924145
  have htrace : WordTrace (prefixWord ++ tailWord_4924145) baseStart_4924145 baseEnd_4924145 := by
    simpa [prefixWord, tailWord_4924145, baseEnd_4924145] using wordTrace_append hprefix tailTrace_4924145
  have hstable : (prefixWord ++ tailWord_4924145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924145).length < 2 ^ (prefixWord ++ tailWord_4924145).sum := by decide
  have hdescent : baseEnd_4924145 < baseStart_4924145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924152 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_4924152 : Nat := 118140960795 + 4924152 * 2 ^ 59
def prefixEnd_4924152 : Nat := 4983230072969 + 3 ^ 40 * 4924152 * 2
def baseEnd_4924152 : Nat := 2528456791798323466354243

theorem tailTrace_4924152 : CollatzResearch.WordTrace tailWord_4924152 prefixEnd_4924152 2528456791798323466354243 := by
  unfold tailWord_4924152
  simp only [CollatzResearch.WordTrace]
  refine ⟨89799289028322878526507355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119732385371097171368676473 89799289028322878526507355)
  ·
    refine ⟨134698933542484317789761033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89799289028322878526507355 134698933542484317789761033)
    ·
      refine ⟨101024200156863238342320775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134698933542484317789761033 101024200156863238342320775)
      ·
        refine ⟨151536300235294857513481163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101024200156863238342320775 151536300235294857513481163)
        ·
          refine ⟨227304450352942286270221745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151536300235294857513481163 227304450352942286270221745)
          ·
            refine ⟨170478337764706714702666309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227304450352942286270221745 170478337764706714702666309)
            ·
              refine ⟨31964688330882509006749933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170478337764706714702666309 31964688330882509006749933)
              ·
                refine ⟨11986758124080940877531225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31964688330882509006749933 11986758124080940877531225)
                ·
                  refine ⟨8990068593060705658148419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11986758124080940877531225 8990068593060705658148419)
                  ·
                    refine ⟨13485102889591058487222629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8990068593060705658148419 13485102889591058487222629)
                    ·
                      refine ⟨2528456791798323466354243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13485102889591058487222629 2528456791798323466354243)
                      ·
                        rfl

theorem cell23_4924152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_4924152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924152 prefixEnd_4924152 := by exact prefixLift 4924152
  have htrace : WordTrace (prefixWord ++ tailWord_4924152) baseStart_4924152 baseEnd_4924152 := by
    simpa [prefixWord, tailWord_4924152, baseEnd_4924152] using wordTrace_append hprefix tailTrace_4924152
  have hstable : (prefixWord ++ tailWord_4924152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924152).length < 2 ^ (prefixWord ++ tailWord_4924152).sum := by decide
  have hdescent : baseEnd_4924152 < baseStart_4924152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924165 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_4924165 : Nat := 118140960795 + 4924165 * 2 ^ 59
def prefixEnd_4924165 : Nat := 4983230072969 + 3 ^ 40 * 4924165 * 2
def baseEnd_4924165 : Nat := 2528463467046831915491683

theorem tailTrace_4924165 : CollatzResearch.WordTrace tailWord_4924165 prefixEnd_4924165 2528463467046831915491683 := by
  unfold tailWord_4924165
  simp only [CollatzResearch.WordTrace]
  refine ⟨179599052205598660273237949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119732701470399106848825299 179599052205598660273237949)
  ·
    refine ⟨67349644577099497602464231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179599052205598660273237949 67349644577099497602464231)
    ·
      refine ⟨101024466865649246403696347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67349644577099497602464231 101024466865649246403696347)
      ·
        refine ⟨151536700298473869605544521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101024466865649246403696347 151536700298473869605544521)
        ·
          refine ⟨113652525223855402204158391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151536700298473869605544521 113652525223855402204158391)
          ·
            refine ⟨170478787835783103306237587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113652525223855402204158391 170478787835783103306237587)
            ·
              refine ⟨255718181753674654959356381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170478787835783103306237587 255718181753674654959356381)
              ·
                refine ⟨95894318157627995609758643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255718181753674654959356381 95894318157627995609758643)
                ·
                  refine ⟨143841477236441993414637965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95894318157627995609758643 143841477236441993414637965)
                  ·
                    refine ⟨53940553963665747530489237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143841477236441993414637965 53940553963665747530489237)
                    ·
                      refine ⟨2528463467046831915491683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53940553963665747530489237 2528463467046831915491683)
                      ·
                        rfl

theorem cell23_4924165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_4924165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924165 prefixEnd_4924165 := by exact prefixLift 4924165
  have htrace : WordTrace (prefixWord ++ tailWord_4924165) baseStart_4924165 baseEnd_4924165 := by
    simpa [prefixWord, tailWord_4924165, baseEnd_4924165] using wordTrace_append hprefix tailTrace_4924165
  have hstable : (prefixWord ++ tailWord_4924165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924165).length < 2 ^ (prefixWord ++ tailWord_4924165).sum := by decide
  have hdescent : baseEnd_4924165 < baseStart_4924165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924175 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 8]
def baseStart_4924175 : Nat := 118140960795 + 4924175 * 2 ^ 59
def prefixEnd_4924175 : Nat := 4983230072969 + 3 ^ 40 * 4924175 * 2
def baseEnd_4924175 : Nat := 280940955761486319596293

theorem tailTrace_4924175 : CollatzResearch.WordTrace tailWord_4924175 prefixEnd_4924175 280940955761486319596293 := by
  unfold tailWord_4924175
  simp only [CollatzResearch.WordTrace]
  refine ⟨179599416935562431981101979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119732944623708287987401319 179599416935562431981101979)
  ·
    refine ⟨269399125403343647971652969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179599416935562431981101979 269399125403343647971652969)
    ·
      refine ⟨202049344052507735978739727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269399125403343647971652969 202049344052507735978739727)
      ·
        refine ⟨303074016078761603968109591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202049344052507735978739727 303074016078761603968109591)
        ·
          refine ⟨454611024118142405952164387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303074016078761603968109591 454611024118142405952164387)
          ·
            refine ⟨681916536177213608928246581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454611024118142405952164387 681916536177213608928246581)
            ·
              refine ⟨63929675266613775837023117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 681916536177213608928246581 63929675266613775837023117)
              ·
                refine ⟨23973628224980165938883669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63929675266613775837023117 23973628224980165938883669)
                ·
                  refine ⟨280940955761486319596293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23973628224980165938883669 280940955761486319596293)
                  ·
                    rfl

theorem cell23_4924175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 8].length) (baseStart_4924175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924175 prefixEnd_4924175 := by exact prefixLift 4924175
  have htrace : WordTrace (prefixWord ++ tailWord_4924175) baseStart_4924175 baseEnd_4924175 := by
    simpa [prefixWord, tailWord_4924175, baseEnd_4924175] using wordTrace_append hprefix tailTrace_4924175
  have hstable : (prefixWord ++ tailWord_4924175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924175).length < 2 ^ (prefixWord ++ tailWord_4924175).sum := by decide
  have hdescent : baseEnd_4924175 < baseStart_4924175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924206 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4924206 : Nat := 118140960795 + 4924206 * 2 ^ 59
def prefixEnd_4924206 : Nat := 4983230072969 + 3 ^ 40 * 4924206 * 2
def baseEnd_4924206 : Nat := 2528484519753666255078995

theorem tailTrace_4924206 : CollatzResearch.WordTrace tailWord_4924206 prefixEnd_4924206 2528484519753666255078995 := by
  unfold tailWord_4924206
  simp only [CollatzResearch.WordTrace]
  refine ⟨22450068449806265534435059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119733698398966749516986981 22450068449806265534435059)
  ·
    refine ⟨33675102674709398301652589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22450068449806265534435059 33675102674709398301652589)
    ·
      refine ⟨12628163503016024363119721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33675102674709398301652589 12628163503016024363119721)
      ·
        refine ⟨9471122627262018272339791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12628163503016024363119721 9471122627262018272339791)
        ·
          refine ⟨14206683940893027408509687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9471122627262018272339791 14206683940893027408509687)
          ·
            refine ⟨21310025911339541112764531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14206683940893027408509687 21310025911339541112764531)
            ·
              refine ⟨31965038867009311669146797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21310025911339541112764531 31965038867009311669146797)
              ·
                refine ⟨11986889575128491875930049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31965038867009311669146797 11986889575128491875930049)
                ·
                  refine ⟨8990167181346368906947537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11986889575128491875930049 8990167181346368906947537)
                  ·
                    refine ⟨6742625386009776680210653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8990167181346368906947537 6742625386009776680210653)
                    ·
                      refine ⟨2528484519753666255078995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6742625386009776680210653 2528484519753666255078995)
                      ·
                        rfl

theorem cell23_4924206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4924206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924206 prefixEnd_4924206 := by exact prefixLift 4924206
  have htrace : WordTrace (prefixWord ++ tailWord_4924206) baseStart_4924206 baseEnd_4924206 := by
    simpa [prefixWord, tailWord_4924206, baseEnd_4924206] using wordTrace_append hprefix tailTrace_4924206
  have hstable : (prefixWord ++ tailWord_4924206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924206).length < 2 ^ (prefixWord ++ tailWord_4924206).sum := by decide
  have hdescent : baseEnd_4924206 < baseStart_4924206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924229 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 4, 3, 2]
def baseStart_4924229 : Nat := 118140960795 + 4924229 * 2 ^ 59
def prefixEnd_4924229 : Nat := 4983230072969 + 3 ^ 40 * 4924229 * 2
def baseEnd_4924229 : Nat := 2528496329808719665091389

theorem tailTrace_4924229 : CollatzResearch.WordTrace tailWord_4924229 prefixEnd_4924229 2528496329808719665091389 := by
  unfold tailWord_4924229
  simp only [CollatzResearch.WordTrace]
  refine ⟨179601386477366799203567741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119734257651577866135711827 179601386477366799203567741)
  ·
    refine ⟨67350519929012549701337903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179601386477366799203567741 67350519929012549701337903)
    ·
      refine ⟨101025779893518824552006855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67350519929012549701337903 101025779893518824552006855)
      ·
        refine ⟨151538669840278236828010283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101025779893518824552006855 151538669840278236828010283)
        ·
          refine ⟨227308004760417355242015425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151538669840278236828010283 227308004760417355242015425)
          ·
            refine ⟨170481003570313016431511569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227308004760417355242015425 170481003570313016431511569)
            ·
              refine ⟨127860752677734762323633677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170481003570313016431511569 127860752677734762323633677)
              ·
                refine ⟨47947782254150535871362629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127860752677734762323633677 47947782254150535871362629)
                ·
                  refine ⟨8990209172653225475880493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47947782254150535871362629 8990209172653225475880493)
                  ·
                    refine ⟨3371328439744959553455185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8990209172653225475880493 3371328439744959553455185)
                    ·
                      refine ⟨2528496329808719665091389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371328439744959553455185 2528496329808719665091389)
                      ·
                        rfl

theorem cell23_4924229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_4924229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924229 prefixEnd_4924229 := by exact prefixLift 4924229
  have htrace : WordTrace (prefixWord ++ tailWord_4924229) baseStart_4924229 baseEnd_4924229 := by
    simpa [prefixWord, tailWord_4924229, baseEnd_4924229] using wordTrace_append hprefix tailTrace_4924229
  have hstable : (prefixWord ++ tailWord_4924229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924229).length < 2 ^ (prefixWord ++ tailWord_4924229).sum := by decide
  have hdescent : baseEnd_4924229 < baseStart_4924229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924259 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4924259 : Nat := 118140960795 + 4924259 * 2 ^ 59
def prefixEnd_4924259 : Nat := 4983230072969 + 3 ^ 40 * 4924259 * 2
def baseEnd_4924259 : Nat := 2528511734228354547716251

theorem tailTrace_4924259 : CollatzResearch.WordTrace tailWord_4924259 prefixEnd_4924259 2528511734228354547716251 := by
  unfold tailWord_4924259
  simp only [CollatzResearch.WordTrace]
  refine ⟨179602480667258114327159831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119734987111505409551439887 179602480667258114327159831)
  ·
    refine ⟨269403721000887171490739747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179602480667258114327159831 269403721000887171490739747)
    ·
      refine ⟨404105581501330757236109621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269403721000887171490739747 404105581501330757236109621)
      ·
        refine ⟨37884898265749758490885277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 404105581501330757236109621 37884898265749758490885277)
        ·
          refine ⟨14206836849656159434081979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37884898265749758490885277 14206836849656159434081979)
          ·
            refine ⟨21310255274484239151122969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14206836849656159434081979 21310255274484239151122969)
            ·
              refine ⟨15982691455863179363342227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21310255274484239151122969 15982691455863179363342227)
              ·
                refine ⟨23974037183794769045013341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15982691455863179363342227 23974037183794769045013341)
                ·
                  refine ⟨8990263943923038391880003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23974037183794769045013341 8990263943923038391880003)
                  ·
                    refine ⟨13485395915884557587820005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8990263943923038391880003 13485395915884557587820005)
                    ·
                      refine ⟨2528511734228354547716251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13485395915884557587820005 2528511734228354547716251)
                      ·
                        rfl

theorem cell23_4924259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4924259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924259 prefixEnd_4924259 := by exact prefixLift 4924259
  have htrace : WordTrace (prefixWord ++ tailWord_4924259) baseStart_4924259 baseEnd_4924259 := by
    simpa [prefixWord, tailWord_4924259, baseEnd_4924259] using wordTrace_append hprefix tailTrace_4924259
  have hstable : (prefixWord ++ tailWord_4924259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924259).length < 2 ^ (prefixWord ++ tailWord_4924259).sum := by decide
  have hdescent : baseEnd_4924259 < baseStart_4924259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924263 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_4924263 : Nat := 118140960795 + 4924263 * 2 ^ 59
def prefixEnd_4924263 : Nat := 4983230072969 + 3 ^ 40 * 4924263 * 2
def baseEnd_4924263 : Nat := 2528513788150972532066233

theorem tailTrace_4924263 : CollatzResearch.WordTrace tailWord_4924263 prefixEnd_4924263 2528513788150972532066233 := by
  unfold tailWord_4924263
  simp only [CollatzResearch.WordTrace]
  refine ⟨179602626559243623010305443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119735084372829082006870295 179602626559243623010305443)
  ·
    refine ⟨269403939838865434515458165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179602626559243623010305443 269403939838865434515458165)
    ·
      refine ⟨25256619359893634485824203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269403939838865434515458165 25256619359893634485824203)
      ·
        refine ⟨37884929039840451728736305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25256619359893634485824203 37884929039840451728736305)
        ·
          refine ⟨28413696779880338796552229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37884929039840451728736305 28413696779880338796552229)
          ·
            refine ⟨5327568146227563524353543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28413696779880338796552229 5327568146227563524353543)
            ·
              refine ⟨7991352219341345286530315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5327568146227563524353543 7991352219341345286530315)
              ·
                refine ⟨11987028329012017929795473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7991352219341345286530315 11987028329012017929795473)
                ·
                  refine ⟨8990271246759013447346605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11987028329012017929795473 8990271246759013447346605)
                  ·
                    refine ⟨3371351717534630042754977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8990271246759013447346605 3371351717534630042754977)
                    ·
                      refine ⟨2528513788150972532066233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371351717534630042754977 2528513788150972532066233)
                      ·
                        rfl

theorem cell23_4924263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_4924263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924263 prefixEnd_4924263 := by exact prefixLift 4924263
  have htrace : WordTrace (prefixWord ++ tailWord_4924263) baseStart_4924263 baseEnd_4924263 := by
    simpa [prefixWord, tailWord_4924263, baseEnd_4924263] using wordTrace_append hprefix tailTrace_4924263
  have hstable : (prefixWord ++ tailWord_4924263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924263).length < 2 ^ (prefixWord ++ tailWord_4924263).sum := by decide
  have hdescent : baseEnd_4924263 < baseStart_4924263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924269 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_4924269 : Nat := 118140960795 + 4924269 * 2 ^ 59
def prefixEnd_4924269 : Nat := 4983230072969 + 3 ^ 40 * 4924269 * 2
def baseEnd_4924269 : Nat := 842838956344966502863735

theorem tailTrace_4924269 : CollatzResearch.WordTrace tailWord_4924269 prefixEnd_4924269 842838956344966502863735 := by
  unfold tailWord_4924269
  simp only [CollatzResearch.WordTrace]
  refine ⟨179602845397221886035023861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119735230264814590690015907 179602845397221886035023861)
  ·
    refine ⟨16837766755989551815783487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179602845397221886035023861 16837766755989551815783487)
    ·
      refine ⟨25256650133984327723675231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16837766755989551815783487 25256650133984327723675231)
      ·
        refine ⟨37884975200976491585512847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25256650133984327723675231 37884975200976491585512847)
        ·
          refine ⟨56827462801464737378269271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37884975200976491585512847 56827462801464737378269271)
          ·
            refine ⟨85241194202197106067403907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56827462801464737378269271 85241194202197106067403907)
            ·
              refine ⟨127861791303295659101105861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85241194202197106067403907 127861791303295659101105861)
              ·
                refine ⟨23974085869367936081457349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127861791303295659101105861 23974085869367936081457349)
                ·
                  refine ⟨4495141100506488015273253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23974085869367936081457349 4495141100506488015273253)
                  ·
                    refine ⟨842838956344966502863735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4495141100506488015273253 842838956344966502863735)
                    ·
                      rfl

theorem cell23_4924269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_4924269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924269 prefixEnd_4924269 := by exact prefixLift 4924269
  have htrace : WordTrace (prefixWord ++ tailWord_4924269) baseStart_4924269 baseEnd_4924269 := by
    simpa [prefixWord, tailWord_4924269, baseEnd_4924269] using wordTrace_append hprefix tailTrace_4924269
  have hstable : (prefixWord ++ tailWord_4924269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924269).length < 2 ^ (prefixWord ++ tailWord_4924269).sum := by decide
  have hdescent : baseEnd_4924269 < baseStart_4924269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924292 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4924292 : Nat := 118140960795 + 4924292 * 2 ^ 59
def prefixEnd_4924292 : Nat := 4983230072969 + 3 ^ 40 * 4924292 * 2
def baseEnd_4924292 : Nat := 2528528679089952918603599

theorem tailTrace_4924292 : CollatzResearch.WordTrace tailWord_4924292 prefixEnd_4924292 2528528679089952918603599 := by
  unfold tailWord_4924292
  simp only [CollatzResearch.WordTrace]
  refine ⟨89801842138069280481555565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119735789517425707308740753 89801842138069280481555565)
  ·
    refine ⟨33675690801775980180583337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89801842138069280481555565 33675690801775980180583337)
    ·
      refine ⟨25256768101331985135437503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33675690801775980180583337 25256768101331985135437503)
      ·
        refine ⟨37885152151997977703156255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25256768101331985135437503 37885152151997977703156255)
        ·
          refine ⟨56827728227996966554734383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37885152151997977703156255 56827728227996966554734383)
          ·
            refine ⟨85241592341995449832101575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56827728227996966554734383 85241592341995449832101575)
            ·
              refine ⟨127862388512993174748152363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85241592341995449832101575 127862388512993174748152363)
              ·
                refine ⟨191793582769489762122228545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127862388512993174748152363 191793582769489762122228545)
                ·
                  refine ⟨143845187077117321591671409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191793582769489762122228545 143845187077117321591671409)
                  ·
                    refine ⟨107883890307837991193753557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143845187077117321591671409 107883890307837991193753557)
                    ·
                      refine ⟨2528528679089952918603599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107883890307837991193753557 2528528679089952918603599)
                      ·
                        rfl

theorem cell23_4924292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4924292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924292 prefixEnd_4924292 := by exact prefixLift 4924292
  have htrace : WordTrace (prefixWord ++ tailWord_4924292) baseStart_4924292 baseEnd_4924292 := by
    simpa [prefixWord, tailWord_4924292, baseEnd_4924292] using wordTrace_append hprefix tailTrace_4924292
  have hstable : (prefixWord ++ tailWord_4924292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924292).length < 2 ^ (prefixWord ++ tailWord_4924292).sum := by decide
  have hdescent : baseEnd_4924292 < baseStart_4924292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924293 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 3, 2, 2]
def baseStart_4924293 : Nat := 118140960795 + 4924293 * 2 ^ 59
def prefixEnd_4924293 : Nat := 4983230072969 + 3 ^ 40 * 4924293 * 2
def baseEnd_4924293 : Nat := 2528529192570607414691095

theorem tailTrace_4924293 : CollatzResearch.WordTrace tailWord_4924293 prefixEnd_4924293 2528529192570607414691095 := by
  unfold tailWord_4924293
  simp only [CollatzResearch.WordTrace]
  refine ⟨179603720749134938133897533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119735813832756625422598355 179603720749134938133897533)
  ·
    refine ⟨67351395280925601800211575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179603720749134938133897533 67351395280925601800211575)
    ·
      refine ⟨101027092921388402700317363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67351395280925601800211575 101027092921388402700317363)
      ·
        refine ⟨151540639382082604050476045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101027092921388402700317363 151540639382082604050476045)
        ·
          refine ⟨56827739768280976518928517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151540639382082604050476045 56827739768280976518928517)
          ·
            refine ⟨10655201206552683097299097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56827739768280976518928517 10655201206552683097299097)
            ·
              refine ⟨7991400904914512322974323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10655201206552683097299097 7991400904914512322974323)
              ·
                refine ⟨11987101357371768484461485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7991400904914512322974323 11987101357371768484461485)
                ·
                  refine ⟨4495163009014413181673057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11987101357371768484461485 4495163009014413181673057)
                  ·
                    refine ⟨3371372256760809886254793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4495163009014413181673057 3371372256760809886254793)
                    ·
                      refine ⟨2528529192570607414691095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371372256760809886254793 2528529192570607414691095)
                      ·
                        rfl

theorem cell23_4924293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_4924293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924293 prefixEnd_4924293 := by exact prefixLift 4924293
  have htrace : WordTrace (prefixWord ++ tailWord_4924293) baseStart_4924293 baseEnd_4924293 := by
    simpa [prefixWord, tailWord_4924293, baseEnd_4924293] using wordTrace_append hprefix tailTrace_4924293
  have hstable : (prefixWord ++ tailWord_4924293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924293).length < 2 ^ (prefixWord ++ tailWord_4924293).sum := by decide
  have hdescent : baseEnd_4924293 < baseStart_4924293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924306 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4924306 : Nat := 118140960795 + 4924306 * 2 ^ 59
def prefixEnd_4924306 : Nat := 4983230072969 + 3 ^ 40 * 4924306 * 2
def baseEnd_4924306 : Nat := 2528535867819115863828535

theorem tailTrace_4924306 : CollatzResearch.WordTrace tailWord_4924306 prefixEnd_4924306 2528535867819115863828535 := by
  unfold tailWord_4924306
  simp only [CollatzResearch.WordTrace]
  refine ⟨44901048724521960338530193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119736129932058560902747181 44901048724521960338530193)
  ·
    refine ⟨33675786543391470253897645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44901048724521960338530193 33675786543391470253897645)
    ·
      refine ⟨12628419953771801345211617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33675786543391470253897645 12628419953771801345211617)
      ·
        refine ⟨9471314965328851008908713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12628419953771801345211617 9471314965328851008908713)
        ·
          refine ⟨7103486223996638256681535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9471314965328851008908713 7103486223996638256681535)
          ·
            refine ⟨10655229335994957385022303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7103486223996638256681535 10655229335994957385022303)
            ·
              refine ⟨15982844003992436077533455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10655229335994957385022303 15982844003992436077533455)
              ·
                refine ⟨23974266005988654116300183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15982844003992436077533455 23974266005988654116300183)
                ·
                  refine ⟨35961399008982981174450275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23974266005988654116300183 35961399008982981174450275)
                  ·
                    refine ⟨53942098513474471761675413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35961399008982981174450275 53942098513474471761675413)
                    ·
                      refine ⟨2528535867819115863828535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53942098513474471761675413 2528535867819115863828535)
                      ·
                        rfl

theorem cell23_4924306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4924306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924306 prefixEnd_4924306 := by exact prefixLift 4924306
  have htrace : WordTrace (prefixWord ++ tailWord_4924306) baseStart_4924306 baseEnd_4924306 := by
    simpa [prefixWord, tailWord_4924306, baseEnd_4924306] using wordTrace_append hprefix tailTrace_4924306
  have hstable : (prefixWord ++ tailWord_4924306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924306).length < 2 ^ (prefixWord ++ tailWord_4924306).sum := by decide
  have hdescent : baseEnd_4924306 < baseStart_4924306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924310 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4924310 : Nat := 118140960795 + 4924310 * 2 ^ 59
def prefixEnd_4924310 : Nat := 4983230072969 + 3 ^ 40 * 4924310 * 2
def baseEnd_4924310 : Nat := 2528537921741733848178517

theorem tailTrace_4924310 : CollatzResearch.WordTrace tailWord_4924310 prefixEnd_4924310 2528537921741733848178517 := by
  unfold tailWord_4924310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11225271299379584377329149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119736227193382233358177589 11225271299379584377329149)
  ·
    refine ⟨4209476737267344141498431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11225271299379584377329149 4209476737267344141498431)
    ·
      refine ⟨6314215105901016212247647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209476737267344141498431 6314215105901016212247647)
      ·
        refine ⟨9471322658851524318371471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6314215105901016212247647 9471322658851524318371471)
        ·
          refine ⟨14206983988277286477557207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9471322658851524318371471 14206983988277286477557207)
          ·
            refine ⟨21310475982415929716335811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14206983988277286477557207 21310475982415929716335811)
            ·
              refine ⟨31965713973623894574503717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21310475982415929716335811 31965713973623894574503717)
              ·
                refine ⟨5993571370054480232719447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31965713973623894574503717 5993571370054480232719447)
                ·
                  refine ⟨8990357055081720349079171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5993571370054480232719447 8990357055081720349079171)
                  ·
                    refine ⟨13485535582622580523618757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8990357055081720349079171 13485535582622580523618757)
                    ·
                      refine ⟨2528537921741733848178517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13485535582622580523618757 2528537921741733848178517)
                      ·
                        rfl

theorem cell23_4924310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4924310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924310 prefixEnd_4924310 := by exact prefixLift 4924310
  have htrace : WordTrace (prefixWord ++ tailWord_4924310) baseStart_4924310 baseEnd_4924310 := by
    simpa [prefixWord, tailWord_4924310, baseEnd_4924310] using wordTrace_append hprefix tailTrace_4924310
  have hstable : (prefixWord ++ tailWord_4924310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924310).length < 2 ^ (prefixWord ++ tailWord_4924310).sum := by decide
  have hdescent : baseEnd_4924310 < baseStart_4924310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924333 : List Nat := [1, 5, 2, 3, 2, 1, 9]
def baseStart_4924333 : Nat := 118140960795 + 4924333 * 2 ^ 59
def prefixEnd_4924333 : Nat := 4983230072969 + 3 ^ 40 * 4924333 * 2
def baseEnd_4924333 : Nat := 31216663355515892076431

theorem tailTrace_4924333 : CollatzResearch.WordTrace tailWord_4924333 prefixEnd_4924333 31216663355515892076431 := by
  unfold tailWord_4924333
  simp only [CollatzResearch.WordTrace]
  refine ⟨179605179668990024965353653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119736786445993349976902435 179605179668990024965353653)
  ·
    refine ⟨16837985593967814840501905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179605179668990024965353653 16837985593967814840501905)
    ·
      refine ⟨12628489195475861130376429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16837985593967814840501905 12628489195475861130376429)
      ·
        refine ⟨4735683448303447923891161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12628489195475861130376429 4735683448303447923891161)
        ·
          refine ⟨3551762586227585942918371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4735683448303447923891161 3551762586227585942918371)
          ·
            refine ⟨5327643879341378914377557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551762586227585942918371 5327643879341378914377557)
            ·
              refine ⟨31216663355515892076431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5327643879341378914377557 31216663355515892076431)
              ·
                rfl

theorem cell23_4924333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 9].length) (baseStart_4924333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924333 prefixEnd_4924333 := by exact prefixLift 4924333
  have htrace : WordTrace (prefixWord ++ tailWord_4924333) baseStart_4924333 baseEnd_4924333 := by
    simpa [prefixWord, tailWord_4924333, baseEnd_4924333] using wordTrace_append hprefix tailTrace_4924333
  have hstable : (prefixWord ++ tailWord_4924333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924333).length < 2 ^ (prefixWord ++ tailWord_4924333).sum := by decide
  have hdescent : baseEnd_4924333 < baseStart_4924333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924370 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_4924370 : Nat := 118140960795 + 4924370 * 2 ^ 59
def prefixEnd_4924370 : Nat := 4983230072969 + 3 ^ 40 * 4924370 * 2
def baseEnd_4924370 : Nat := 2528568730581003613428241

theorem tailTrace_4924370 : CollatzResearch.WordTrace tailWord_4924370 prefixEnd_4924370 2528568730581003613428241 := by
  unfold tailWord_4924370
  simp only [CollatzResearch.WordTrace]
  refine ⟨44901632292463995071112641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119737686113237320189633709 44901632292463995071112641)
  ·
    refine ⟨33676224219347996303334481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44901632292463995071112641 33676224219347996303334481)
    ·
      refine ⟨25257168164510997227500861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33676224219347996303334481 25257168164510997227500861)
      ·
        refine ⟨9471438061691623960312823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25257168164510997227500861 9471438061691623960312823)
        ·
          refine ⟨14207157092537435940469235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9471438061691623960312823 14207157092537435940469235)
          ·
            refine ⟨21310735638806153910703853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14207157092537435940469235 21310735638806153910703853)
            ·
              refine ⟨7991525864552307716513945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21310735638806153910703853 7991525864552307716513945)
              ·
                refine ⟨5993644398414230787385459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7991525864552307716513945 5993644398414230787385459)
                ·
                  refine ⟨8990466597621346181078189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5993644398414230787385459 8990466597621346181078189)
                  ·
                    refine ⟨3371424974108004817904321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8990466597621346181078189 3371424974108004817904321)
                    ·
                      refine ⟨2528568730581003613428241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371424974108004817904321 2528568730581003613428241)
                      ·
                        rfl

theorem cell23_4924370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_4924370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924370 prefixEnd_4924370 := by exact prefixLift 4924370
  have htrace : WordTrace (prefixWord ++ tailWord_4924370) baseStart_4924370 baseEnd_4924370 := by
    simpa [prefixWord, tailWord_4924370, baseEnd_4924370] using wordTrace_append hprefix tailTrace_4924370
  have hstable : (prefixWord ++ tailWord_4924370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924370).length < 2 ^ (prefixWord ++ tailWord_4924370).sum := by decide
  have hdescent : baseEnd_4924370 < baseStart_4924370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924383 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 1, 4, 2]
def baseStart_4924383 : Nat := 118140960795 + 4924383 * 2 ^ 59
def prefixEnd_4924383 : Nat := 4983230072969 + 3 ^ 40 * 4924383 * 2
def baseEnd_4924383 : Nat := 2528575405829512062565681

theorem tailTrace_4924383 : CollatzResearch.WordTrace tailWord_4924383 prefixEnd_4924383 2528575405829512062565681 := by
  unfold tailWord_4924383
  simp only [CollatzResearch.WordTrace]
  refine ⟨179607003318808883504673803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119738002212539255669782535 179607003318808883504673803)
  ·
    refine ⟨269410504978213325257010705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179607003318808883504673803 269410504978213325257010705)
    ·
      refine ⟨202057878733659993942758029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269410504978213325257010705 202057878733659993942758029)
      ·
        refine ⟨75771704525122497728534261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202057878733659993942758029 75771704525122497728534261)
        ·
          refine ⟨7103597299230234162050087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75771704525122497728534261 7103597299230234162050087)
          ·
            refine ⟨10655395948845351243075131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7103597299230234162050087 10655395948845351243075131)
            ·
              refine ⟨15983093923268026864612697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10655395948845351243075131 15983093923268026864612697)
              ·
                refine ⟨11987320442451020148459523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15983093923268026864612697 11987320442451020148459523)
                ·
                  refine ⟨17980980663676530222689285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11987320442451020148459523 17980980663676530222689285)
                  ·
                    refine ⟨3371433874439349416754241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17980980663676530222689285 3371433874439349416754241)
                    ·
                      refine ⟨2528575405829512062565681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371433874439349416754241 2528575405829512062565681)
                      ·
                        rfl

theorem cell23_4924383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_4924383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924383 prefixEnd_4924383 := by exact prefixLift 4924383
  have htrace : WordTrace (prefixWord ++ tailWord_4924383) baseStart_4924383 baseEnd_4924383 := by
    simpa [prefixWord, tailWord_4924383, baseEnd_4924383] using wordTrace_append hprefix tailTrace_4924383
  have hstable : (prefixWord ++ tailWord_4924383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924383).length < 2 ^ (prefixWord ++ tailWord_4924383).sum := by decide
  have hdescent : baseEnd_4924383 < baseStart_4924383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924469 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4924469 : Nat := 118140960795 + 4924469 * 2 ^ 59
def prefixEnd_4924469 : Nat := 4983230072969 + 3 ^ 40 * 4924469 * 2
def baseEnd_4924469 : Nat := 2528619565165798726090285

theorem tailTrace_4924469 : CollatzResearch.WordTrace tailWord_4924469 prefixEnd_4924469 2528619565165798726090285 := by
  unfold tailWord_4924469
  simp only [CollatzResearch.WordTrace]
  refine ⟨179610139996497320192304461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119740093330998213461536307 179610139996497320192304461)
  ·
    refine ⟨67353802498686495072114173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179610139996497320192304461 67353802498686495072114173)
    ·
      refine ⟨25257675937007435652042815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67353802498686495072114173 25257675937007435652042815)
      ·
        refine ⟨37886513905511153478064223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25257675937007435652042815 37886513905511153478064223)
        ·
          refine ⟨56829770858266730217096335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37886513905511153478064223 56829770858266730217096335)
          ·
            refine ⟨85244656287400095325644503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56829770858266730217096335 85244656287400095325644503)
            ·
              refine ⟨127866984431100142988466755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85244656287400095325644503 127866984431100142988466755)
              ·
                refine ⟨191800476646650214482700133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127866984431100142988466755 191800476646650214482700133)
                ·
                  refine ⟨35962589371246915215506275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191800476646650214482700133 35962589371246915215506275)
                  ·
                    refine ⟨53943884056870372823259413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35962589371246915215506275 53943884056870372823259413)
                    ·
                      refine ⟨2528619565165798726090285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53943884056870372823259413 2528619565165798726090285)
                      ·
                        rfl

theorem cell23_4924469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4924469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924469 prefixEnd_4924469 := by exact prefixLift 4924469
  have htrace : WordTrace (prefixWord ++ tailWord_4924469) baseStart_4924469 baseEnd_4924469 := by
    simpa [prefixWord, tailWord_4924469, baseEnd_4924469] using wordTrace_append hprefix tailTrace_4924469
  have hstable : (prefixWord ++ tailWord_4924469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924469).length < 2 ^ (prefixWord ++ tailWord_4924469).sum := by decide
  have hdescent : baseEnd_4924469 < baseStart_4924469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924473 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 2, 4, 2]
def baseStart_4924473 : Nat := 118140960795 + 4924473 * 2 ^ 59
def prefixEnd_4924473 : Nat := 4983230072969 + 3 ^ 40 * 4924473 * 2
def baseEnd_4924473 : Nat := 2528621619088416710440267

theorem tailTrace_4924473 : CollatzResearch.WordTrace tailWord_4924473 prefixEnd_4924473 2528621619088416710440267 := by
  unfold tailWord_4924473
  simp only [CollatzResearch.WordTrace]
  refine ⟨179610285888482828875450073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119740190592321885916966715 179610285888482828875450073)
  ·
    refine ⟨134707714416362121656587555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179610285888482828875450073 134707714416362121656587555)
    ·
      refine ⟨202061571624543182484881333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134707714416362121656587555 202061571624543182484881333)
      ·
        refine ⟨18943272339800923357957625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202061571624543182484881333 18943272339800923357957625)
        ·
          refine ⟨14207454254850692518468219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18943272339800923357957625 14207454254850692518468219)
          ·
            refine ⟨21311181382276038777702329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14207454254850692518468219 21311181382276038777702329)
            ·
              refine ⟨15983386036707029083276747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21311181382276038777702329 15983386036707029083276747)
              ·
                refine ⟨23975079055060543624915121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15983386036707029083276747 23975079055060543624915121)
                ·
                  refine ⟨17981309291295407718686341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23975079055060543624915121 17981309291295407718686341)
                  ·
                    refine ⟨3371495492117888947253689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17981309291295407718686341 3371495492117888947253689)
                    ·
                      refine ⟨2528621619088416710440267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371495492117888947253689 2528621619088416710440267)
                      ·
                        rfl

theorem cell23_4924473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_4924473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924473 prefixEnd_4924473 := by exact prefixLift 4924473
  have htrace : WordTrace (prefixWord ++ tailWord_4924473) baseStart_4924473 baseEnd_4924473 := by
    simpa [prefixWord, tailWord_4924473, baseEnd_4924473] using wordTrace_append hprefix tailTrace_4924473
  have hstable : (prefixWord ++ tailWord_4924473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924473).length < 2 ^ (prefixWord ++ tailWord_4924473).sum := by decide
  have hdescent : baseEnd_4924473 < baseStart_4924473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924476 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_4924476 : Nat := 118140960795 + 4924476 * 2 ^ 59
def prefixEnd_4924476 : Nat := 4983230072969 + 3 ^ 40 * 4924476 * 2
def baseEnd_4924476 : Nat := 2528623159530380198702753

theorem tailTrace_4924476 : CollatzResearch.WordTrace tailWord_4924476 prefixEnd_4924476 2528623159530380198702753 := by
  unfold tailWord_4924476
  simp only [CollatzResearch.WordTrace]
  refine ⟨89805197653735980193904641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119740263538314640258539521 89805197653735980193904641)
  ·
    refine ⟨67353898240301985145428481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89805197653735980193904641 67353898240301985145428481)
    ·
      refine ⟨50515423680226488859071361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67353898240301985145428481 50515423680226488859071361)
      ·
        refine ⟨37886567760169866644303521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50515423680226488859071361 37886567760169866644303521)
        ·
          refine ⟨28414925820127399983227641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37886567760169866644303521 28414925820127399983227641)
          ·
            refine ⟨21311194365095549987420731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28414925820127399983227641 21311194365095549987420731)
            ·
              refine ⟨31966791547643324981131097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21311194365095549987420731 31966791547643324981131097)
              ·
                refine ⟨23975093660732493735848323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31966791547643324981131097 23975093660732493735848323)
                ·
                  refine ⟨35962640491098740603772485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23975093660732493735848323 35962640491098740603772485)
                  ·
                    refine ⟨6742995092081013863207341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35962640491098740603772485 6742995092081013863207341)
                    ·
                      refine ⟨2528623159530380198702753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6742995092081013863207341 2528623159530380198702753)
                      ·
                        rfl

theorem cell23_4924476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_4924476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924476 prefixEnd_4924476 := by exact prefixLift 4924476
  have htrace : WordTrace (prefixWord ++ tailWord_4924476) baseStart_4924476 baseEnd_4924476 := by
    simpa [prefixWord, tailWord_4924476, baseEnd_4924476] using wordTrace_append hprefix tailTrace_4924476
  have hstable : (prefixWord ++ tailWord_4924476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924476).length < 2 ^ (prefixWord ++ tailWord_4924476).sum := by decide
  have hdescent : baseEnd_4924476 < baseStart_4924476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924493 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_4924493 : Nat := 118140960795 + 4924493 * 2 ^ 59
def prefixEnd_4924493 : Nat := 4983230072969 + 3 ^ 40 * 4924493 * 2
def baseEnd_4924493 : Nat := 2528631888701506632190175

theorem tailTrace_4924493 : CollatzResearch.WordTrace tailWord_4924493 prefixEnd_4924493 2528631888701506632190175 := by
  unfold tailWord_4924493
  simp only [CollatzResearch.WordTrace]
  refine ⟨179611015348410372291178133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119740676898940248194118755 179611015348410372291178133)
  ·
    refine ⟨8419266344456736201148975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179611015348410372291178133 8419266344456736201148975)
    ·
      refine ⟨12628899516685104301723463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8419266344456736201148975 12628899516685104301723463)
      ·
        refine ⟨18943349275027656452585195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12628899516685104301723463 18943349275027656452585195)
        ·
          refine ⟨28415023912541484678877793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18943349275027656452585195 28415023912541484678877793)
          ·
            refine ⟨21311267934406113509158345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28415023912541484678877793 21311267934406113509158345)
            ·
              refine ⟨15983450950804585131868759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21311267934406113509158345 15983450950804585131868759)
              ·
                refine ⟨23975176426206877697803139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15983450950804585131868759 23975176426206877697803139)
                ·
                  refine ⟨35962764639310316546704709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23975176426206877697803139 35962764639310316546704709)
                  ·
                    refine ⟨6743018369870684352507133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35962764639310316546704709 6743018369870684352507133)
                    ·
                      refine ⟨2528631888701506632190175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743018369870684352507133 2528631888701506632190175)
                      ·
                        rfl

theorem cell23_4924493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_4924493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924493 prefixEnd_4924493 := by exact prefixLift 4924493
  have htrace : WordTrace (prefixWord ++ tailWord_4924493) baseStart_4924493 baseEnd_4924493 := by
    simpa [prefixWord, tailWord_4924493, baseEnd_4924493] using wordTrace_append hprefix tailTrace_4924493
  have hstable : (prefixWord ++ tailWord_4924493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924493).length < 2 ^ (prefixWord ++ tailWord_4924493).sum := by decide
  have hdescent : baseEnd_4924493 < baseStart_4924493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924500 : List Nat := [2, 4, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_4924500 : Nat := 118140960795 + 4924500 * 2 ^ 59
def prefixEnd_4924500 : Nat := 4983230072969 + 3 ^ 40 * 4924500 * 2
def baseEnd_4924500 : Nat := 842878494355362701600881

theorem tailTrace_4924500 : CollatzResearch.WordTrace tailWord_4924500 prefixEnd_4924500 842878494355362701600881 := by
  unfold tailWord_4924500
  simp only [CollatzResearch.WordTrace]
  refine ⟨89805635329692506243341477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119740847106256674991121969 89805635329692506243341477)
  ·
    refine ⟨16838556624317344920626527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89805635329692506243341477 16838556624317344920626527)
    ·
      refine ⟨25257834936476017380939791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16838556624317344920626527 25257834936476017380939791)
      ·
        refine ⟨37886752404714026071409687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25257834936476017380939791 37886752404714026071409687)
        ·
          refine ⟨56830128607071039107114531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37886752404714026071409687 56830128607071039107114531)
          ·
            refine ⟨85245192910606558660671797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56830128607071039107114531 85245192910606558660671797)
            ·
              refine ⟨7991736835369364874437981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85245192910606558660671797 7991736835369364874437981)
              ·
                refine ⟨2996901313263511827914243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7991736835369364874437981 2996901313263511827914243)
                ·
                  refine ⟨4495351969895267741871365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996901313263511827914243 4495351969895267741871365)
                  ·
                    refine ⟨842878494355362701600881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4495351969895267741871365 842878494355362701600881)
                    ·
                      rfl

theorem cell23_4924500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_4924500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924500 prefixEnd_4924500 := by exact prefixLift 4924500
  have htrace : WordTrace (prefixWord ++ tailWord_4924500) baseStart_4924500 baseEnd_4924500 := by
    simpa [prefixWord, tailWord_4924500, baseEnd_4924500] using wordTrace_append hprefix tailTrace_4924500
  have hstable : (prefixWord ++ tailWord_4924500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924500).length < 2 ^ (prefixWord ++ tailWord_4924500).sum := by decide
  have hdescent : baseEnd_4924500 < baseStart_4924500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924539 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 5, 6]
def baseStart_4924539 : Nat := 118140960795 + 4924539 * 2 ^ 59
def prefixEnd_4924539 : Nat := 4983230072969 + 3 ^ 40 * 4924539 * 2
def baseEnd_4924539 : Nat := 842885169603871150738321

theorem tailTrace_4924539 : CollatzResearch.WordTrace tailWord_4924539 prefixEnd_4924539 842885169603871150738321 := by
  unfold tailWord_4924539
  simp only [CollatzResearch.WordTrace]
  refine ⟨179612693106243722147352671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119741795404162481431568447 179612693106243722147352671)
  ·
    refine ⟨269419039659365583221029007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179612693106243722147352671 269419039659365583221029007)
    ·
      refine ⟨404128559489048374831543511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269419039659365583221029007 404128559489048374831543511)
      ·
        refine ⟨606192839233572562247315267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404128559489048374831543511 606192839233572562247315267)
        ·
          refine ⟨909289258850358843370972901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606192839233572562247315267 909289258850358843370972901)
          ·
            refine ⟨170491736034442283132057419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 909289258850358843370972901 170491736034442283132057419)
            ·
              refine ⟨255737604051663424698086129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170491736034442283132057419 255737604051663424698086129)
              ·
                refine ⟨191803203038747568523564597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255737604051663424698086129 191803203038747568523564597)
                ·
                  refine ⟨17981550284882584549084181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191803203038747568523564597 17981550284882584549084181)
                  ·
                    refine ⟨842885169603871150738321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17981550284882584549084181 842885169603871150738321)
                    ·
                      rfl

theorem cell23_4924539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 6].length) (baseStart_4924539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924539 prefixEnd_4924539 := by exact prefixLift 4924539
  have htrace : WordTrace (prefixWord ++ tailWord_4924539) baseStart_4924539 baseEnd_4924539 := by
    simpa [prefixWord, tailWord_4924539, baseEnd_4924539] using wordTrace_append hprefix tailTrace_4924539
  have hstable : (prefixWord ++ tailWord_4924539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924539).length < 2 ^ (prefixWord ++ tailWord_4924539).sum := by decide
  have hdescent : baseEnd_4924539 < baseStart_4924539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924556 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_4924556 : Nat := 118140960795 + 4924556 * 2 ^ 59
def prefixEnd_4924556 : Nat := 4983230072969 + 3 ^ 40 * 4924556 * 2
def baseEnd_4924556 : Nat := 842888079327579961900795

theorem tailTrace_4924556 : CollatzResearch.WordTrace tailWord_4924556 prefixEnd_4924556 842888079327579961900795 := by
  unfold tailWord_4924556
  simp only [CollatzResearch.WordTrace]
  refine ⟨89806656573591067025360761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119742208764788089367147681 89806656573591067025360761)
  ·
    refine ⟨67354992430193300269020571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89806656573591067025360761 67354992430193300269020571)
    ·
      refine ⟨101032488645289950403530857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67354992430193300269020571 101032488645289950403530857)
      ·
        refine ⟨75774366483967462802648143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101032488645289950403530857 75774366483967462802648143)
        ·
          refine ⟨113661549725951194203972215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75774366483967462802648143 113661549725951194203972215)
          ·
            refine ⟨170492324588926791305958323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113661549725951194203972215 170492324588926791305958323)
            ·
              refine ⟨255738486883390186958937485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170492324588926791305958323 255738486883390186958937485)
              ·
                refine ⟨95901932581271320109601557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255738486883390186958937485 95901932581271320109601557)
                ·
                  refine ⟨4495403089747093130137573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95901932581271320109601557 4495403089747093130137573)
                  ·
                    refine ⟨842888079327579961900795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4495403089747093130137573 842888079327579961900795)
                    ·
                      rfl

theorem cell23_4924556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_4924556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924556 prefixEnd_4924556 := by exact prefixLift 4924556
  have htrace : WordTrace (prefixWord ++ tailWord_4924556) baseStart_4924556 baseEnd_4924556 := by
    simpa [prefixWord, tailWord_4924556, baseEnd_4924556] using wordTrace_append hprefix tailTrace_4924556
  have hstable : (prefixWord ++ tailWord_4924556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924556).length < 2 ^ (prefixWord ++ tailWord_4924556).sum := by decide
  have hdescent : baseEnd_4924556 < baseStart_4924556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924574 : List Nat := [4, 3, 1, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_4924574 : Nat := 118140960795 + 4924574 * 2 ^ 59
def prefixEnd_4924574 : Nat := 4983230072969 + 3 ^ 40 * 4924574 * 2
def baseEnd_4924574 : Nat := 2528673480634520815277303

theorem tailTrace_4924574 : CollatzResearch.WordTrace tailWord_4924574 prefixEnd_4924574 2528673480634520815277303 := by
  unfold tailWord_4924574
  simp only [CollatzResearch.WordTrace]
  refine ⟨22451746207639615390609597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119742646440744615416584517 22451746207639615390609597)
  ·
    refine ⟨8419404827864855771478599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22451746207639615390609597 8419404827864855771478599)
    ·
      refine ⟨12629107241797283657217899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8419404827864855771478599 12629107241797283657217899)
      ·
        refine ⟨18943660862695925485826849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12629107241797283657217899 18943660862695925485826849)
        ·
          refine ⟨14207745647021944114370137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18943660862695925485826849 14207745647021944114370137)
          ·
            refine ⟨10655809235266458085777603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14207745647021944114370137 10655809235266458085777603)
            ·
              refine ⟨15983713852899687128666405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10655809235266458085777603 15983713852899687128666405)
              ·
                refine ⟨2996946347418691336624951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15983713852899687128666405 2996946347418691336624951)
                ·
                  refine ⟨4495419521128037004937427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996946347418691336624951 4495419521128037004937427)
                  ·
                    refine ⟨6743129281692055507406141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4495419521128037004937427 6743129281692055507406141)
                    ·
                      refine ⟨2528673480634520815277303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743129281692055507406141 2528673480634520815277303)
                      ·
                        rfl

theorem cell23_4924574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_4924574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924574 prefixEnd_4924574 := by exact prefixLift 4924574
  have htrace : WordTrace (prefixWord ++ tailWord_4924574) baseStart_4924574 baseEnd_4924574 := by
    simpa [prefixWord, tailWord_4924574, baseEnd_4924574] using wordTrace_append hprefix tailTrace_4924574
  have hstable : (prefixWord ++ tailWord_4924574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924574).length < 2 ^ (prefixWord ++ tailWord_4924574).sum := by decide
  have hdescent : baseEnd_4924574 < baseStart_4924574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924576 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4924576 : Nat := 118140960795 + 4924576 * 2 ^ 59
def prefixEnd_4924576 : Nat := 4983230072969 + 3 ^ 40 * 4924576 * 2
def baseEnd_4924576 : Nat := 2528674507595829807452293

theorem tailTrace_4924576 : CollatzResearch.WordTrace tailWord_4924576 prefixEnd_4924576 2528674507595829807452293 := by
  unfold tailWord_4924576
  simp only [CollatzResearch.WordTrace]
  refine ⟨89807021303554838733224791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119742695071406451644299721 89807021303554838733224791)
  ·
    refine ⟨134710531955332258099837187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89807021303554838733224791 134710531955332258099837187)
    ·
      refine ⟨202065797932998387149755781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134710531955332258099837187 202065797932998387149755781)
      ·
        refine ⟨37887337112437197590579209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202065797932998387149755781 37887337112437197590579209)
        ·
          refine ⟨28415502834327898192934407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37887337112437197590579209 28415502834327898192934407)
          ·
            refine ⟨42623254251491847289401611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28415502834327898192934407 42623254251491847289401611)
            ·
              refine ⟨63934881377237770934102417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42623254251491847289401611 63934881377237770934102417)
              ·
                refine ⟨47951161032928328200576813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63934881377237770934102417 47951161032928328200576813)
                ·
                  refine ⟨17981685387348123075216305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47951161032928328200576813 17981685387348123075216305)
                  ·
                    refine ⟨13486264040511092306412229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17981685387348123075216305 13486264040511092306412229)
                    ·
                      refine ⟨2528674507595829807452293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13486264040511092306412229 2528674507595829807452293)
                      ·
                        rfl

theorem cell23_4924576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4924576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924576 prefixEnd_4924576 := by exact prefixLift 4924576
  have htrace : WordTrace (prefixWord ++ tailWord_4924576) baseStart_4924576 baseEnd_4924576 := by
    simpa [prefixWord, tailWord_4924576, baseEnd_4924576] using wordTrace_append hprefix tailTrace_4924576
  have hstable : (prefixWord ++ tailWord_4924576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924576).length < 2 ^ (prefixWord ++ tailWord_4924576).sum := by decide
  have hdescent : baseEnd_4924576 < baseStart_4924576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924593 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4924593 : Nat := 118140960795 + 4924593 * 2 ^ 59
def prefixEnd_4924593 : Nat := 4983230072969 + 3 ^ 40 * 4924593 * 2
def baseEnd_4924593 : Nat := 2528683236766956240939715

theorem tailTrace_4924593 : CollatzResearch.WordTrace tailWord_4924593 prefixEnd_4924593 2528683236766956240939715 := by
  unfold tailWord_4924593
  simp only [CollatzResearch.WordTrace]
  refine ⟨179614662648048089369818433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119743108432032059579878955 179614662648048089369818433)
  ·
    refine ⟨134710996986036067027363825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179614662648048089369818433 134710996986036067027363825)
    ·
      refine ⟨101033247739527050270522869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134710996986036067027363825 101033247739527050270522869)
      ·
        refine ⟨9471866975580660962861519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101033247739527050270522869 9471866975580660962861519)
        ·
          refine ⟨14207800463370991444292279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9471866975580660962861519 14207800463370991444292279)
          ·
            refine ⟨21311700695056487166438419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14207800463370991444292279 21311700695056487166438419)
            ·
              refine ⟨31967551042584730749657629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21311700695056487166438419 31967551042584730749657629)
              ·
                refine ⟨11987831640969274031121611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31967551042584730749657629 11987831640969274031121611)
                ·
                  refine ⟨17981747461453911046682417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11987831640969274031121611 17981747461453911046682417)
                  ·
                    refine ⟨13486310596090433285011813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17981747461453911046682417 13486310596090433285011813)
                    ·
                      refine ⟨2528683236766956240939715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13486310596090433285011813 2528683236766956240939715)
                      ·
                        rfl

theorem cell23_4924593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4924593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924593 prefixEnd_4924593 := by exact prefixLift 4924593
  have htrace : WordTrace (prefixWord ++ tailWord_4924593) baseStart_4924593 baseEnd_4924593 := by
    simpa [prefixWord, tailWord_4924593, baseEnd_4924593] using wordTrace_append hprefix tailTrace_4924593
  have hstable : (prefixWord ++ tailWord_4924593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924593).length < 2 ^ (prefixWord ++ tailWord_4924593).sum := by decide
  have hdescent : baseEnd_4924593 < baseStart_4924593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924613 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_4924613 : Nat := 118140960795 + 4924613 * 2 ^ 59
def prefixEnd_4924613 : Nat := 4983230072969 + 3 ^ 40 * 4924613 * 2
def baseEnd_4924613 : Nat := 2528693506380046162689623

theorem tailTrace_4924613 : CollatzResearch.WordTrace tailWord_4924613 prefixEnd_4924613 2528693506380046162689623 := by
  unfold tailWord_4924613
  simp only [CollatzResearch.WordTrace]
  refine ⟨179615392107975632785546493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119743594738650421857030995 179615392107975632785546493)
  ·
    refine ⟨67355772040490862294579935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179615392107975632785546493 67355772040490862294579935)
    ·
      refine ⟨101033658060736293441869903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67355772040490862294579935 101033658060736293441869903)
      ·
        refine ⟨151550487091104440162804855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101033658060736293441869903 151550487091104440162804855)
        ·
          refine ⟨227325730636656660244207283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151550487091104440162804855 227325730636656660244207283)
          ·
            refine ⟨340988595954984990366310925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227325730636656660244207283 340988595954984990366310925)
            ·
              refine ⟨127870723483119371387366597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340988595954984990366310925 127870723483119371387366597)
              ·
                refine ⟨23975760653084882135131237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127870723483119371387366597 23975760653084882135131237)
                ·
                  refine ⟨4495455122453415400337107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23975760653084882135131237 4495455122453415400337107)
                  ·
                    refine ⟨6743182683680123100505661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4495455122453415400337107 6743182683680123100505661)
                    ·
                      refine ⟨2528693506380046162689623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743182683680123100505661 2528693506380046162689623)
                      ·
                        rfl

theorem cell23_4924613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_4924613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924613 prefixEnd_4924613 := by exact prefixLift 4924613
  have htrace : WordTrace (prefixWord ++ tailWord_4924613) baseStart_4924613 baseEnd_4924613 := by
    simpa [prefixWord, tailWord_4924613, baseEnd_4924613] using wordTrace_append hprefix tailTrace_4924613
  have hstable : (prefixWord ++ tailWord_4924613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924613).length < 2 ^ (prefixWord ++ tailWord_4924613).sum := by decide
  have hdescent : baseEnd_4924613 < baseStart_4924613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924623 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 5, 3, 2]
def baseStart_4924623 : Nat := 118140960795 + 4924623 * 2 ^ 59
def prefixEnd_4924623 : Nat := 4983230072969 + 3 ^ 40 * 4924623 * 2
def baseEnd_4924623 : Nat := 2528698641186591123564577

theorem tailTrace_4924623 : CollatzResearch.WordTrace tailWord_4924623 prefixEnd_4924623 2528698641186591123564577 := by
  unfold tailWord_4924623
  simp only [CollatzResearch.WordTrace]
  refine ⟨179615756837939404493410523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119743837891959602995607015 179615756837939404493410523)
  ·
    refine ⟨269423635256909106740115785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179615756837939404493410523 269423635256909106740115785)
    ·
      refine ⟨202067726442681830055086839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269423635256909106740115785 202067726442681830055086839)
      ·
        refine ⟨303101589664022745082630259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202067726442681830055086839 303101589664022745082630259)
        ·
          refine ⟨454652384496034117623945389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303101589664022745082630259 454652384496034117623945389)
          ·
            refine ⟨170494644186012794108979521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 454652384496034117623945389 170494644186012794108979521)
            ·
              refine ⟨127870983139509595581734641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170494644186012794108979521 127870983139509595581734641)
              ·
                refine ⟨95903237354632196686300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127870983139509595581734641 95903237354632196686300981)
                ·
                  refine ⟨8990928501996768439340717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95903237354632196686300981 8990928501996768439340717)
                  ·
                    refine ⟨3371598188248788164752769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8990928501996768439340717 3371598188248788164752769)
                    ·
                      refine ⟨2528698641186591123564577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371598188248788164752769 2528698641186591123564577)
                      ·
                        rfl

theorem cell23_4924623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3, 2].length) (baseStart_4924623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924623 prefixEnd_4924623 := by exact prefixLift 4924623
  have htrace : WordTrace (prefixWord ++ tailWord_4924623) baseStart_4924623 baseEnd_4924623 := by
    simpa [prefixWord, tailWord_4924623, baseEnd_4924623] using wordTrace_append hprefix tailTrace_4924623
  have hstable : (prefixWord ++ tailWord_4924623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924623).length < 2 ^ (prefixWord ++ tailWord_4924623).sum := by decide
  have hdescent : baseEnd_4924623 < baseStart_4924623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924647 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4924647 : Nat := 118140960795 + 4924647 * 2 ^ 59
def prefixEnd_4924647 : Nat := 4983230072969 + 3 ^ 40 * 4924647 * 2
def baseEnd_4924647 : Nat := 2528710964722299029664467

theorem tailTrace_4924647 : CollatzResearch.WordTrace tailWord_4924647 prefixEnd_4924647 2528710964722299029664467 := by
  unfold tailWord_4924647
  simp only [CollatzResearch.WordTrace]
  refine ⟨179616632189852456592284195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119744421459901637728189463 179616632189852456592284195)
  ·
    refine ⟨269424948284778684888426293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179616632189852456592284195 269424948284778684888426293)
    ·
      refine ⟨25258588901698001708289965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269424948284778684888426293 25258588901698001708289965)
      ·
        refine ⟨9471970838136750640608737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25258588901698001708289965 9471970838136750640608737)
        ·
          refine ⟨7103978128602562980456553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9471970838136750640608737 7103978128602562980456553)
          ·
            refine ⟨5327983596451922235342415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7103978128602562980456553 5327983596451922235342415)
            ·
              refine ⟨7991975394677883353013623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5327983596451922235342415 7991975394677883353013623)
              ·
                refine ⟨11987963092016825029520435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7991975394677883353013623 11987963092016825029520435)
                ·
                  refine ⟨17981944638025237544280653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11987963092016825029520435 17981944638025237544280653)
                  ·
                    refine ⟨6743229239259464079105245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17981944638025237544280653 6743229239259464079105245)
                    ·
                      refine ⟨2528710964722299029664467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743229239259464079105245 2528710964722299029664467)
                      ·
                        rfl

theorem cell23_4924647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4924647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924647 prefixEnd_4924647 := by exact prefixLift 4924647
  have htrace : WordTrace (prefixWord ++ tailWord_4924647) baseStart_4924647 baseEnd_4924647 := by
    simpa [prefixWord, tailWord_4924647, baseEnd_4924647] using wordTrace_append hprefix tailTrace_4924647
  have hstable : (prefixWord ++ tailWord_4924647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924647).length < 2 ^ (prefixWord ++ tailWord_4924647).sum := by decide
  have hdescent : baseEnd_4924647 < baseStart_4924647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924673 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4924673 : Nat := 118140960795 + 4924673 * 2 ^ 59
def prefixEnd_4924673 : Nat := 4983230072969 + 3 ^ 40 * 4924673 * 2
def baseEnd_4924673 : Nat := 2528724315219315927939347

theorem tailTrace_4924673 : CollatzResearch.WordTrace tailWord_4924673 prefixEnd_4924673 2528724315219315927939347 := by
  unfold tailWord_4924673
  simp only [CollatzResearch.WordTrace]
  refine ⟨179617580487758263032730673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119745053658505508688487115 179617580487758263032730673)
  ·
    refine ⟨134713185365818697274548005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179617580487758263032730673 134713185365818697274548005)
    ·
      refine ⟨25258722256091005738977751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134713185365818697274548005 25258722256091005738977751)
      ·
        refine ⟨37888083384136508608466627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25258722256091005738977751 37888083384136508608466627)
        ·
          refine ⟨56832125076204762912699941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37888083384136508608466627 56832125076204762912699941)
          ·
            refine ⟨10656023451788393046131239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56832125076204762912699941 10656023451788393046131239)
            ·
              refine ⟨15984035177682589569196859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10656023451788393046131239 15984035177682589569196859)
              ·
                refine ⟨23976052766523884353795289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15984035177682589569196859 23976052766523884353795289)
                ·
                  refine ⟨17982039574892913265346467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23976052766523884353795289 17982039574892913265346467)
                  ·
                    refine ⟨26973059362339369898019701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17982039574892913265346467 26973059362339369898019701)
                    ·
                      refine ⟨2528724315219315927939347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26973059362339369898019701 2528724315219315927939347)
                      ·
                        rfl

theorem cell23_4924673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4924673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924673 prefixEnd_4924673 := by exact prefixLift 4924673
  have htrace : WordTrace (prefixWord ++ tailWord_4924673) baseStart_4924673 baseEnd_4924673 := by
    simpa [prefixWord, tailWord_4924673, baseEnd_4924673] using wordTrace_append hprefix tailTrace_4924673
  have hstable : (prefixWord ++ tailWord_4924673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924673).length < 2 ^ (prefixWord ++ tailWord_4924673).sum := by decide
  have hdescent : baseEnd_4924673 < baseStart_4924673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924704 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 2, 2, 2]
def baseStart_4924704 : Nat := 118140960795 + 4924704 * 2 ^ 59
def prefixEnd_4924704 : Nat := 4983230072969 + 3 ^ 40 * 4924704 * 2
def baseEnd_4924704 : Nat := 2528740233119605306651705

theorem tailTrace_4924704 : CollatzResearch.WordTrace tailWord_4924704 prefixEnd_4924704 2528740233119605306651705 := by
  unfold tailWord_4924704
  simp only [CollatzResearch.WordTrace]
  refine ⟨89809355575322977663554583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119745807433763970218072777 89809355575322977663554583)
  ·
    refine ⟨134714033362984466495331875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89809355575322977663554583 134714033362984466495331875)
    ·
      refine ⟨202071050044476699742997813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134714033362984466495331875 202071050044476699742997813)
      ·
        refine ⟨18944160941669690600906045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202071050044476699742997813 18944160941669690600906045)
        ·
          refine ⟨7104060353126133975339767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18944160941669690600906045 7104060353126133975339767)
          ·
            refine ⟨10656090529689200963009651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104060353126133975339767 10656090529689200963009651)
            ·
              refine ⟨15984135794533801444514477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10656090529689200963009651 15984135794533801444514477)
              ·
                refine ⟨5994050922950175541692929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15984135794533801444514477 5994050922950175541692929)
                ·
                  refine ⟨4495538192212631656269697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994050922950175541692929 4495538192212631656269697)
                  ·
                    refine ⟨3371653644159473742202273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4495538192212631656269697 3371653644159473742202273)
                    ·
                      refine ⟨2528740233119605306651705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371653644159473742202273 2528740233119605306651705)
                      ·
                        rfl

theorem cell23_4924704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_4924704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924704 prefixEnd_4924704 := by exact prefixLift 4924704
  have htrace : WordTrace (prefixWord ++ tailWord_4924704) baseStart_4924704 baseEnd_4924704 := by
    simpa [prefixWord, tailWord_4924704, baseEnd_4924704] using wordTrace_append hprefix tailTrace_4924704
  have hstable : (prefixWord ++ tailWord_4924704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924704).length < 2 ^ (prefixWord ++ tailWord_4924704).sum := by decide
  have hdescent : baseEnd_4924704 < baseStart_4924704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924716 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_4924716 : Nat := 118140960795 + 4924716 * 2 ^ 59
def prefixEnd_4924716 : Nat := 4983230072969 + 3 ^ 40 * 4924716 * 2
def baseEnd_4924716 : Nat := 2528746394887459259701649

theorem tailTrace_4924716 : CollatzResearch.WordTrace tailWord_4924716 prefixEnd_4924716 2528746394887459259701649 := by
  unfold tailWord_4924716
  simp only [CollatzResearch.WordTrace]
  refine ⟨89809574413301240688273001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119746099217734987584364001 89809574413301240688273001)
  ·
    refine ⟨67357180809975930516204751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89809574413301240688273001 67357180809975930516204751)
    ·
      refine ⟨101035771214963895774307127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67357180809975930516204751 101035771214963895774307127)
      ·
        refine ⟨151553656822445843661460691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101035771214963895774307127 151553656822445843661460691)
        ·
          refine ⟨227330485233668765492191037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151553656822445843661460691 227330485233668765492191037)
          ·
            refine ⟨85248931962625787059571639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227330485233668765492191037 85248931962625787059571639)
            ·
              refine ⟨127873397943938680589357459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85248931962625787059571639 127873397943938680589357459)
              ·
                refine ⟨191810096915908020884036189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127873397943938680589357459 191810096915908020884036189)
                ·
                  refine ⟨71928786343465507831513571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191810096915908020884036189 71928786343465507831513571)
                  ·
                    refine ⟨107893179515198261747270357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71928786343465507831513571 107893179515198261747270357)
                    ·
                      refine ⟨2528746394887459259701649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107893179515198261747270357 2528746394887459259701649)
                      ·
                        rfl

theorem cell23_4924716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_4924716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924716 prefixEnd_4924716 := by exact prefixLift 4924716
  have htrace : WordTrace (prefixWord ++ tailWord_4924716) baseStart_4924716 baseEnd_4924716 := by
    simpa [prefixWord, tailWord_4924716, baseEnd_4924716] using wordTrace_append hprefix tailTrace_4924716
  have hstable : (prefixWord ++ tailWord_4924716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924716).length < 2 ^ (prefixWord ++ tailWord_4924716).sum := by decide
  have hdescent : baseEnd_4924716 < baseStart_4924716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924723 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 2, 5]
def baseStart_4924723 : Nat := 118140960795 + 4924723 * 2 ^ 59
def prefixEnd_4924723 : Nat := 4983230072969 + 3 ^ 40 * 4924723 * 2
def baseEnd_4924723 : Nat := 842916663084013577438039

theorem tailTrace_4924723 : CollatzResearch.WordTrace tailWord_4924723 prefixEnd_4924723 842916663084013577438039 := by
  unfold tailWord_4924723
  simp only [CollatzResearch.WordTrace]
  refine ⟨179619404137577121572050823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119746269425051414381367215 179619404137577121572050823)
  ·
    refine ⟨269429106206365682358076235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179619404137577121572050823 269429106206365682358076235)
    ·
      refine ⟨404143659309548523537114353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269429106206365682358076235 404143659309548523537114353)
      ·
        refine ⟨303107744482161392652835765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404143659309548523537114353 303107744482161392652835765)
        ·
          refine ⟨28416351045202630561203353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 303107744482161392652835765 28416351045202630561203353)
          ·
            refine ⟨21312263283901972920902515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28416351045202630561203353 21312263283901972920902515)
            ·
              refine ⟨31968394925852959381353773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21312263283901972920902515 31968394925852959381353773)
              ·
                refine ⟨11988148097194859768007665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31968394925852959381353773 11988148097194859768007665)
                ·
                  refine ⟨8991111072896144826005749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11988148097194859768007665 8991111072896144826005749)
                  ·
                    refine ⟨842916663084013577438039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8991111072896144826005749 842916663084013577438039)
                    ·
                      rfl

theorem cell23_4924723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 5].length) (baseStart_4924723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924723 prefixEnd_4924723 := by exact prefixLift 4924723
  have htrace : WordTrace (prefixWord ++ tailWord_4924723) baseStart_4924723 baseEnd_4924723 := by
    simpa [prefixWord, tailWord_4924723, baseEnd_4924723] using wordTrace_append hprefix tailTrace_4924723
  have hstable : (prefixWord ++ tailWord_4924723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924723).length < 2 ^ (prefixWord ++ tailWord_4924723).sum := by decide
  have hdescent : baseEnd_4924723 < baseStart_4924723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924760 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 2, 4, 2]
def baseStart_4924760 : Nat := 118140960795 + 4924760 * 2 ^ 59
def prefixEnd_4924760 : Nat := 4983230072969 + 3 ^ 40 * 4924760 * 2
def baseEnd_4924760 : Nat := 2528768988036257087551447

theorem tailTrace_4924760 : CollatzResearch.WordTrace tailWord_4924760 prefixEnd_4924760 2528768988036257087551447 := by
  unfold tailWord_4924760
  simp only [CollatzResearch.WordTrace]
  refine ⟨89810376819221538445573867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119747169092295384594098489 89810376819221538445573867)
  ·
    refine ⟨134715565228832307668360801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89810376819221538445573867 134715565228832307668360801)
    ·
      refine ⟨101036673921624230751270601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134715565228832307668360801 101036673921624230751270601)
      ·
        refine ⟨75777505441218173063452951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101036673921624230751270601 75777505441218173063452951)
        ·
          refine ⟨113666258161827259595179427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75777505441218173063452951 113666258161827259595179427)
          ·
            refine ⟨170499387242740889392769141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113666258161827259595179427 170499387242740889392769141)
            ·
              refine ⟨15984317554006958380572107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170499387242740889392769141 15984317554006958380572107)
              ·
                refine ⟨23976476331010437570858161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15984317554006958380572107 23976476331010437570858161)
                ·
                  refine ⟨17982357248257828178143621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23976476331010437570858161 17982357248257828178143621)
                  ·
                    refine ⟨3371691984048342783401929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17982357248257828178143621 3371691984048342783401929)
                    ·
                      refine ⟨2528768988036257087551447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371691984048342783401929 2528768988036257087551447)
                      ·
                        rfl

theorem cell23_4924760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_4924760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924760 prefixEnd_4924760 := by exact prefixLift 4924760
  have htrace : WordTrace (prefixWord ++ tailWord_4924760) baseStart_4924760 baseEnd_4924760 := by
    simpa [prefixWord, tailWord_4924760, baseEnd_4924760] using wordTrace_append hprefix tailTrace_4924760
  have hstable : (prefixWord ++ tailWord_4924760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924760).length < 2 ^ (prefixWord ++ tailWord_4924760).sum := by decide
  have hdescent : baseEnd_4924760 < baseStart_4924760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924780 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_4924780 : Nat := 118140960795 + 4924780 * 2 ^ 59
def prefixEnd_4924780 : Nat := 4983230072969 + 3 ^ 40 * 4924780 * 2
def baseEnd_4924780 : Nat := 2528779257649347009301355

theorem tailTrace_4924780 : CollatzResearch.WordTrace tailWord_4924780 prefixEnd_4924780 2528779257649347009301355 := by
  unfold tailWord_4924780
  simp only [CollatzResearch.WordTrace]
  refine ⟨89810741549185310153437897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119747655398913746871250529 89810741549185310153437897)
  ·
    refine ⟨67358056161888982615078423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89810741549185310153437897 67358056161888982615078423)
    ·
      refine ⟨101037084242833473922617635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67358056161888982615078423 101037084242833473922617635)
      ·
        refine ⟨151555626364250210883926453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101037084242833473922617635 151555626364250210883926453)
        ·
          refine ⟨14208339971648457270368105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151555626364250210883926453 14208339971648457270368105)
          ·
            refine ⟨10656254978736342952776079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14208339971648457270368105 10656254978736342952776079)
            ·
              refine ⟨15984382468104514429164119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10656254978736342952776079 15984382468104514429164119)
              ·
                refine ⟨23976573702156771643746179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15984382468104514429164119 23976573702156771643746179)
                ·
                  refine ⟨35964860553235157465619269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23976573702156771643746179 35964860553235157465619269)
                  ·
                    refine ⟨6743411353731592024803613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35964860553235157465619269 6743411353731592024803613)
                    ·
                      refine ⟨2528779257649347009301355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743411353731592024803613 2528779257649347009301355)
                      ·
                        rfl

theorem cell23_4924780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_4924780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924780 prefixEnd_4924780 := by exact prefixLift 4924780
  have htrace : WordTrace (prefixWord ++ tailWord_4924780) baseStart_4924780 baseEnd_4924780 := by
    simpa [prefixWord, tailWord_4924780, baseEnd_4924780] using wordTrace_append hprefix tailTrace_4924780
  have hstable : (prefixWord ++ tailWord_4924780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924780).length < 2 ^ (prefixWord ++ tailWord_4924780).sum := by decide
  have hdescent : baseEnd_4924780 < baseStart_4924780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924803 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6]
def baseStart_4924803 : Nat := 118140960795 + 4924803 * 2 ^ 59
def prefixEnd_4924803 : Nat := 4983230072969 + 3 ^ 40 * 4924803 * 2
def baseEnd_4924803 : Nat := 2528791067704400419313749

theorem tailTrace_4924803 : CollatzResearch.WordTrace tailWord_4924803 prefixEnd_4924803 2528791067704400419313749 := by
  unfold tailWord_4924803
  simp only [CollatzResearch.WordTrace]
  refine ⟨179622321977287295234963063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119748214651524863489975375 179622321977287295234963063)
  ·
    refine ⟨269433482965930942852444595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179622321977287295234963063 269433482965930942852444595)
    ·
      refine ⟨404150224448896414278666893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269433482965930942852444595 404150224448896414278666893)
      ·
        refine ⟨151556334168336155354500085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404150224448896414278666893 151556334168336155354500085)
        ·
          refine ⟨14208406328281514564484383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151556334168336155354500085 14208406328281514564484383)
          ·
            refine ⟨21312609492422271846726575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14208406328281514564484383 21312609492422271846726575)
            ·
              refine ⟨31968914238633407770089863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21312609492422271846726575 31968914238633407770089863)
              ·
                refine ⟨47953371357950111655134795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31968914238633407770089863 47953371357950111655134795)
                ·
                  refine ⟨71930057036925167482702193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47953371357950111655134795 71930057036925167482702193)
                  ·
                    refine ⟨53947542777693875612026645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71930057036925167482702193 53947542777693875612026645)
                    ·
                      refine ⟨2528791067704400419313749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53947542777693875612026645 2528791067704400419313749)
                      ·
                        rfl

theorem cell23_4924803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_4924803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924803 prefixEnd_4924803 := by exact prefixLift 4924803
  have htrace : WordTrace (prefixWord ++ tailWord_4924803) baseStart_4924803 baseEnd_4924803 := by
    simpa [prefixWord, tailWord_4924803, baseEnd_4924803] using wordTrace_append hprefix tailTrace_4924803
  have hstable : (prefixWord ++ tailWord_4924803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924803).length < 2 ^ (prefixWord ++ tailWord_4924803).sum := by decide
  have hdescent : baseEnd_4924803 < baseStart_4924803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924844 : List Nat := [2, 2, 1, 1, 1, 1, 7, 3, 1, 1, 3]
def baseStart_4924844 : Nat := 118140960795 + 4924844 * 2 ^ 59
def prefixEnd_4924844 : Nat := 4983230072969 + 3 ^ 40 * 4924844 * 2
def baseEnd_4924844 : Nat := 2528812120411234758901061

theorem tailTrace_4924844 : CollatzResearch.WordTrace tailWord_4924844 prefixEnd_4924844 2528812120411234758901061 := by
  unfold tailWord_4924844
  simp only [CollatzResearch.WordTrace]
  refine ⟨89811908685069379618602793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119749211580092506158137057 89811908685069379618602793)
  ·
    refine ⟨67358931513802034713952095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89811908685069379618602793 67358931513802034713952095)
    ·
      refine ⟨101038397270703052070928143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67358931513802034713952095 101038397270703052070928143)
      ·
        refine ⟨151557595906054578106392215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101038397270703052070928143 151557595906054578106392215)
        ·
          refine ⟨227336393859081867159588323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151557595906054578106392215 227336393859081867159588323)
          ·
            refine ⟨341004590788622800739382485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227336393859081867159588323 341004590788622800739382485)
            ·
              refine ⟨7992295096608346892329277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 341004590788622800739382485 7992295096608346892329277)
              ·
                refine ⟨2997110661228130084623479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7992295096608346892329277 2997110661228130084623479)
                ·
                  refine ⟨4495665991842195126935219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997110661228130084623479 4495665991842195126935219)
                  ·
                    refine ⟨6743498987763292690402829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4495665991842195126935219 6743498987763292690402829)
                    ·
                      refine ⟨2528812120411234758901061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743498987763292690402829 2528812120411234758901061)
                      ·
                        rfl

theorem cell23_4924844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_4924844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924844 prefixEnd_4924844 := by exact prefixLift 4924844
  have htrace : WordTrace (prefixWord ++ tailWord_4924844) baseStart_4924844 baseEnd_4924844 := by
    simpa [prefixWord, tailWord_4924844, baseEnd_4924844] using wordTrace_append hprefix tailTrace_4924844
  have hstable : (prefixWord ++ tailWord_4924844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924844).length < 2 ^ (prefixWord ++ tailWord_4924844).sum := by decide
  have hdescent : baseEnd_4924844 < baseStart_4924844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924861 : List Nat := [1, 4, 1, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_4924861 : Nat := 118140960795 + 4924861 * 2 ^ 59
def prefixEnd_4924861 : Nat := 4983230072969 + 3 ^ 40 * 4924861 * 2
def baseEnd_4924861 : Nat := 2528820849582361192388483

theorem tailTrace_4924861 : CollatzResearch.WordTrace tailWord_4924861 prefixEnd_4924861 2528820849582361192388483 := by
  unfold tailWord_4924861
  simp only [CollatzResearch.WordTrace]
  refine ⟨179624437411077171140574437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119749624940718114093716291 179624437411077171140574437)
  ·
    refine ⟨33679582014576969588857707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179624437411077171140574437 33679582014576969588857707)
    ·
      refine ⟨50519373021865454383286561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33679582014576969588857707 50519373021865454383286561)
      ·
        refine ⟨37889529766399090787464921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50519373021865454383286561 37889529766399090787464921)
        ·
          refine ⟨28417147324799318090598691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37889529766399090787464921 28417147324799318090598691)
          ·
            refine ⟨42625720987198977135898037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28417147324799318090598691 42625720987198977135898037)
            ·
              refine ⟨3996161342549904106490441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42625720987198977135898037 3996161342549904106490441)
              ·
                refine ⟨2997121006912428079867831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3996161342549904106490441 2997121006912428079867831)
                ·
                  refine ⟨4495681510368642119801747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997121006912428079867831 4495681510368642119801747)
                  ·
                    refine ⟨6743522265552963179702621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4495681510368642119801747 6743522265552963179702621)
                    ·
                      refine ⟨2528820849582361192388483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743522265552963179702621 2528820849582361192388483)
                      ·
                        rfl

theorem cell23_4924861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_4924861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924861 prefixEnd_4924861 := by exact prefixLift 4924861
  have htrace : WordTrace (prefixWord ++ tailWord_4924861) baseStart_4924861 baseEnd_4924861 := by
    simpa [prefixWord, tailWord_4924861, baseEnd_4924861] using wordTrace_append hprefix tailTrace_4924861
  have hstable : (prefixWord ++ tailWord_4924861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924861).length < 2 ^ (prefixWord ++ tailWord_4924861).sum := by decide
  have hdescent : baseEnd_4924861 < baseStart_4924861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924904 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_4924904 : Nat := 118140960795 + 4924904 * 2 ^ 59
def prefixEnd_4924904 : Nat := 4983230072969 + 3 ^ 40 * 4924904 * 2
def baseEnd_4924904 : Nat := 2528842929250504524150785

theorem tailTrace_4924904 : CollatzResearch.WordTrace tailWord_4924904 prefixEnd_4924904 2528842929250504524150785 := by
  unfold tailWord_4924904
  simp only [CollatzResearch.WordTrace]
  refine ⟨89813002874960694742194883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119750670499947592989593177 89813002874960694742194883)
  ·
    refine ⟨134719504312441042113292325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89813002874960694742194883 134719504312441042113292325)
    ·
      refine ⟨25259907058582695396242311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134719504312441042113292325 25259907058582695396242311)
      ·
        refine ⟨37889860587874043094363467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25259907058582695396242311 37889860587874043094363467)
        ·
          refine ⟨56834790881811064641545201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37889860587874043094363467 56834790881811064641545201)
          ·
            refine ⟨42626093161358298481158901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56834790881811064641545201 42626093161358298481158901)
            ·
              refine ⟨3996196233877340482608647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42626093161358298481158901 3996196233877340482608647)
              ·
                refine ⟨5994294350816010723912971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996196233877340482608647 5994294350816010723912971)
                ·
                  refine ⟨8991441526224016085869457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5994294350816010723912971 8991441526224016085869457)
                  ·
                    refine ⟨6743581144668012064402093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8991441526224016085869457 6743581144668012064402093)
                    ·
                      refine ⟨2528842929250504524150785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743581144668012064402093 2528842929250504524150785)
                      ·
                        rfl

theorem cell23_4924904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_4924904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924904 prefixEnd_4924904 := by exact prefixLift 4924904
  have htrace : WordTrace (prefixWord ++ tailWord_4924904) baseStart_4924904 baseEnd_4924904 := by
    simpa [prefixWord, tailWord_4924904, baseEnd_4924904] using wordTrace_append hprefix tailTrace_4924904
  have hstable : (prefixWord ++ tailWord_4924904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924904).length < 2 ^ (prefixWord ++ tailWord_4924904).sum := by decide
  have hdescent : baseEnd_4924904 < baseStart_4924904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924918 : List Nat := [5, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_4924918 : Nat := 118140960795 + 4924918 * 2 ^ 59
def prefixEnd_4924918 : Nat := 4983230072969 + 3 ^ 40 * 4924918 * 2
def baseEnd_4924918 : Nat := 2528850117979667469375721

theorem tailTrace_4924918 : CollatzResearch.WordTrace tailWord_4924918 prefixEnd_4924918 2528850117979667469375721 := by
  unfold tailWord_4924918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226657273241916867212463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119751010914580446583599605 11226657273241916867212463)
  ·
    refine ⟨16839985909862875300818695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11226657273241916867212463 16839985909862875300818695)
    ·
      refine ⟨25259978864794312951228043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16839985909862875300818695 25259978864794312951228043)
      ·
        refine ⟨37889968297191469426842065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25259978864794312951228043 37889968297191469426842065)
        ·
          refine ⟨28417476222893602070131549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37889968297191469426842065 28417476222893602070131549)
          ·
            refine ⟨10656553583585100776299331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28417476222893602070131549 10656553583585100776299331)
            ·
              refine ⟨15984830375377651164448997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10656553583585100776299331 15984830375377651164448997)
              ·
                refine ⟨2997155695383309593334187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15984830375377651164448997 2997155695383309593334187)
                ·
                  refine ⟨4495733543074964390001281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997155695383309593334187 4495733543074964390001281)
                  ·
                    refine ⟨3371800157306223292500961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4495733543074964390001281 3371800157306223292500961)
                    ·
                      refine ⟨2528850117979667469375721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371800157306223292500961 2528850117979667469375721)
                      ·
                        rfl

theorem cell23_4924918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_4924918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924918 prefixEnd_4924918 := by exact prefixLift 4924918
  have htrace : WordTrace (prefixWord ++ tailWord_4924918) baseStart_4924918 baseEnd_4924918 := by
    simpa [prefixWord, tailWord_4924918, baseEnd_4924918] using wordTrace_append hprefix tailTrace_4924918
  have hstable : (prefixWord ++ tailWord_4924918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924918).length < 2 ^ (prefixWord ++ tailWord_4924918).sum := by decide
  have hdescent : baseEnd_4924918 < baseStart_4924918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924941 : List Nat := [1, 7, 1, 1, 2, 1, 3, 7]
def baseStart_4924941 : Nat := 118140960795 + 4924941 * 2 ^ 59
def prefixEnd_4924941 : Nat := 4983230072969 + 3 ^ 40 * 4924941 * 2
def baseEnd_4924941 : Nat := 93661552890174847384745

theorem tailTrace_4924941 : CollatzResearch.WordTrace tailWord_4924941 prefixEnd_4924941 93661552890174847384745 := by
  unfold tailWord_4924941
  simp only [CollatzResearch.WordTrace]
  refine ⟨179627355250787344803486677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119751570167191563202324451 179627355250787344803486677)
  ·
    refine ⟨4210016138690328393831719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 179627355250787344803486677 4210016138690328393831719)
    ·
      refine ⟨6315024208035492590747579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4210016138690328393831719 6315024208035492590747579)
      ·
        refine ⟨9472536312053238886121369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315024208035492590747579 9472536312053238886121369)
        ·
          refine ⟨7104402234039929164591027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9472536312053238886121369 7104402234039929164591027)
          ·
            refine ⟨10656603351059893746886541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104402234039929164591027 10656603351059893746886541)
            ·
              refine ⟨3996226256647460155082453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10656603351059893746886541 3996226256647460155082453)
              ·
                refine ⟨93661552890174847384745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3996226256647460155082453 93661552890174847384745)
                ·
                  rfl

theorem cell23_4924941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 7].length) (baseStart_4924941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924941 prefixEnd_4924941 := by exact prefixLift 4924941
  have htrace : WordTrace (prefixWord ++ tailWord_4924941) baseStart_4924941 baseEnd_4924941 := by
    simpa [prefixWord, tailWord_4924941, baseEnd_4924941] using wordTrace_append hprefix tailTrace_4924941
  have hstable : (prefixWord ++ tailWord_4924941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924941).length < 2 ^ (prefixWord ++ tailWord_4924941).sum := by decide
  have hdescent : baseEnd_4924941 < baseStart_4924941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924961 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_4924961 : Nat := 118140960795 + 4924961 * 2 ^ 59
def prefixEnd_4924961 : Nat := 4983230072969 + 3 ^ 40 * 4924961 * 2
def baseEnd_4924961 : Nat := 2528872197647810801138023

theorem tailTrace_4924961 : CollatzResearch.WordTrace tailWord_4924961 prefixEnd_4924961 2528872197647810801138023 := by
  unfold tailWord_4924961
  simp only [CollatzResearch.WordTrace]
  refine ⟨179628084710714888219214737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119752056473809925479476491 179628084710714888219214737)
  ·
    refine ⟨134721063533036166164411053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179628084710714888219214737 134721063533036166164411053)
    ·
      refine ⟨50520398824888562311654145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134721063533036166164411053 50520398824888562311654145)
      ·
        refine ⟨37890299118666421733740609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50520398824888562311654145 37890299118666421733740609)
        ·
          refine ⟨28417724338999816300305457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37890299118666421733740609 28417724338999816300305457)
          ·
            refine ⟨21313293254249862225229093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28417724338999816300305457 21313293254249862225229093)
            ·
              refine ⟨3996242485171849167230455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21313293254249862225229093 3996242485171849167230455)
              ·
                refine ⟨5994363727757773750845683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996242485171849167230455 5994363727757773750845683)
                ·
                  refine ⟨8991545591636660626268525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5994363727757773750845683 8991545591636660626268525)
                  ·
                    refine ⟨3371829596863747734850697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8991545591636660626268525 3371829596863747734850697)
                    ·
                      refine ⟨2528872197647810801138023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371829596863747734850697 2528872197647810801138023)
                      ·
                        rfl

theorem cell23_4924961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_4924961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924961 prefixEnd_4924961 := by exact prefixLift 4924961
  have htrace : WordTrace (prefixWord ++ tailWord_4924961) baseStart_4924961 baseEnd_4924961 := by
    simpa [prefixWord, tailWord_4924961, baseEnd_4924961] using wordTrace_append hprefix tailTrace_4924961
  have hstable : (prefixWord ++ tailWord_4924961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924961).length < 2 ^ (prefixWord ++ tailWord_4924961).sum := by decide
  have hdescent : baseEnd_4924961 < baseStart_4924961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4924968 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4924968 : Nat := 118140960795 + 4924968 * 2 ^ 59
def prefixEnd_4924968 : Nat := 4983230072969 + 3 ^ 40 * 4924968 * 2
def baseEnd_4924968 : Nat := 2528875792012392273750491

theorem tailTrace_4924968 : CollatzResearch.WordTrace tailWord_4924968 prefixEnd_4924968 2528875792012392273750491 := by
  unfold tailWord_4924968
  simp only [CollatzResearch.WordTrace]
  refine ⟨89814170010844764207359779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119752226681126352276479705 89814170010844764207359779)
  ·
    refine ⟨134721255016267146311039669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89814170010844764207359779 134721255016267146311039669)
    ·
      refine ⟨12630117657775044966659969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134721255016267146311039669 12630117657775044966659969)
      ·
        refine ⟨9472588243331283724994977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12630117657775044966659969 9472588243331283724994977)
        ·
          refine ⟨7104441182498462793746233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9472588243331283724994977 7104441182498462793746233)
          ·
            refine ⟨5328330886873847095309675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7104441182498462793746233 5328330886873847095309675)
            ·
              refine ⟨7992496330310770642964513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328330886873847095309675 7992496330310770642964513)
              ·
                refine ⟨5994372247733077982223385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7992496330310770642964513 5994372247733077982223385)
                ·
                  refine ⟨4495779185799808486667539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994372247733077982223385 4495779185799808486667539)
                  ·
                    refine ⟨6743668778699712730001309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4495779185799808486667539 6743668778699712730001309)
                    ·
                      refine ⟨2528875792012392273750491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743668778699712730001309 2528875792012392273750491)
                      ·
                        rfl

theorem cell23_4924968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4924968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4924968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4924968 prefixEnd_4924968 := by exact prefixLift 4924968
  have htrace : WordTrace (prefixWord ++ tailWord_4924968) baseStart_4924968 baseEnd_4924968 := by
    simpa [prefixWord, tailWord_4924968, baseEnd_4924968] using wordTrace_append hprefix tailTrace_4924968
  have hstable : (prefixWord ++ tailWord_4924968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4924968).length < 2 ^ (prefixWord ++ tailWord_4924968).sum := by decide
  have hdescent : baseEnd_4924968 < baseStart_4924968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4924968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925027 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 2, 5]
def baseStart_4925027 : Nat := 118140960795 + 4925027 * 2 ^ 59
def prefixEnd_4925027 : Nat := 4983230072969 + 3 ^ 40 * 4925027 * 2
def baseEnd_4925027 : Nat := 842968695790335847637573

theorem tailTrace_4925027 : CollatzResearch.WordTrace tailWord_4925027 prefixEnd_4925027 842968695790335847637573 := by
  unfold tailWord_4925027
  simp only [CollatzResearch.WordTrace]
  refine ⟨179630491928475781491117335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119753661285650520994078223 179630491928475781491117335)
  ·
    refine ⟨269445737892713672236676003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179630491928475781491117335 269445737892713672236676003)
    ·
      refine ⟨404168606839070508355014005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269445737892713672236676003 404168606839070508355014005)
      ·
        refine ⟨37890806891162860158282563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 404168606839070508355014005 37890806891162860158282563)
        ·
          refine ⟨56836210336744290237423845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37890806891162860158282563 56836210336744290237423845)
          ·
            refine ⟨10656789438139554419516971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56836210336744290237423845 10656789438139554419516971)
            ·
              refine ⟨15985184157209331629275457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10656789438139554419516971 15985184157209331629275457)
              ·
                refine ⟨11988888117906998721956593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15985184157209331629275457 11988888117906998721956593)
                ·
                  refine ⟨8991666088430249041467445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11988888117906998721956593 8991666088430249041467445)
                  ·
                    refine ⟨842968695790335847637573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8991666088430249041467445 842968695790335847637573)
                    ·
                      rfl

theorem cell23_4925027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 5].length) (baseStart_4925027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925027 prefixEnd_4925027 := by exact prefixLift 4925027
  have htrace : WordTrace (prefixWord ++ tailWord_4925027) baseStart_4925027 baseEnd_4925027 := by
    simpa [prefixWord, tailWord_4925027, baseEnd_4925027] using wordTrace_append hprefix tailTrace_4925027
  have hstable : (prefixWord ++ tailWord_4925027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925027).length < 2 ^ (prefixWord ++ tailWord_4925027).sum := by decide
  have hdescent : baseEnd_4925027 < baseStart_4925027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925047 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 1, 6, 2]
def baseStart_4925047 : Nat := 118140960795 + 4925047 * 2 ^ 59
def prefixEnd_4925047 : Nat := 4983230072969 + 3 ^ 40 * 4925047 * 2
def baseEnd_4925047 : Nat := 2528916356984097464662627

theorem tailTrace_4925047 : CollatzResearch.WordTrace tailWord_4925047 prefixEnd_4925047 2528916356984097464662627 := by
  unfold tailWord_4925047
  simp only [CollatzResearch.WordTrace]
  refine ⟨179631221388403324906845395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119754147592268883271230263 179631221388403324906845395)
  ·
    refine ⟨269446832082604987360268093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179631221388403324906845395 269446832082604987360268093)
    ·
      refine ⟨101042562030976870260100535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269446832082604987360268093 101042562030976870260100535)
      ·
        refine ⟨151563843046465305390150803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101042562030976870260100535 151563843046465305390150803)
        ·
          refine ⟨227345764569697958085226205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151563843046465305390150803 227345764569697958085226205)
          ·
            refine ⟨85254661713636734281959827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227345764569697958085226205 85254661713636734281959827)
            ·
              refine ⟨127881992570455101422939741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85254661713636734281959827 127881992570455101422939741)
              ·
                refine ⟨47955747213920663033602403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127881992570455101422939741 47955747213920663033602403)
                ·
                  refine ⟨71933620820880994550403605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47955747213920663033602403 71933620820880994550403605)
                  ·
                    refine ⟨3371888475978796619550169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71933620820880994550403605 3371888475978796619550169)
                    ·
                      refine ⟨2528916356984097464662627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371888475978796619550169 2528916356984097464662627)
                      ·
                        rfl

theorem cell23_4925047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_4925047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925047 prefixEnd_4925047 := by exact prefixLift 4925047
  have htrace : WordTrace (prefixWord ++ tailWord_4925047) baseStart_4925047 baseEnd_4925047 := by
    simpa [prefixWord, tailWord_4925047, baseEnd_4925047] using wordTrace_append hprefix tailTrace_4925047
  have hstable : (prefixWord ++ tailWord_4925047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925047).length < 2 ^ (prefixWord ++ tailWord_4925047).sum := by decide
  have hdescent : baseEnd_4925047 < baseStart_4925047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925114 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_4925114 : Nat := 118140960795 + 4925114 * 2 ^ 59
def prefixEnd_4925114 : Nat := 4983230072969 + 3 ^ 40 * 4925114 * 2
def baseEnd_4925114 : Nat := 2528950760187948702524819

theorem tailTrace_4925114 : CollatzResearch.WordTrace tailWord_4925114 prefixEnd_4925114 2528950760187948702524819 := by
  unfold tailWord_4925114
  simp only [CollatzResearch.WordTrace]
  refine ⟨44908416269790148837383599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119755776719440396899689597 44908416269790148837383599)
  ·
    refine ⟨67362624404685223256075399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44908416269790148837383599 67362624404685223256075399)
    ·
      refine ⟨101043936607027834884113099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67362624404685223256075399 101043936607027834884113099)
      ·
        refine ⟨151565904910541752326169649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101043936607027834884113099 151565904910541752326169649)
        ·
          refine ⟨113674428682906314244627237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151565904910541752326169649 113674428682906314244627237)
          ·
            refine ⟨21313955378044933920867607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113674428682906314244627237 21313955378044933920867607)
            ·
              refine ⟨31970933067067400881301411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21313955378044933920867607 31970933067067400881301411)
              ·
                refine ⟨47956399600601101321952117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31970933067067400881301411 47956399600601101321952117)
                ·
                  refine ⟨4495912462556353248933011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47956399600601101321952117 4495912462556353248933011)
                  ·
                    refine ⟨6743868693834529873399517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4495912462556353248933011 6743868693834529873399517)
                    ·
                      refine ⟨2528950760187948702524819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743868693834529873399517 2528950760187948702524819)
                      ·
                        rfl

theorem cell23_4925114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_4925114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925114 prefixEnd_4925114 := by exact prefixLift 4925114
  have htrace : WordTrace (prefixWord ++ tailWord_4925114) baseStart_4925114 baseEnd_4925114 := by
    simpa [prefixWord, tailWord_4925114, baseEnd_4925114] using wordTrace_append hprefix tailTrace_4925114
  have hstable : (prefixWord ++ tailWord_4925114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925114).length < 2 ^ (prefixWord ++ tailWord_4925114).sum := by decide
  have hdescent : baseEnd_4925114 < baseStart_4925114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925117 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_4925117 : Nat := 118140960795 + 4925117 * 2 ^ 59
def prefixEnd_4925117 : Nat := 4983230072969 + 3 ^ 40 * 4925117 * 2
def baseEnd_4925117 : Nat := 842984100209970730262435

theorem tailTrace_4925117 : CollatzResearch.WordTrace tailWord_4925117 prefixEnd_4925117 842984100209970730262435 := by
  unfold tailWord_4925117
  simp only [CollatzResearch.WordTrace]
  refine ⟨179633774498149726861893605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119755849665433151241262403 179633774498149726861893605)
  ·
    refine ⟨33681332718403073786605051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179633774498149726861893605 33681332718403073786605051)
    ·
      refine ⟨50521999077604610679907577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33681332718403073786605051 50521999077604610679907577)
      ·
        refine ⟨37891499308203458009930683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50521999077604610679907577 37891499308203458009930683)
        ·
          refine ⟨56837248962305187014896025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37891499308203458009930683 56837248962305187014896025)
          ·
            refine ⟨42627936721728890261172019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56837248962305187014896025 42627936721728890261172019)
            ·
              refine ⟨63941905082593335391758029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42627936721728890261172019 63941905082593335391758029)
              ·
                refine ⟨23978214405972500771909261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63941905082593335391758029 23978214405972500771909261)
                ·
                  refine ⟨8991830402239687789465973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23978214405972500771909261 8991830402239687789465973)
                  ·
                    refine ⟨842984100209970730262435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8991830402239687789465973 842984100209970730262435)
                    ·
                      rfl

theorem cell23_4925117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_4925117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925117 prefixEnd_4925117 := by exact prefixLift 4925117
  have htrace : WordTrace (prefixWord ++ tailWord_4925117) baseStart_4925117 baseEnd_4925117 := by
    simpa [prefixWord, tailWord_4925117, baseEnd_4925117] using wordTrace_append hprefix tailTrace_4925117
  have hstable : (prefixWord ++ tailWord_4925117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925117).length < 2 ^ (prefixWord ++ tailWord_4925117).sum := by decide
  have hdescent : baseEnd_4925117 < baseStart_4925117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925134 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_4925134 : Nat := 118140960795 + 4925134 * 2 ^ 59
def prefixEnd_4925134 : Nat := 4983230072969 + 3 ^ 40 * 4925134 * 2
def baseEnd_4925134 : Nat := 842987009933679541424909

theorem tailTrace_4925134 : CollatzResearch.WordTrace tailWord_4925134 prefixEnd_4925134 842987009933679541424909 := by
  unfold tailWord_4925134
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454299317386017345657807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119756263026058759176841637 22454299317386017345657807)
  ·
    refine ⟨33681448976079026018486711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22454299317386017345657807 33681448976079026018486711)
    ·
      refine ⟨50522173464118539027730067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33681448976079026018486711 50522173464118539027730067)
      ·
        refine ⟨75783260196177808541595101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50522173464118539027730067 75783260196177808541595101)
        ·
          refine ⟨28418722573566678203098163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75783260196177808541595101 28418722573566678203098163)
          ·
            refine ⟨42628083860350017304647245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28418722573566678203098163 42628083860350017304647245)
            ·
              refine ⟨15985531447631256489242717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42628083860350017304647245 15985531447631256489242717)
              ·
                refine ⟨5994574292861721183466019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15985531447631256489242717 5994574292861721183466019)
                ·
                  refine ⟨8991861439292581775199029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5994574292861721183466019 8991861439292581775199029)
                  ·
                    refine ⟨842987009933679541424909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8991861439292581775199029 842987009933679541424909)
                    ·
                      rfl

theorem cell23_4925134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_4925134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925134 prefixEnd_4925134 := by exact prefixLift 4925134
  have htrace : WordTrace (prefixWord ++ tailWord_4925134) baseStart_4925134 baseEnd_4925134 := by
    simpa [prefixWord, tailWord_4925134, baseEnd_4925134] using wordTrace_append hprefix tailTrace_4925134
  have hstable : (prefixWord ++ tailWord_4925134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925134).length < 2 ^ (prefixWord ++ tailWord_4925134).sum := by decide
  have hdescent : baseEnd_4925134 < baseStart_4925134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925164 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_4925164 : Nat := 118140960795 + 4925164 * 2 ^ 59
def prefixEnd_4925164 : Nat := 4983230072969 + 3 ^ 40 * 4925164 * 2
def baseEnd_4925164 : Nat := 842992144740224502299863

theorem tailTrace_4925164 : CollatzResearch.WordTrace tailWord_4925164 prefixEnd_4925164 842992144740224502299863 := by
  unfold tailWord_4925164
  simp only [CollatzResearch.WordTrace]
  refine ⟨89817744364489726944427273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119756992485986302592569697 89817744364489726944427273)
  ·
    refine ⟨67363308273367295208320455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89817744364489726944427273 67363308273367295208320455)
    ·
      refine ⟨101044962410050942812480683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67363308273367295208320455 101044962410050942812480683)
      ·
        refine ⟨151567443615076414218721025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101044962410050942812480683 151567443615076414218721025)
        ·
          refine ⟨113675582711307310664040769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151567443615076414218721025 113675582711307310664040769)
          ·
            refine ⟨85256687033480482998030577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113675582711307310664040769 85256687033480482998030577)
            ·
              refine ⟨63942515275110362248522933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85256687033480482998030577 63942515275110362248522933)
              ·
                refine ⟨5994610807041596460799025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63942515275110362248522933 5994610807041596460799025)
                ·
                  refine ⟨4495958105281197345599269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994610807041596460799025 4495958105281197345599269)
                  ·
                    refine ⟨842992144740224502299863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4495958105281197345599269 842992144740224502299863)
                    ·
                      rfl

theorem cell23_4925164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_4925164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925164 prefixEnd_4925164 := by exact prefixLift 4925164
  have htrace : WordTrace (prefixWord ++ tailWord_4925164) baseStart_4925164 baseEnd_4925164 := by
    simpa [prefixWord, tailWord_4925164, baseEnd_4925164] using wordTrace_append hprefix tailTrace_4925164
  have hstable : (prefixWord ++ tailWord_4925164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925164).length < 2 ^ (prefixWord ++ tailWord_4925164).sum := by decide
  have hdescent : baseEnd_4925164 < baseStart_4925164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925167 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_4925167 : Nat := 118140960795 + 4925167 * 2 ^ 59
def prefixEnd_4925167 : Nat := 4983230072969 + 3 ^ 40 * 4925167 * 2
def baseEnd_4925167 : Nat := 2528977974662636995162075

theorem tailTrace_4925167 : CollatzResearch.WordTrace tailWord_4925167 prefixEnd_4925167 2528977974662636995162075 := by
  unfold tailWord_4925167
  simp only [CollatzResearch.WordTrace]
  refine ⟨179635598147968585401213755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119757065431979056934142503 179635598147968585401213755)
  ·
    refine ⟨269453397221952878101820633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179635598147968585401213755 269453397221952878101820633)
    ·
      refine ⟨202090047916464658576365475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269453397221952878101820633 202090047916464658576365475)
      ·
        refine ⟨303135071874696987864548213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202090047916464658576365475 303135071874696987864548213)
        ·
          refine ⟨28418912988252842612301395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 303135071874696987864548213 28418912988252842612301395)
          ·
            refine ⟨42628369482379263918452093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28418912988252842612301395 42628369482379263918452093)
            ·
              refine ⟨15985638555892223969419535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42628369482379263918452093 15985638555892223969419535)
              ·
                refine ⟨23978457833838335954129303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15985638555892223969419535 23978457833838335954129303)
                ·
                  refine ⟨35967686750757503931193955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23978457833838335954129303 35967686750757503931193955)
                  ·
                    refine ⟨53951530126136255896790933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35967686750757503931193955 53951530126136255896790933)
                    ·
                      refine ⟨2528977974662636995162075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53951530126136255896790933 2528977974662636995162075)
                      ·
                        rfl

theorem cell23_4925167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_4925167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925167 prefixEnd_4925167 := by exact prefixLift 4925167
  have htrace : WordTrace (prefixWord ++ tailWord_4925167) baseStart_4925167 baseEnd_4925167 := by
    simpa [prefixWord, tailWord_4925167, baseEnd_4925167] using wordTrace_append hprefix tailTrace_4925167
  have hstable : (prefixWord ++ tailWord_4925167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925167).length < 2 ^ (prefixWord ++ tailWord_4925167).sum := by decide
  have hdescent : baseEnd_4925167 < baseStart_4925167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925171 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 3, 2, 2]
def baseStart_4925171 : Nat := 118140960795 + 4925171 * 2 ^ 59
def prefixEnd_4925171 : Nat := 4983230072969 + 3 ^ 40 * 4925171 * 2
def baseEnd_4925171 : Nat := 2528980028585254979512057

theorem tailTrace_4925171 : CollatzResearch.WordTrace tailWord_4925171 prefixEnd_4925171 2528980028585254979512057 := by
  unfold tailWord_4925171
  simp only [CollatzResearch.WordTrace]
  refine ⟨179635744039954094084359367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119757162693302729389572911 179635744039954094084359367)
  ·
    refine ⟨269453616059931141126539051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179635744039954094084359367 269453616059931141126539051)
    ·
      refine ⟨404180424089896711689808577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269453616059931141126539051 404180424089896711689808577)
      ·
        refine ⟨303135318067422533767356433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404180424089896711689808577 303135318067422533767356433)
        ·
          refine ⟨227351488550566900325517325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303135318067422533767356433 227351488550566900325517325)
          ·
            refine ⟨85256808206462587622068997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227351488550566900325517325 85256808206462587622068997)
            ·
              refine ⟨15985651538711735179137937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85256808206462587622068997 15985651538711735179137937)
              ·
                refine ⟨11989238654033801384353453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15985651538711735179137937 11989238654033801384353453)
                ·
                  refine ⟨4495964495262675519132545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11989238654033801384353453 4495964495262675519132545)
                  ·
                    refine ⟨3371973371447006639349409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4495964495262675519132545 3371973371447006639349409)
                    ·
                      refine ⟨2528980028585254979512057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371973371447006639349409 2528980028585254979512057)
                      ·
                        rfl

theorem cell23_4925171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 2, 2].length) (baseStart_4925171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925171 prefixEnd_4925171 := by exact prefixLift 4925171
  have htrace : WordTrace (prefixWord ++ tailWord_4925171) baseStart_4925171 baseEnd_4925171 := by
    simpa [prefixWord, tailWord_4925171, baseEnd_4925171] using wordTrace_append hprefix tailTrace_4925171
  have hstable : (prefixWord ++ tailWord_4925171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925171).length < 2 ^ (prefixWord ++ tailWord_4925171).sum := by decide
  have hdescent : baseEnd_4925171 < baseStart_4925171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925182 : List Nat := [4, 2, 2, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4925182 : Nat := 118140960795 + 4925182 * 2 ^ 59
def prefixEnd_4925182 : Nat := 4983230072969 + 3 ^ 40 * 4925182 * 2
def baseEnd_4925182 : Nat := 2528985676872454436474507

theorem tailTrace_4925182 : CollatzResearch.WordTrace tailWord_4925182 prefixEnd_4925182 2528985676872454436474507 := by
  unfold tailWord_4925182
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454518155364280370376225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119757430161942828642006533 22454518155364280370376225)
  ·
    refine ⟨16840888616523210277782169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22454518155364280370376225 16840888616523210277782169)
    ·
      refine ⟨12630666462392407708336627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16840888616523210277782169 12630666462392407708336627)
      ·
        refine ⟨18945999693588611562504941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12630666462392407708336627 18945999693588611562504941)
        ·
          refine ⟨7104749885095729335939353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18945999693588611562504941 7104749885095729335939353)
          ·
            refine ⟨5328562413821797001954515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7104749885095729335939353 5328562413821797001954515)
            ·
              refine ⟨7992843620732695502931773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328562413821797001954515 7992843620732695502931773)
              ·
                refine ⟨2997316357774760813599415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7992843620732695502931773 2997316357774760813599415)
                ·
                  refine ⟨4495974536662141220399123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997316357774760813599415 4495974536662141220399123)
                  ·
                    refine ⟨6743961804993211830598685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4495974536662141220399123 6743961804993211830598685)
                    ·
                      refine ⟨2528985676872454436474507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6743961804993211830598685 2528985676872454436474507)
                      ·
                        rfl

theorem cell23_4925182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4925182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925182 prefixEnd_4925182 := by exact prefixLift 4925182
  have htrace : WordTrace (prefixWord ++ tailWord_4925182) baseStart_4925182 baseEnd_4925182 := by
    simpa [prefixWord, tailWord_4925182, baseEnd_4925182] using wordTrace_append hprefix tailTrace_4925182
  have hstable : (prefixWord ++ tailWord_4925182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925182).length < 2 ^ (prefixWord ++ tailWord_4925182).sum := by decide
  have hdescent : baseEnd_4925182 < baseStart_4925182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925191 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4925191 : Nat := 118140960795 + 4925191 * 2 ^ 59
def prefixEnd_4925191 : Nat := 4983230072969 + 3 ^ 40 * 4925191 * 2
def baseEnd_4925191 : Nat := 2528990298198344901261965

theorem tailTrace_4925191 : CollatzResearch.WordTrace tailWord_4925191 prefixEnd_4925191 2528990298198344901261965 := by
  unfold tailWord_4925191
  simp only [CollatzResearch.WordTrace]
  refine ⟨179636473499881637500087427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119757648999921091666724951 179636473499881637500087427)
  ·
    refine ⟨269454710249822456250131141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179636473499881637500087427 269454710249822456250131141)
    ·
      refine ⟨50522758171841710546899589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269454710249822456250131141 50522758171841710546899589)
      ·
        refine ⟨9473017157220320727543673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50522758171841710546899589 9473017157220320727543673)
        ·
          refine ⟨7104762867915240545657755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9473017157220320727543673 7104762867915240545657755)
          ·
            refine ⟨10657144301872860818486633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104762867915240545657755 10657144301872860818486633)
            ·
              refine ⟨7992858226404645613864975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10657144301872860818486633 7992858226404645613864975)
              ·
                refine ⟨11989287339606968420797463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7992858226404645613864975 11989287339606968420797463)
                ·
                  refine ⟨17983931009410452631196195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11989287339606968420797463 17983931009410452631196195)
                  ·
                    refine ⟨26975896514115678946794293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17983931009410452631196195 26975896514115678946794293)
                    ·
                      refine ⟨2528990298198344901261965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26975896514115678946794293 2528990298198344901261965)
                      ·
                        rfl

theorem cell23_4925191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4925191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925191 prefixEnd_4925191 := by exact prefixLift 4925191
  have htrace : WordTrace (prefixWord ++ tailWord_4925191) baseStart_4925191 baseEnd_4925191 := by
    simpa [prefixWord, tailWord_4925191, baseEnd_4925191] using wordTrace_append hprefix tailTrace_4925191
  have hstable : (prefixWord ++ tailWord_4925191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925191).length < 2 ^ (prefixWord ++ tailWord_4925191).sum := by decide
  have hdescent : baseEnd_4925191 < baseStart_4925191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925238 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4925238 : Nat := 118140960795 + 4925238 * 2 ^ 59
def prefixEnd_4925238 : Nat := 4983230072969 + 3 ^ 40 * 4925238 * 2
def baseEnd_4925238 : Nat := 2529014431789106217374249

theorem tailTrace_4925238 : CollatzResearch.WordTrace tailWord_4925238 prefixEnd_4925238 2529014431789106217374249 := by
  unfold tailWord_4925238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227386733169460282940523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119758791820474243018032245 11227386733169460282940523)
  ·
    refine ⟨16841080099754190424410785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11227386733169460282940523 16841080099754190424410785)
    ·
      refine ⟨12630810074815642818308089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16841080099754190424410785 12630810074815642818308089)
      ·
        refine ⟨9473107556111732113731067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12630810074815642818308089 9473107556111732113731067)
        ·
          refine ⟨14209661334167598170596601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473107556111732113731067 14209661334167598170596601)
          ·
            refine ⟨10657246000625698627947451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14209661334167598170596601 10657246000625698627947451)
            ·
              refine ⟨15985869000938547941921177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10657246000625698627947451 15985869000938547941921177)
              ·
                refine ⟨11989401750703910956440883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15985869000938547941921177 11989401750703910956440883)
                ·
                  refine ⟨17984102626055866434661325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11989401750703910956440883 17984102626055866434661325)
                  ·
                    refine ⟨6744038484770949912997997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17984102626055866434661325 6744038484770949912997997)
                    ·
                      refine ⟨2529014431789106217374249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6744038484770949912997997 2529014431789106217374249)
                      ·
                        rfl

theorem cell23_4925238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4925238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925238 prefixEnd_4925238 := by exact prefixLift 4925238
  have htrace : WordTrace (prefixWord ++ tailWord_4925238) baseStart_4925238 baseEnd_4925238 := by
    simpa [prefixWord, tailWord_4925238, baseEnd_4925238] using wordTrace_append hprefix tailTrace_4925238
  have hstable : (prefixWord ++ tailWord_4925238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925238).length < 2 ^ (prefixWord ++ tailWord_4925238).sum := by decide
  have hdescent : baseEnd_4925238 < baseStart_4925238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925261 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4925261 : Nat := 118140960795 + 4925261 * 2 ^ 59
def prefixEnd_4925261 : Nat := 4983230072969 + 3 ^ 40 * 4925261 * 2
def baseEnd_4925261 : Nat := 2529026241844159627386643

theorem tailTrace_4925261 : CollatzResearch.WordTrace tailWord_4925261 prefixEnd_4925261 2529026241844159627386643 := by
  unfold tailWord_4925261
  simp only [CollatzResearch.WordTrace]
  refine ⟨179639026609628039455135637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119759351073085359636757091 179639026609628039455135637)
  ·
    refine ⟨8420579372326314349459483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179639026609628039455135637 8420579372326314349459483)
    ·
      refine ⟨12630869058489471524189225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8420579372326314349459483 12630869058489471524189225)
      ·
        refine ⟨9473151793867103643141919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12630869058489471524189225 9473151793867103643141919)
        ·
          refine ⟨14209727690800655464712879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473151793867103643141919 14209727690800655464712879)
          ·
            refine ⟨21314591536200983197069319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14209727690800655464712879 21314591536200983197069319)
            ·
              refine ⟨31971887304301474795603979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21314591536200983197069319 31971887304301474795603979)
              ·
                refine ⟨47957830956452212193405969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31971887304301474795603979 47957830956452212193405969)
                ·
                  refine ⟨35968373217339159145054477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47957830956452212193405969 35968373217339159145054477)
                  ·
                    refine ⟨13488139956502184679395429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35968373217339159145054477 13488139956502184679395429)
                    ·
                      refine ⟨2529026241844159627386643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13488139956502184679395429 2529026241844159627386643)
                      ·
                        rfl

theorem cell23_4925261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4925261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925261 prefixEnd_4925261 := by exact prefixLift 4925261
  have htrace : WordTrace (prefixWord ++ tailWord_4925261) baseStart_4925261 baseEnd_4925261 := by
    simpa [prefixWord, tailWord_4925261, baseEnd_4925261] using wordTrace_append hprefix tailTrace_4925261
  have hstable : (prefixWord ++ tailWord_4925261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925261).length < 2 ^ (prefixWord ++ tailWord_4925261).sum := by decide
  have hdescent : baseEnd_4925261 < baseStart_4925261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925274 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_4925274 : Nat := 118140960795 + 4925274 * 2 ^ 59
def prefixEnd_4925274 : Nat := 4983230072969 + 3 ^ 40 * 4925274 * 2
def baseEnd_4925274 : Nat := 2529032917092668076524083

theorem tailTrace_4925274 : CollatzResearch.WordTrace tailWord_4925274 prefixEnd_4925274 2529032917092668076524083 := by
  unfold tailWord_4925274
  simp only [CollatzResearch.WordTrace]
  refine ⟨44909875189645235668839719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119759667172387295116905917 44909875189645235668839719)
  ·
    refine ⟨67364812784467853503259579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44909875189645235668839719 67364812784467853503259579)
    ·
      refine ⟨101047219176701780254889369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67364812784467853503259579 101047219176701780254889369)
      ·
        refine ⟨75785414382526335191167027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101047219176701780254889369 75785414382526335191167027)
        ·
          refine ⟨113678121573789502786750541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75785414382526335191167027 113678121573789502786750541)
          ·
            refine ⟨42629295590171063545031453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113678121573789502786750541 42629295590171063545031453)
            ·
              refine ⟨15985985846314148829386795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42629295590171063545031453 15985985846314148829386795)
              ·
                refine ⟨23978978769471223244080193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15985985846314148829386795 23978978769471223244080193)
                ·
                  refine ⟨17984234077103417433060145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23978978769471223244080193 17984234077103417433060145)
                  ·
                    refine ⟨13488175557827563074795109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17984234077103417433060145 13488175557827563074795109)
                    ·
                      refine ⟨2529032917092668076524083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13488175557827563074795109 2529032917092668076524083)
                      ·
                        rfl

theorem cell23_4925274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_4925274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925274 prefixEnd_4925274 := by exact prefixLift 4925274
  have htrace : WordTrace (prefixWord ++ tailWord_4925274) baseStart_4925274 baseEnd_4925274 := by
    simpa [prefixWord, tailWord_4925274, baseEnd_4925274] using wordTrace_append hprefix tailTrace_4925274
  have hstable : (prefixWord ++ tailWord_4925274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925274).length < 2 ^ (prefixWord ++ tailWord_4925274).sum := by decide
  have hdescent : baseEnd_4925274 < baseStart_4925274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925351 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4925351 : Nat := 118140960795 + 4925351 * 2 ^ 59
def prefixEnd_4925351 : Nat := 4983230072969 + 3 ^ 40 * 4925351 * 2
def baseEnd_4925351 : Nat := 2529072455103064275261229

theorem tailTrace_4925351 : CollatzResearch.WordTrace tailWord_4925351 prefixEnd_4925351 2529072455103064275261229 := by
  unfold tailWord_4925351
  simp only [CollatzResearch.WordTrace]
  refine ⟨179642309179301984825911907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119761539452867989883941271 179642309179301984825911907)
  ·
    refine ⟨269463463768952977238867861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179642309179301984825911907 269463463768952977238867861)
    ·
      refine ⟨12631099864169670808071931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 269463463768952977238867861 12631099864169670808071931)
      ·
        refine ⟨18946649796254506212107897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12631099864169670808071931 18946649796254506212107897)
        ·
          refine ⟨14209987347190879659080923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18946649796254506212107897 14209987347190879659080923)
          ·
            refine ⟨21314981020786319488621385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14209987347190879659080923 21314981020786319488621385)
            ·
              refine ⟨15986235765589739616466039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21314981020786319488621385 15986235765589739616466039)
              ·
                refine ⟨23979353648384609424699059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15986235765589739616466039 23979353648384609424699059)
                ·
                  refine ⟨35969030472576914137048589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23979353648384609424699059 35969030472576914137048589)
                  ·
                    refine ⟨13488386427216342801393221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35969030472576914137048589 13488386427216342801393221)
                    ·
                      refine ⟨2529072455103064275261229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13488386427216342801393221 2529072455103064275261229)
                      ·
                        rfl

theorem cell23_4925351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4925351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925351 prefixEnd_4925351 := by exact prefixLift 4925351
  have htrace : WordTrace (prefixWord ++ tailWord_4925351) baseStart_4925351 baseEnd_4925351 := by
    simpa [prefixWord, tailWord_4925351, baseEnd_4925351] using wordTrace_append hprefix tailTrace_4925351
  have hstable : (prefixWord ++ tailWord_4925351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925351).length < 2 ^ (prefixWord ++ tailWord_4925351).sum := by decide
  have hdescent : baseEnd_4925351 < baseStart_4925351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925352 : List Nat := [2, 1, 6, 2, 1, 2, 1, 3, 5]
def baseStart_4925352 : Nat := 118140960795 + 4925352 * 2 ^ 59
def prefixEnd_4925352 : Nat := 4983230072969 + 3 ^ 40 * 4925352 * 2
def baseEnd_4925352 : Nat := 281008107620413196816525

theorem tailTrace_4925352 : CollatzResearch.WordTrace tailWord_4925352 prefixEnd_4925352 281008107620413196816525 := by
  unfold tailWord_4925352
  simp only [CollatzResearch.WordTrace]
  refine ⟨89821172826149180998349155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119761563768198907997798873 89821172826149180998349155)
  ·
    refine ⟨134731759239223771497523733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89821172826149180998349155 134731759239223771497523733)
    ·
      refine ⟨6315551214338614288946425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134731759239223771497523733 6315551214338614288946425)
      ·
        refine ⟨4736663410753960716709819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6315551214338614288946425 4736663410753960716709819)
        ·
          refine ⟨7104995116130941075064729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4736663410753960716709819 7104995116130941075064729)
          ·
            refine ⟨5328746337098205806298547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7104995116130941075064729 5328746337098205806298547)
            ·
              refine ⟨7993119505647308709447821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328746337098205806298547 7993119505647308709447821)
              ·
                refine ⟨2997419814617740766042933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7993119505647308709447821 2997419814617740766042933)
                ·
                  refine ⟨281008107620413196816525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2997419814617740766042933 281008107620413196816525)
                  ·
                    rfl

theorem cell23_4925352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 5].length) (baseStart_4925352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925352 prefixEnd_4925352 := by exact prefixLift 4925352
  have htrace : WordTrace (prefixWord ++ tailWord_4925352) baseStart_4925352 baseEnd_4925352 := by
    simpa [prefixWord, tailWord_4925352, baseEnd_4925352] using wordTrace_append hprefix tailTrace_4925352
  have hstable : (prefixWord ++ tailWord_4925352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925352).length < 2 ^ (prefixWord ++ tailWord_4925352).sum := by decide
  have hdescent : baseEnd_4925352 < baseStart_4925352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925405 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4925405 : Nat := 118140960795 + 4925405 * 2 ^ 59
def prefixEnd_4925405 : Nat := 4983230072969 + 3 ^ 40 * 4925405 * 2
def baseEnd_4925405 : Nat := 2529100183058407063985981

theorem tailTrace_4925405 : CollatzResearch.WordTrace tailWord_4925405 prefixEnd_4925405 2529100183058407063985981 := by
  unfold tailWord_4925405
  simp only [CollatzResearch.WordTrace]
  refine ⟨179644278721106352048377669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119762852480737568032251779 179644278721106352048377669)
  ·
    refine ⟨33683302260207441009070813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179644278721106352048377669 33683302260207441009070813)
    ·
      refine ⟨12631238347577790378401555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33683302260207441009070813 12631238347577790378401555)
      ·
        refine ⟨18946857521366685567602333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12631238347577790378401555 18946857521366685567602333)
        ·
          refine ⟨7105071570512507087850875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18946857521366685567602333 7105071570512507087850875)
          ·
            refine ⟨10657607355768760631776313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105071570512507087850875 10657607355768760631776313)
            ·
              refine ⟨7993205516826570473832235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10657607355768760631776313 7993205516826570473832235)
              ·
                refine ⟨11989808275239855710748353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993205516826570473832235 11989808275239855710748353)
                ·
                  refine ⟨8992356206429891783061265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11989808275239855710748353 8992356206429891783061265)
                  ·
                    refine ⟨6744267154822418837295949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8992356206429891783061265 6744267154822418837295949)
                    ·
                      refine ⟨2529100183058407063985981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6744267154822418837295949 2529100183058407063985981)
                      ·
                        rfl

theorem cell23_4925405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4925405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925405 prefixEnd_4925405 := by exact prefixLift 4925405
  have htrace : WordTrace (prefixWord ++ tailWord_4925405) baseStart_4925405 baseEnd_4925405 := by
    simpa [prefixWord, tailWord_4925405, baseEnd_4925405] using wordTrace_append hprefix tailTrace_4925405
  have hstable : (prefixWord ++ tailWord_4925405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925405).length < 2 ^ (prefixWord ++ tailWord_4925405).sum := by decide
  have hdescent : baseEnd_4925405 < baseStart_4925405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925438 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4925438 : Nat := 118140960795 + 4925438 * 2 ^ 59
def prefixEnd_4925438 : Nat := 4983230072969 + 3 ^ 40 * 4925438 * 2
def baseEnd_4925438 : Nat := 843039042640001811624443

theorem tailTrace_4925438 : CollatzResearch.WordTrace tailWord_4925438 prefixEnd_4925438 843039042640001811624443 := by
  unfold tailWord_4925438
  simp only [CollatzResearch.WordTrace]
  refine ⟨22455685291248349835541121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119763654886657865789552645 22455685291248349835541121)
  ·
    refine ⟨16841763968436262376655841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22455685291248349835541121 16841763968436262376655841)
    ·
      refine ⟨12631322976327196782491881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16841763968436262376655841 12631322976327196782491881)
      ·
        refine ⟨9473492232245397586868911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12631322976327196782491881 9473492232245397586868911)
        ·
          refine ⟨14210238348368096380303367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473492232245397586868911 14210238348368096380303367)
          ·
            refine ⟨21315357522552144570455051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14210238348368096380303367 21315357522552144570455051)
            ·
              refine ⟨31973036283828216855682577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21315357522552144570455051 31973036283828216855682577)
              ·
                refine ⟨23979777212871162641761933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31973036283828216855682577 23979777212871162641761933)
                ·
                  refine ⟨8992416454826685990660725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23979777212871162641761933 8992416454826685990660725)
                  ·
                    refine ⟨843039042640001811624443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8992416454826685990660725 843039042640001811624443)
                    ·
                      rfl

theorem cell23_4925438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4925438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925438 prefixEnd_4925438 := by exact prefixLift 4925438
  have htrace : WordTrace (prefixWord ++ tailWord_4925438) baseStart_4925438 baseEnd_4925438 := by
    simpa [prefixWord, tailWord_4925438, baseEnd_4925438] using wordTrace_append hprefix tailTrace_4925438
  have hstable : (prefixWord ++ tailWord_4925438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925438).length < 2 ^ (prefixWord ++ tailWord_4925438).sum := by decide
  have hdescent : baseEnd_4925438 < baseStart_4925438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925441 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4925441 : Nat := 118140960795 + 4925441 * 2 ^ 59
def prefixEnd_4925441 : Nat := 4983230072969 + 3 ^ 40 * 4925441 * 2
def baseEnd_4925441 : Nat := 2529118668361968923135815

theorem tailTrace_4925441 : CollatzResearch.WordTrace tailWord_4925441 prefixEnd_4925441 2529118668361968923135815 := by
  unfold tailWord_4925441
  simp only [CollatzResearch.WordTrace]
  refine ⟨179645591748975930196688177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119763727832650620131125451 179645591748975930196688177)
  ·
    refine ⟨134734193811731947647516133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179645591748975930196688177 134734193811731947647516133)
    ·
      refine ⟨25262661339699740183909275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134734193811731947647516133 25262661339699740183909275)
      ·
        refine ⟨37893992009549610275863913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25262661339699740183909275 37893992009549610275863913)
        ·
          refine ⟨28420494007162207706897935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37893992009549610275863913 28420494007162207706897935)
          ·
            refine ⟨42630741010743311560346903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28420494007162207706897935 42630741010743311560346903)
            ·
              refine ⟨63946111516114967340520355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42630741010743311560346903 63946111516114967340520355)
              ·
                refine ⟨95919167274172451010780533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63946111516114967340520355 95919167274172451010780533)
                ·
                  refine ⟨8992421931953667282260675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95919167274172451010780533 8992421931953667282260675)
                  ·
                    refine ⟨13488632897930500923391013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8992421931953667282260675 13488632897930500923391013)
                    ·
                      refine ⟨2529118668361968923135815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13488632897930500923391013 2529118668361968923135815)
                      ·
                        rfl

theorem cell23_4925441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4925441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925441 prefixEnd_4925441 := by exact prefixLift 4925441
  have htrace : WordTrace (prefixWord ++ tailWord_4925441) baseStart_4925441 baseEnd_4925441 := by
    simpa [prefixWord, tailWord_4925441, baseEnd_4925441] using wordTrace_append hprefix tailTrace_4925441
  have hstable : (prefixWord ++ tailWord_4925441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925441).length < 2 ^ (prefixWord ++ tailWord_4925441).sum := by decide
  have hdescent : baseEnd_4925441 < baseStart_4925441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925451 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 1, 6]
def baseStart_4925451 : Nat := 118140960795 + 4925451 * 2 ^ 59
def prefixEnd_4925451 : Nat := 4983230072969 + 3 ^ 40 * 4925451 * 2
def baseEnd_4925451 : Nat := 843041267722837961336923

theorem tailTrace_4925451 : CollatzResearch.WordTrace tailWord_4925451 prefixEnd_4925451 843041267722837961336923 := by
  unfold tailWord_4925451
  simp only [CollatzResearch.WordTrace]
  refine ⟨179645956478939701904552207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119763970985959801269701471 179645956478939701904552207)
  ·
    refine ⟨269468934718409552856828311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179645956478939701904552207 269468934718409552856828311)
    ·
      refine ⟨404203402077614329285242467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269468934718409552856828311 404203402077614329285242467)
      ·
        refine ⟨606305103116421493927863701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404203402077614329285242467 606305103116421493927863701)
        ·
          refine ⟨28420551708582257527868611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 606305103116421493927863701 28420551708582257527868611)
          ·
            refine ⟨42630827562873386291802917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28420551708582257527868611 42630827562873386291802917)
            ·
              refine ⟨7993280168038759929713047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42630827562873386291802917 7993280168038759929713047)
              ·
                refine ⟨11989920252058139894569571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993280168038759929713047 11989920252058139894569571)
                ·
                  refine ⟨17984880378087209841854357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11989920252058139894569571 17984880378087209841854357)
                  ·
                    refine ⟨843041267722837961336923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17984880378087209841854357 843041267722837961336923)
                    ·
                      rfl

theorem cell23_4925451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 6].length) (baseStart_4925451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925451 prefixEnd_4925451 := by exact prefixLift 4925451
  have htrace : WordTrace (prefixWord ++ tailWord_4925451) baseStart_4925451 baseEnd_4925451 := by
    simpa [prefixWord, tailWord_4925451, baseEnd_4925451] using wordTrace_append hprefix tailTrace_4925451
  have hstable : (prefixWord ++ tailWord_4925451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925451).length < 2 ^ (prefixWord ++ tailWord_4925451).sum := by decide
  have hdescent : baseEnd_4925451 < baseStart_4925451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925471 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_4925471 : Nat := 118140960795 + 4925471 * 2 ^ 59
def prefixEnd_4925471 : Nat := 4983230072969 + 3 ^ 40 * 4925471 * 2
def baseEnd_4925471 : Nat := 2529134072781603805760677

theorem tailTrace_4925471 : CollatzResearch.WordTrace tailWord_4925471 prefixEnd_4925471 2529134072781603805760677 := by
  unfold tailWord_4925471
  simp only [CollatzResearch.WordTrace]
  refine ⟨179646685938867245320280267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119764457292578163546853511 179646685938867245320280267)
  ·
    refine ⟨269470028908300867980420401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179646685938867245320280267 269470028908300867980420401)
    ·
      refine ⟨202102521681225650985315301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269470028908300867980420401 202102521681225650985315301)
      ·
        refine ⟨37894222815229809559746619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202102521681225650985315301 37894222815229809559746619)
        ·
          refine ⟨56841334222844714339619929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37894222815229809559746619 56841334222844714339619929)
          ·
            refine ⟨42631000667133535754714947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56841334222844714339619929 42631000667133535754714947)
            ·
              refine ⟨63946501000700303632072421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42631000667133535754714947 63946501000700303632072421)
              ·
                refine ⟨11989968937631306931013579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63946501000700303632072421 11989968937631306931013579)
                ·
                  refine ⟨17984953406446960396520369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11989968937631306931013579 17984953406446960396520369)
                  ·
                    refine ⟨13488715054835220297390277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17984953406446960396520369 13488715054835220297390277)
                    ·
                      refine ⟨2529134072781603805760677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13488715054835220297390277 2529134072781603805760677)
                      ·
                        rfl

theorem cell23_4925471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_4925471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925471 prefixEnd_4925471 := by exact prefixLift 4925471
  have htrace : WordTrace (prefixWord ++ tailWord_4925471) baseStart_4925471 baseEnd_4925471 := by
    simpa [prefixWord, tailWord_4925471, baseEnd_4925471] using wordTrace_append hprefix tailTrace_4925471
  have hstable : (prefixWord ++ tailWord_4925471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925471).length < 2 ^ (prefixWord ++ tailWord_4925471).sum := by decide
  have hdescent : baseEnd_4925471 < baseStart_4925471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925491 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 3]
def baseStart_4925491 : Nat := 118140960795 + 4925491 * 2 ^ 59
def prefixEnd_4925491 : Nat := 4983230072969 + 3 ^ 40 * 4925491 * 2
def baseEnd_4925491 : Nat := 2529144342394693727510585

theorem tailTrace_4925491 : CollatzResearch.WordTrace tailWord_4925491 prefixEnd_4925491 2529144342394693727510585 := by
  unfold tailWord_4925491
  simp only [CollatzResearch.WordTrace]
  refine ⟨179647415398794788736008327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119764943599196525824005551 179647415398794788736008327)
  ·
    refine ⟨269471123098192183104012491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179647415398794788736008327 269471123098192183104012491)
    ·
      refine ⟨404206684647288274656018737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269471123098192183104012491 404206684647288274656018737)
      ·
        refine ⟨303155013485466205992014053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404206684647288274656018737 303155013485466205992014053)
        ·
          refine ⟨56841565028524913623502635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303155013485466205992014053 56841565028524913623502635)
          ·
            refine ⟨85262347542787370435253953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56841565028524913623502635 85262347542787370435253953)
            ·
              refine ⟨63946760657090527826440465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85262347542787370435253953 63946760657090527826440465)
              ·
                refine ⟨47960070492817895869830349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63946760657090527826440465 47960070492817895869830349)
                ·
                  refine ⟨17985026434806710951186381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47960070492817895869830349 17985026434806710951186381)
                  ·
                    refine ⟨6744384913052516606694893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17985026434806710951186381 6744384913052516606694893)
                    ·
                      refine ⟨2529144342394693727510585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6744384913052516606694893 2529144342394693727510585)
                      ·
                        rfl

theorem cell23_4925491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_4925491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925491 prefixEnd_4925491 := by exact prefixLift 4925491
  have htrace : WordTrace (prefixWord ++ tailWord_4925491) baseStart_4925491 baseEnd_4925491 := by
    simpa [prefixWord, tailWord_4925491, baseEnd_4925491] using wordTrace_append hprefix tailTrace_4925491
  have hstable : (prefixWord ++ tailWord_4925491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925491).length < 2 ^ (prefixWord ++ tailWord_4925491).sum := by decide
  have hdescent : baseEnd_4925491 < baseStart_4925491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925502 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_4925502 : Nat := 118140960795 + 4925502 * 2 ^ 59
def prefixEnd_4925502 : Nat := 4983230072969 + 3 ^ 40 * 4925502 * 2
def baseEnd_4925502 : Nat := 843049996893964394824345

theorem tailTrace_4925502 : CollatzResearch.WordTrace tailWord_4925502 prefixEnd_4925502 843049996893964394824345 := by
  unfold tailWord_4925502
  simp only [CollatzResearch.WordTrace]
  refine ⟨22455977075219367201832345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119765211067836625076439173 22455977075219367201832345)
  ·
    refine ⟨16841982806414525401374259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22455977075219367201832345 16841982806414525401374259)
    ·
      refine ⟨25262974209621788102061389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16841982806414525401374259 25262974209621788102061389)
      ·
        refine ⟨9473615328608170538273021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25262974209621788102061389 9473615328608170538273021)
        ·
          refine ⟨3552605748228063951852383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9473615328608170538273021 3552605748228063951852383)
          ·
            refine ⟨5328908622342095927778575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552605748228063951852383 5328908622342095927778575)
            ·
              refine ⟨7993362933513143891667863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328908622342095927778575 7993362933513143891667863)
              ·
                refine ⟨11990044400269715837501795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993362933513143891667863 11990044400269715837501795)
                ·
                  refine ⟨17985066600404573756252693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11990044400269715837501795 17985066600404573756252693)
                  ·
                    refine ⟨843049996893964394824345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17985066600404573756252693 843049996893964394824345)
                    ·
                      rfl

theorem cell23_4925502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_4925502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925502 prefixEnd_4925502 := by exact prefixLift 4925502
  have htrace : WordTrace (prefixWord ++ tailWord_4925502) baseStart_4925502 baseEnd_4925502 := by
    simpa [prefixWord, tailWord_4925502, baseEnd_4925502] using wordTrace_append hprefix tailTrace_4925502
  have hstable : (prefixWord ++ tailWord_4925502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925502).length < 2 ^ (prefixWord ++ tailWord_4925502).sum := by decide
  have hdescent : baseEnd_4925502 < baseStart_4925502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925505 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_4925505 : Nat := 118140960795 + 4925505 * 2 ^ 59
def prefixEnd_4925505 : Nat := 4983230072969 + 3 ^ 40 * 4925505 * 2
def baseEnd_4925505 : Nat := 2529151531123856672735521

theorem tailTrace_4925505 : CollatzResearch.WordTrace tailWord_4925505 prefixEnd_4925505 2529151531123856672735521 := by
  unfold tailWord_4925505
  simp only [CollatzResearch.WordTrace]
  refine ⟨179647926020744069127017969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119765284013829379418011979 179647926020744069127017969)
  ·
    refine ⟨134735944515558051845263477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179647926020744069127017969 134735944515558051845263477)
    ·
      refine ⟨12631494798333567360493451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134735944515558051845263477 12631494798333567360493451)
      ·
        refine ⟨18947242197500351040740177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12631494798333567360493451 18947242197500351040740177)
        ·
          refine ⟨14210431648125263280555133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18947242197500351040740177 14210431648125263280555133)
          ·
            refine ⟨5328911868046973730208175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14210431648125263280555133 5328911868046973730208175)
            ·
              refine ⟨7993367802070460595312263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328911868046973730208175 7993367802070460595312263)
              ·
                refine ⟨11990051703105690892968395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993367802070460595312263 11990051703105690892968395)
                ·
                  refine ⟨17985077554658536339452593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11990051703105690892968395 17985077554658536339452593)
                  ·
                    refine ⟨13488808165993902254589445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17985077554658536339452593 13488808165993902254589445)
                    ·
                      refine ⟨2529151531123856672735521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13488808165993902254589445 2529151531123856672735521)
                      ·
                        rfl

theorem cell23_4925505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_4925505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925505 prefixEnd_4925505 := by exact prefixLift 4925505
  have htrace : WordTrace (prefixWord ++ tailWord_4925505) baseStart_4925505 baseEnd_4925505 := by
    simpa [prefixWord, tailWord_4925505, baseEnd_4925505] using wordTrace_append hprefix tailTrace_4925505
  have hstable : (prefixWord ++ tailWord_4925505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925505).length < 2 ^ (prefixWord ++ tailWord_4925505).sum := by decide
  have hdescent : baseEnd_4925505 < baseStart_4925505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925569 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_4925569 : Nat := 118140960795 + 4925569 * 2 ^ 59
def prefixEnd_4925569 : Nat := 4983230072969 + 3 ^ 40 * 4925569 * 2
def baseEnd_4925569 : Nat := 2529184393885744422335227

theorem tailTrace_4925569 : CollatzResearch.WordTrace tailWord_4925569 prefixEnd_4925569 2529184393885744422335227 := by
  unfold tailWord_4925569
  simp only [CollatzResearch.WordTrace]
  refine ⟨179650260292512208057347761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119766840195008138704898507 179650260292512208057347761)
  ·
    refine ⟨134737695219384156043010821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179650260292512208057347761 134737695219384156043010821)
    ·
      refine ⟨25263317853634529258064529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134737695219384156043010821 25263317853634529258064529)
      ·
        refine ⟨18947488390225896943548397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25263317853634529258064529 18947488390225896943548397)
        ·
          refine ⟨7105308146334711353830649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18947488390225896943548397 7105308146334711353830649)
          ·
            refine ⟨5328981109751033515372987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7105308146334711353830649 5328981109751033515372987)
            ·
              refine ⟨7993471664626550273059481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328981109751033515372987 7993471664626550273059481)
              ·
                refine ⟨5995103748469912704794611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7993471664626550273059481 5995103748469912704794611)
                ·
                  refine ⟨8992655622704869057191917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995103748469912704794611 8992655622704869057191917)
                  ·
                    refine ⟨3372245858514325896446969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8992655622704869057191917 3372245858514325896446969)
                    ·
                      refine ⟨2529184393885744422335227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3372245858514325896446969 2529184393885744422335227)
                      ·
                        rfl

theorem cell23_4925569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_4925569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925569 prefixEnd_4925569 := by exact prefixLift 4925569
  have htrace : WordTrace (prefixWord ++ tailWord_4925569) baseStart_4925569 baseEnd_4925569 := by
    simpa [prefixWord, tailWord_4925569, baseEnd_4925569] using wordTrace_append hprefix tailTrace_4925569
  have hstable : (prefixWord ++ tailWord_4925569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925569).length < 2 ^ (prefixWord ++ tailWord_4925569).sum := by decide
  have hdescent : baseEnd_4925569 < baseStart_4925569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925582 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4925582 : Nat := 118140960795 + 4925582 * 2 ^ 59
def prefixEnd_4925582 : Nat := 4983230072969 + 3 ^ 40 * 4925582 * 2
def baseEnd_4925582 : Nat := 2529191069134252871472667

theorem tailTrace_4925582 : CollatzResearch.WordTrace tailWord_4925582 prefixEnd_4925582 2529191069134252871472667 := by
  unfold tailWord_4925582
  simp only [CollatzResearch.WordTrace]
  refine ⟨22456341805183138909696375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119767156294310074185047333 22456341805183138909696375)
  ·
    refine ⟨33684512707774708364544563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22456341805183138909696375 33684512707774708364544563)
    ·
      refine ⟨50526769061662062546816845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33684512707774708364544563 50526769061662062546816845)
      ·
        refine ⟨18947538398123273455056317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50526769061662062546816845 18947538398123273455056317)
        ·
          refine ⟨7105326899296227545646119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18947538398123273455056317 7105326899296227545646119)
          ·
            refine ⟨10657990348944341318469179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105326899296227545646119 10657990348944341318469179)
            ·
              refine ⟨15986985523416511977703769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10657990348944341318469179 15986985523416511977703769)
              ·
                refine ⟨11990239142562383983277827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15986985523416511977703769 11990239142562383983277827)
                ·
                  refine ⟨17985358713843575974916741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11990239142562383983277827 17985358713843575974916741)
                  ·
                    refine ⟨3372254758845670495296889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17985358713843575974916741 3372254758845670495296889)
                    ·
                      refine ⟨2529191069134252871472667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3372254758845670495296889 2529191069134252871472667)
                      ·
                        rfl

theorem cell23_4925582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4925582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925582 prefixEnd_4925582 := by exact prefixLift 4925582
  have htrace : WordTrace (prefixWord ++ tailWord_4925582) baseStart_4925582 baseEnd_4925582 := by
    simpa [prefixWord, tailWord_4925582, baseEnd_4925582] using wordTrace_append hprefix tailTrace_4925582
  have hstable : (prefixWord ++ tailWord_4925582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925582).length < 2 ^ (prefixWord ++ tailWord_4925582).sum := by decide
  have hdescent : baseEnd_4925582 < baseStart_4925582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925599 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4925599 : Nat := 118140960795 + 4925599 * 2 ^ 59
def prefixEnd_4925599 : Nat := 4983230072969 + 3 ^ 40 * 4925599 * 2
def baseEnd_4925599 : Nat := 2529199798305379304960089

theorem tailTrace_4925599 : CollatzResearch.WordTrace tailWord_4925599 prefixEnd_4925599 2529199798305379304960089 := by
  unfold tailWord_4925599
  simp only [CollatzResearch.WordTrace]
  refine ⟨179651354482403523180939851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119767569654935682120626567 179651354482403523180939851)
  ·
    refine ⟨269477031723605284771409777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179651354482403523180939851 269477031723605284771409777)
    ·
      refine ⟨202107773792703963578557333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269477031723605284771409777 202107773792703963578557333)
      ·
        refine ⟨9473801896532998292744875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 202107773792703963578557333 9473801896532998292744875)
        ·
          refine ⟨14210702844799497439117313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473801896532998292744875 14210702844799497439117313)
          ·
            refine ⟨10658027133599623079337985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14210702844799497439117313 10658027133599623079337985)
            ·
              refine ⟨7993520350199717309503489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10658027133599623079337985 7993520350199717309503489)
              ·
                refine ⟨5995140262649787982127617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7993520350199717309503489 5995140262649787982127617)
                ·
                  refine ⟨4496355196987340986595713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5995140262649787982127617 4496355196987340986595713)
                  ·
                    refine ⟨3372266397740505739946785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4496355196987340986595713 3372266397740505739946785)
                    ·
                      refine ⟨2529199798305379304960089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3372266397740505739946785 2529199798305379304960089)
                      ·
                        rfl

theorem cell23_4925599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4925599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925599 prefixEnd_4925599 := by exact prefixLift 4925599
  have htrace : WordTrace (prefixWord ++ tailWord_4925599) baseStart_4925599 baseEnd_4925599 := by
    simpa [prefixWord, tailWord_4925599, baseEnd_4925599] using wordTrace_append hprefix tailTrace_4925599
  have hstable : (prefixWord ++ tailWord_4925599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925599).length < 2 ^ (prefixWord ++ tailWord_4925599).sum := by decide
  have hdescent : baseEnd_4925599 < baseStart_4925599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925641 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_4925641 : Nat := 118140960795 + 4925641 * 2 ^ 59
def prefixEnd_4925641 : Nat := 4983230072969 + 3 ^ 40 * 4925641 * 2
def baseEnd_4925641 : Nat := 2529221364492868140634895

theorem tailTrace_4925641 : CollatzResearch.WordTrace tailWord_4925641 prefixEnd_4925641 2529221364492868140634895 := by
  unfold tailWord_4925641
  simp only [CollatzResearch.WordTrace]
  refine ⟨179652886348251364353968777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119768590898834242902645851 179652886348251364353968777)
  ·
    refine ⟨134739664761188523265476583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179652886348251364353968777 134739664761188523265476583)
    ·
      refine ⟨202109497141782784898214875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134739664761188523265476583 202109497141782784898214875)
      ·
        refine ⟨303164245712674177347322313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202109497141782784898214875 303164245712674177347322313)
        ·
          refine ⟨227373184284505633010491735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303164245712674177347322313 227373184284505633010491735)
          ·
            refine ⟨341059776426758449515737603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227373184284505633010491735 341059776426758449515737603)
            ·
              refine ⟨511589664640137674273606405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341059776426758449515737603 511589664640137674273606405)
              ·
                refine ⟨95923062120025813926301201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511589664640137674273606405 95923062120025813926301201)
                ·
                  refine ⟨71942296590019360444725901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95923062120025813926301201 71942296590019360444725901)
                  ·
                    refine ⟨26978361221257260166772213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71942296590019360444725901 26978361221257260166772213)
                    ·
                      refine ⟨2529221364492868140634895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26978361221257260166772213 2529221364492868140634895)
                      ·
                        rfl

theorem cell23_4925641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_4925641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925641 prefixEnd_4925641 := by exact prefixLift 4925641
  have htrace : WordTrace (prefixWord ++ tailWord_4925641) baseStart_4925641 baseEnd_4925641 := by
    simpa [prefixWord, tailWord_4925641, baseEnd_4925641] using wordTrace_append hprefix tailTrace_4925641
  have hstable : (prefixWord ++ tailWord_4925641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925641).length < 2 ^ (prefixWord ++ tailWord_4925641).sum := by decide
  have hdescent : baseEnd_4925641 < baseStart_4925641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925665 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 3, 4]
def baseStart_4925665 : Nat := 118140960795 + 4925665 * 2 ^ 59
def prefixEnd_4925665 : Nat := 4983230072969 + 3 ^ 40 * 4925665 * 2
def baseEnd_4925665 : Nat := 843077896009525348911595

theorem tailTrace_4925665 : CollatzResearch.WordTrace tailWord_4925665 prefixEnd_4925665 843077896009525348911595 := by
  unfold tailWord_4925665
  simp only [CollatzResearch.WordTrace]
  refine ⟨179653761700164416452842449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119769174466776277635228299 179653761700164416452842449)
  ·
    refine ⟨134740321275123312339631837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179653761700164416452842449 134740321275123312339631837)
    ·
      refine ⟨50527620478171242127361939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134740321275123312339631837 50527620478171242127361939)
      ·
        refine ⟨75791430717256863191042909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50527620478171242127361939 75791430717256863191042909)
        ·
          refine ⟨28421786518971323696641091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75791430717256863191042909 28421786518971323696641091)
          ·
            refine ⟨42632679778456985544961637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28421786518971323696641091 42632679778456985544961637)
            ·
              refine ⟨7993627458460684789680307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42632679778456985544961637 7993627458460684789680307)
              ·
                refine ⟨11990441187691027184520461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993627458460684789680307 11990441187691027184520461)
                ·
                  refine ⟨4496415445384135194195173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11990441187691027184520461 4496415445384135194195173)
                  ·
                    refine ⟨843077896009525348911595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4496415445384135194195173 843077896009525348911595)
                    ·
                      rfl

theorem cell23_4925665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_4925665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925665 prefixEnd_4925665 := by exact prefixLift 4925665
  have htrace : WordTrace (prefixWord ++ tailWord_4925665) baseStart_4925665 baseEnd_4925665 := by
    simpa [prefixWord, tailWord_4925665, baseEnd_4925665] using wordTrace_append hprefix tailTrace_4925665
  have hstable : (prefixWord ++ tailWord_4925665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925665).length < 2 ^ (prefixWord ++ tailWord_4925665).sum := by decide
  have hdescent : baseEnd_4925665 < baseStart_4925665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925691 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 9]
def baseStart_4925691 : Nat := 118140960795 + 4925691 * 2 ^ 59
def prefixEnd_4925691 : Nat := 4983230072969 + 3 ^ 40 * 4925691 * 2
def baseEnd_4925691 : Nat := 843082346175197648336555

theorem tailTrace_4925691 : CollatzResearch.WordTrace tailWord_4925691 prefixEnd_4925691 843082346175197648336555 := by
  unfold tailWord_4925691
  simp only [CollatzResearch.WordTrace]
  refine ⟨179654709998070222893288927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119769806665380148595525951 179654709998070222893288927)
  ·
    refine ⟨269482064997105334339933391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179654709998070222893288927 269482064997105334339933391)
    ·
      refine ⟨404223097495658001509900087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269482064997105334339933391 404223097495658001509900087)
      ·
        refine ⟨606334646243487002264850131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404223097495658001509900087 606334646243487002264850131)
        ·
          refine ⟨909501969365230503397275197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606334646243487002264850131 909501969365230503397275197)
          ·
            refine ⟨341063238511961438773978199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 909501969365230503397275197 341063238511961438773978199)
            ·
              refine ⟨511594857767942158160967299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341063238511961438773978199 511594857767942158160967299)
              ·
                refine ⟨767392286651913237241450949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511594857767942158160967299 767392286651913237241450949)
                ·
                  refine ⟨143886053747233731982772053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 767392286651913237241450949 143886053747233731982772053)
                  ·
                    refine ⟨843082346175197648336555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 143886053747233731982772053 843082346175197648336555)
                    ·
                      rfl

theorem cell23_4925691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_4925691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925691 prefixEnd_4925691 := by exact prefixLift 4925691
  have htrace : WordTrace (prefixWord ++ tailWord_4925691) baseStart_4925691 baseEnd_4925691 := by
    simpa [prefixWord, tailWord_4925691, baseEnd_4925691] using wordTrace_append hprefix tailTrace_4925691
  have hstable : (prefixWord ++ tailWord_4925691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925691).length < 2 ^ (prefixWord ++ tailWord_4925691).sum := by decide
  have hdescent : baseEnd_4925691 < baseStart_4925691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925772 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_4925772 : Nat := 118140960795 + 4925772 * 2 ^ 59
def prefixEnd_4925772 : Nat := 4983230072969 + 3 ^ 40 * 4925772 * 2
def baseEnd_4925772 : Nat := 843096210152869042698931

theorem tailTrace_4925772 : CollatzResearch.WordTrace tailWord_4925772 prefixEnd_4925772 843096210152869042698931 := by
  unfold tailWord_4925772
  simp only [CollatzResearch.WordTrace]
  refine ⟨89828832155388386863493785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119771776207184515817991713 89828832155388386863493785)
  ·
    refine ⟨67371624116541290147620339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89828832155388386863493785 67371624116541290147620339)
    ·
      refine ⟨101057436174811935221430509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67371624116541290147620339 101057436174811935221430509)
      ·
        refine ⟨37896538565554475708036441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101057436174811935221430509 37896538565554475708036441)
        ·
          refine ⟨28422403924165856781027331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37896538565554475708036441 28422403924165856781027331)
          ·
            refine ⟨42633605886248785171540997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28422403924165856781027331 42633605886248785171540997)
            ·
              refine ⟨7993801103671647219663937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42633605886248785171540997 7993801103671647219663937)
              ·
                refine ⟨5995350827753735414747953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7993801103671647219663937 5995350827753735414747953)
                ·
                  refine ⟨4496513120815301561060965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5995350827753735414747953 4496513120815301561060965)
                  ·
                    refine ⟨843096210152869042698931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4496513120815301561060965 843096210152869042698931)
                    ·
                      rfl

theorem cell23_4925772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_4925772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925772 prefixEnd_4925772 := by exact prefixLift 4925772
  have htrace : WordTrace (prefixWord ++ tailWord_4925772) baseStart_4925772 baseEnd_4925772 := by
    simpa [prefixWord, tailWord_4925772, baseEnd_4925772] using wordTrace_append hprefix tailTrace_4925772
  have hstable : (prefixWord ++ tailWord_4925772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925772).length < 2 ^ (prefixWord ++ tailWord_4925772).sum := by decide
  have hdescent : baseEnd_4925772 < baseStart_4925772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925790 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4925790 : Nat := 118140960795 + 4925790 * 2 ^ 59
def prefixEnd_4925790 : Nat := 4983230072969 + 3 ^ 40 * 4925790 * 2
def baseEnd_4925790 : Nat := 2529297873110388057671711

theorem tailTrace_4925790 : CollatzResearch.WordTrace tailWord_4925790 prefixEnd_4925790 2529297873110388057671711 := by
  unfold tailWord_4925790
  simp only [CollatzResearch.WordTrace]
  refine ⟨22457290103088945350142853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119772213883141041867428549 22457290103088945350142853)
  ·
    refine ⟨4210741894329177253151785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22457290103088945350142853 4210741894329177253151785)
    ·
      refine ⟨3158056420746882939863839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4210741894329177253151785 3158056420746882939863839)
      ·
        refine ⟨4737084631120324409795759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3158056420746882939863839 4737084631120324409795759)
        ·
          refine ⟨7105626946680486614693639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4737084631120324409795759 7105626946680486614693639)
          ·
            refine ⟨10658440420020729922040459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105626946680486614693639 10658440420020729922040459)
            ·
              refine ⟨15987660630031094883060689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10658440420020729922040459 15987660630031094883060689)
              ·
                refine ⟨11990745472523321162295517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15987660630031094883060689 11990745472523321162295517)
                ·
                  refine ⟨4496529552196245435860819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11990745472523321162295517 4496529552196245435860819)
                  ·
                    refine ⟨6744794328294368153791229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4496529552196245435860819 6744794328294368153791229)
                    ·
                      refine ⟨2529297873110388057671711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6744794328294368153791229 2529297873110388057671711)
                      ·
                        rfl

theorem cell23_4925790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4925790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925790 prefixEnd_4925790 := by exact prefixLift 4925790
  have htrace : WordTrace (prefixWord ++ tailWord_4925790) baseStart_4925790 baseEnd_4925790 := by
    simpa [prefixWord, tailWord_4925790, baseEnd_4925790] using wordTrace_append hprefix tailTrace_4925790
  have hstable : (prefixWord ++ tailWord_4925790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925790).length < 2 ^ (prefixWord ++ tailWord_4925790).sum := by decide
  have hdescent : baseEnd_4925790 < baseStart_4925790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925792 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4]
def baseStart_4925792 : Nat := 118140960795 + 4925792 * 2 ^ 59
def prefixEnd_4925792 : Nat := 4983230072969 + 3 ^ 40 * 4925792 * 2
def baseEnd_4925792 : Nat := 2529298900071697049846701

theorem tailTrace_4925792 : CollatzResearch.WordTrace tailWord_4925792 prefixEnd_4925792 2529298900071697049846701 := by
  unfold tailWord_4925792
  simp only [CollatzResearch.WordTrace]
  refine ⟨89829196885352158571357815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119772262513802878095143753 89829196885352158571357815)
  ·
    refine ⟨134743795328028237857036723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89829196885352158571357815 134743795328028237857036723)
    ·
      refine ⟨202115692992042356785555085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134743795328028237857036723 202115692992042356785555085)
      ·
        refine ⟨75793384872015883794583157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202115692992042356785555085 75793384872015883794583157)
        ·
          refine ⟨7105629831751489105742171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75793384872015883794583157 7105629831751489105742171)
          ·
            refine ⟨10658444747627233658613257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105629831751489105742171 10658444747627233658613257)
            ·
              refine ⟨7993833560720425243959943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10658444747627233658613257 7993833560720425243959943)
              ·
                refine ⟨11990750341080637865939915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993833560720425243959943 11990750341080637865939915)
                ·
                  refine ⟨17986125511620956798909873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11990750341080637865939915 17986125511620956798909873)
                  ·
                    refine ⟨13489594133715717599182405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17986125511620956798909873 13489594133715717599182405)
                    ·
                      refine ⟨2529298900071697049846701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13489594133715717599182405 2529298900071697049846701)
                      ·
                        rfl

theorem cell23_4925792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_4925792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925792 prefixEnd_4925792 := by exact prefixLift 4925792
  have htrace : WordTrace (prefixWord ++ tailWord_4925792) baseStart_4925792 baseEnd_4925792 := by
    simpa [prefixWord, tailWord_4925792, baseEnd_4925792] using wordTrace_append hprefix tailTrace_4925792
  have hstable : (prefixWord ++ tailWord_4925792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925792).length < 2 ^ (prefixWord ++ tailWord_4925792).sum := by decide
  have hdescent : baseEnd_4925792 < baseStart_4925792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925802 : List Nat := [3, 1, 3, 3, 1, 2, 3, 7]
def baseStart_4925802 : Nat := 118140960795 + 4925802 * 2 ^ 59
def prefixEnd_4925802 : Nat := 4983230072969 + 3 ^ 40 * 4925802 * 2
def baseEnd_4925802 : Nat := 93677927217712667063765

theorem tailTrace_4925802 : CollatzResearch.WordTrace tailWord_4925802 prefixEnd_4925802 93677927217712667063765 := by
  unfold tailWord_4925802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44914689625167022212644915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119772505667112059233719773 44914689625167022212644915)
  ·
    refine ⟨67372034437750533318967373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44914689625167022212644915 67372034437750533318967373)
    ·
      refine ⟨25264512914156449994612765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67372034437750533318967373 25264512914156449994612765)
      ·
        refine ⟨9474192342808668747979787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25264512914156449994612765 9474192342808668747979787)
        ·
          refine ⟨14211288514213003121969681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9474192342808668747979787 14211288514213003121969681)
          ·
            refine ⟨10658466385659752341477261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14211288514213003121969681 10658466385659752341477261)
            ·
              refine ⟨3996924894622407128053973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10658466385659752341477261 3996924894622407128053973)
              ·
                refine ⟨93677927217712667063765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3996924894622407128053973 93677927217712667063765)
                ·
                  rfl

theorem cell23_4925802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_4925802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925802 prefixEnd_4925802 := by exact prefixLift 4925802
  have htrace : WordTrace (prefixWord ++ tailWord_4925802) baseStart_4925802 baseEnd_4925802 := by
    simpa [prefixWord, tailWord_4925802, baseEnd_4925802] using wordTrace_append hprefix tailTrace_4925802
  have hstable : (prefixWord ++ tailWord_4925802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925802).length < 2 ^ (prefixWord ++ tailWord_4925802).sum := by decide
  have hdescent : baseEnd_4925802 < baseStart_4925802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925813 : List Nat := [1, 3, 4, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_4925813 : Nat := 118140960795 + 4925813 * 2 ^ 59
def prefixEnd_4925813 : Nat := 4983230072969 + 3 ^ 40 * 4925813 * 2
def baseEnd_4925813 : Nat := 2529309683165441467684105

theorem tailTrace_4925813 : CollatzResearch.WordTrace tailWord_4925813 prefixEnd_4925813 2529309683165441467684105 := by
  unfold tailWord_4925813
  simp only [CollatzResearch.WordTrace]
  refine ⟨179659159703628237729230093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119772773135752158486153395 179659159703628237729230093)
  ·
    refine ⟨67372184888860589148461285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179659159703628237729230093 67372184888860589148461285)
    ·
      refine ⟨12632284666661360465336491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67372184888860589148461285 12632284666661360465336491)
      ·
        refine ⟨18948426999992040698004737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12632284666661360465336491 18948426999992040698004737)
        ·
          refine ⟨14211320249994030523503553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18948426999992040698004737 14211320249994030523503553)
          ·
            refine ⟨10658490187495522892627665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14211320249994030523503553 10658490187495522892627665)
            ·
              refine ⟨7993867640621642169470749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10658490187495522892627665 7993867640621642169470749)
              ·
                refine ⟨2997700365233115813551531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7993867640621642169470749 2997700365233115813551531)
                ·
                  refine ⟨4496550547849673720327297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997700365233115813551531 4496550547849673720327297)
                  ·
                    refine ⟨3372412910887255290245473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4496550547849673720327297 3372412910887255290245473)
                    ·
                      refine ⟨2529309683165441467684105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3372412910887255290245473 2529309683165441467684105)
                      ·
                        rfl

theorem cell23_4925813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_4925813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925813 prefixEnd_4925813 := by exact prefixLift 4925813
  have htrace : WordTrace (prefixWord ++ tailWord_4925813) baseStart_4925813 baseEnd_4925813 := by
    simpa [prefixWord, tailWord_4925813, baseEnd_4925813] using wordTrace_append hprefix tailTrace_4925813
  have hstable : (prefixWord ++ tailWord_4925813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925813).length < 2 ^ (prefixWord ++ tailWord_4925813).sum := by decide
  have hdescent : baseEnd_4925813 < baseStart_4925813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925855 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4925855 : Nat := 118140960795 + 4925855 * 2 ^ 59
def prefixEnd_4925855 : Nat := 4983230072969 + 3 ^ 40 * 4925855 * 2
def baseEnd_4925855 : Nat := 2529331249352930303358911

theorem tailTrace_4925855 : CollatzResearch.WordTrace tailWord_4925855 prefixEnd_4925855 2529331249352930303358911 := by
  unfold tailWord_4925855
  simp only [CollatzResearch.WordTrace]
  refine ⟨179660691569476078902259019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119773794379650719268172679 179660691569476078902259019)
  ·
    refine ⟨269491037354214118353388529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179660691569476078902259019 269491037354214118353388529)
    ·
      refine ⟨202118278015660588765041397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269491037354214118353388529 202118278015660588765041397)
      ·
        refine ⟨18948588563968180196722631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202118278015660588765041397 18948588563968180196722631)
        ·
          refine ⟨28422882845952270295083947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18948588563968180196722631 28422882845952270295083947)
          ·
            refine ⟨42634324268928405442625921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28422882845952270295083947 42634324268928405442625921)
            ·
              refine ⟨31975743201696304081969441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42634324268928405442625921 31975743201696304081969441)
              ·
                refine ⟨23981807401272228061477081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31975743201696304081969441 23981807401272228061477081)
                ·
                  refine ⟨17986355550954171046107811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23981807401272228061477081 17986355550954171046107811)
                  ·
                    refine ⟨26979533326431256569161717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17986355550954171046107811 26979533326431256569161717)
                    ·
                      refine ⟨2529331249352930303358911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26979533326431256569161717 2529331249352930303358911)
                      ·
                        rfl

theorem cell23_4925855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4925855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925855 prefixEnd_4925855 := by exact prefixLift 4925855
  have htrace : WordTrace (prefixWord ++ tailWord_4925855) baseStart_4925855 baseEnd_4925855 := by
    simpa [prefixWord, tailWord_4925855, baseEnd_4925855] using wordTrace_append hprefix tailTrace_4925855
  have hstable : (prefixWord ++ tailWord_4925855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925855).length < 2 ^ (prefixWord ++ tailWord_4925855).sum := by decide
  have hdescent : baseEnd_4925855 < baseStart_4925855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925962 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_4925962 : Nat := 118140960795 + 4925962 * 2 ^ 59
def prefixEnd_4925962 : Nat := 4983230072969 + 3 ^ 40 * 4925962 * 2
def baseEnd_4925962 : Nat := 2529386191782961384720919

theorem tailTrace_4925962 : CollatzResearch.WordTrace tailWord_4925962 prefixEnd_4925962 2529386191782961384720919 := by
  unfold tailWord_4925962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44916148545022109044101035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119776396120058957450936093 44916148545022109044101035)
  ·
    refine ⟨67374222817533163566151553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44916148545022109044101035 67374222817533163566151553)
    ·
      refine ⟨50530667113149872674613665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67374222817533163566151553 50530667113149872674613665)
      ·
        refine ⟨37898000334862404505960249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50530667113149872674613665 37898000334862404505960249)
        ·
          refine ⟨28423500251146803379470187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37898000334862404505960249 28423500251146803379470187)
          ·
            refine ⟨42635250376720205069205281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28423500251146803379470187 42635250376720205069205281)
            ·
              refine ⟨31976437782540153801903961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42635250376720205069205281 31976437782540153801903961)
              ·
                refine ⟨23982328336905115351427971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31976437782540153801903961 23982328336905115351427971)
                ·
                  refine ⟨35973492505357673027141957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23982328336905115351427971 35973492505357673027141957)
                  ·
                    refine ⟨6745029844754563692589117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35973492505357673027141957 6745029844754563692589117)
                    ·
                      refine ⟨2529386191782961384720919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6745029844754563692589117 2529386191782961384720919)
                      ·
                        rfl

theorem cell23_4925962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_4925962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925962 prefixEnd_4925962 := by exact prefixLift 4925962
  have htrace : WordTrace (prefixWord ++ tailWord_4925962) baseStart_4925962 baseEnd_4925962 := by
    simpa [prefixWord, tailWord_4925962, baseEnd_4925962] using wordTrace_append hprefix tailTrace_4925962
  have hstable : (prefixWord ++ tailWord_4925962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925962).length < 2 ^ (prefixWord ++ tailWord_4925962).sum := by decide
  have hdescent : baseEnd_4925962 < baseStart_4925962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926035 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5]
def baseStart_4926035 : Nat := 118140960795 + 4926035 * 2 ^ 59
def prefixEnd_4926035 : Nat := 4983230072969 + 3 ^ 40 * 4926035 * 2
def baseEnd_4926035 : Nat := 2529423675870739599108083

theorem tailTrace_4926035 : CollatzResearch.WordTrace tailWord_4926035 prefixEnd_4926035 2529423675870739599108083 := by
  unfold tailWord_4926035
  simp only [CollatzResearch.WordTrace]
  refine ⟨179667256708823969643811559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119778171139215979762541039 179667256708823969643811559)
  ·
    refine ⟨269500885063235954465717339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179667256708823969643811559 269500885063235954465717339)
    ·
      refine ⟨404251327594853931698576009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269500885063235954465717339 404251327594853931698576009)
      ·
        refine ⟨303188495696140448773932007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404251327594853931698576009 303188495696140448773932007)
        ·
          refine ⟨454782743544210673160898011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303188495696140448773932007 454782743544210673160898011)
          ·
            refine ⟨682174115316316009741347017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454782743544210673160898011 682174115316316009741347017)
            ·
              refine ⟨511630586487237007306010263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682174115316316009741347017 511630586487237007306010263)
              ·
                refine ⟨767445879730855510959015395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511630586487237007306010263 767445879730855510959015395)
                ·
                  refine ⟨1151168819596283266438523093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767445879730855510959015395 1151168819596283266438523093)
                  ·
                    refine ⟨26980519209287889057152885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1151168819596283266438523093 26980519209287889057152885)
                    ·
                      refine ⟨2529423675870739599108083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26980519209287889057152885 2529423675870739599108083)
                      ·
                        rfl

theorem cell23_4926035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_4926035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926035 prefixEnd_4926035 := by exact prefixLift 4926035
  have htrace : WordTrace (prefixWord ++ tailWord_4926035) baseStart_4926035 baseEnd_4926035 := by
    simpa [prefixWord, tailWord_4926035, baseEnd_4926035] using wordTrace_append hprefix tailTrace_4926035
  have hstable : (prefixWord ++ tailWord_4926035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926035).length < 2 ^ (prefixWord ++ tailWord_4926035).sum := by decide
  have hdescent : baseEnd_4926035 < baseStart_4926035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926049 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_4926049 : Nat := 118140960795 + 4926049 * 2 ^ 59
def prefixEnd_4926049 : Nat := 4983230072969 + 3 ^ 40 * 4926049 * 2
def baseEnd_4926049 : Nat := 2529430864599902544333019

theorem tailTrace_4926049 : CollatzResearch.WordTrace tailWord_4926049 prefixEnd_4926049 2529430864599902544333019 := by
  unfold tailWord_4926049
  simp only [CollatzResearch.WordTrace]
  refine ⟨179667767330773250034821201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119778511553848833356547467 179667767330773250034821201)
  ·
    refine ⟨134750825498079937526115901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179667767330773250034821201 134750825498079937526115901)
    ·
      refine ⟨50531559561779976572293463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134750825498079937526115901 50531559561779976572293463)
      ·
        refine ⟨75797339342669964858440195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50531559561779976572293463 75797339342669964858440195)
        ·
          refine ⟨113696009014004947287660293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75797339342669964858440195 113696009014004947287660293)
          ·
            refine ⟨21318001690125927616436305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113696009014004947287660293 21318001690125927616436305)
            ·
              refine ⟨15988501267594445712327229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21318001690125927616436305 15988501267594445712327229)
              ·
                refine ⟨5995687975347917142122711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15988501267594445712327229 5995687975347917142122711)
                ·
                  refine ⟨8993531963021875713184067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995687975347917142122711 8993531963021875713184067)
                  ·
                    refine ⟨13490297944532813569776101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8993531963021875713184067 13490297944532813569776101)
                    ·
                      refine ⟨2529430864599902544333019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13490297944532813569776101 2529430864599902544333019)
                      ·
                        rfl

theorem cell23_4926049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_4926049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926049 prefixEnd_4926049 := by exact prefixLift 4926049
  have htrace : WordTrace (prefixWord ++ tailWord_4926049) baseStart_4926049 baseEnd_4926049 := by
    simpa [prefixWord, tailWord_4926049, baseEnd_4926049] using wordTrace_append hprefix tailTrace_4926049
  have hstable : (prefixWord ++ tailWord_4926049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926049).length < 2 ^ (prefixWord ++ tailWord_4926049).sum := by decide
  have hdescent : baseEnd_4926049 < baseStart_4926049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926076 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_4926076 : Nat := 118140960795 + 4926076 * 2 ^ 59
def prefixEnd_4926076 : Nat := 4983230072969 + 3 ^ 40 * 4926076 * 2
def baseEnd_4926076 : Nat := 843148242859191312898465

theorem tailTrace_4926076 : CollatzResearch.WordTrace tailWord_4926076 prefixEnd_4926076 843148242859191312898465 := by
  unfold tailWord_4926076
  simp only [CollatzResearch.WordTrace]
  refine ⟨89834376050837716823027041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119779168067783622430702721 89834376050837716823027041)
  ·
    refine ⟨67375782038128287617270281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89834376050837716823027041 67375782038128287617270281)
    ·
      refine ⟨50531836528596215712952711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67375782038128287617270281 50531836528596215712952711)
      ·
        refine ⟨75797754792894323569429067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50531836528596215712952711 75797754792894323569429067)
        ·
          refine ⟨113696632189341485354143601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75797754792894323569429067 113696632189341485354143601)
          ·
            refine ⟨85272474142006114015607701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113696632189341485354143601 85272474142006114015607701)
            ·
              refine ⟨3997147225406536594481611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85272474142006114015607701 3997147225406536594481611)
              ·
                refine ⟨5995720838109804891722417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3997147225406536594481611 5995720838109804891722417)
                ·
                  refine ⟨4496790628582353668791813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5995720838109804891722417 4496790628582353668791813)
                  ·
                    refine ⟨843148242859191312898465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4496790628582353668791813 843148242859191312898465)
                    ·
                      rfl

theorem cell23_4926076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_4926076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926076 prefixEnd_4926076 := by exact prefixLift 4926076
  have htrace : WordTrace (prefixWord ++ tailWord_4926076) baseStart_4926076 baseEnd_4926076 := by
    simpa [prefixWord, tailWord_4926076, baseEnd_4926076] using wordTrace_append hprefix tailTrace_4926076
  have hstable : (prefixWord ++ tailWord_4926076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926076).length < 2 ^ (prefixWord ++ tailWord_4926076).sum := by decide
  have hdescent : baseEnd_4926076 < baseStart_4926076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926133 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4926133 : Nat := 118140960795 + 4926133 * 2 ^ 59
def prefixEnd_4926133 : Nat := 4983230072969 + 3 ^ 40 * 4926133 * 2
def baseEnd_4926133 : Nat := 2529473996974880215682633

theorem tailTrace_4926133 : CollatzResearch.WordTrace tailWord_4926133 prefixEnd_4926133 2529473996974880215682633 := by
  unfold tailWord_4926133
  simp only [CollatzResearch.WordTrace]
  refine ⟨179670831062468932380879053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119780554041645954920586035 179670831062468932380879053)
  ·
    refine ⟨67376561648425849642829645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179670831062468932380879053 67376561648425849642829645)
    ·
      refine ⟨25266210618159693616061117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67376561648425849642829645 25266210618159693616061117)
      ·
        refine ⟨9474828981809885106022919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25266210618159693616061117 9474828981809885106022919)
        ·
          refine ⟨14212243472714827659034379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9474828981809885106022919 14212243472714827659034379)
          ·
            refine ⟨21318365209072241488551569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14212243472714827659034379 21318365209072241488551569)
            ·
              refine ⟨15988773906804181116413677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21318365209072241488551569 15988773906804181116413677)
              ·
                refine ⟨5995790215051567918655129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15988773906804181116413677 5995790215051567918655129)
                ·
                  refine ⟨4496842661288675938991347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5995790215051567918655129 4496842661288675938991347)
                  ·
                    refine ⟨6745263991933013908487021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4496842661288675938991347 6745263991933013908487021)
                    ·
                      refine ⟨2529473996974880215682633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6745263991933013908487021 2529473996974880215682633)
                      ·
                        rfl

theorem cell23_4926133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4926133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926133 prefixEnd_4926133 := by exact prefixLift 4926133
  have htrace : WordTrace (prefixWord ++ tailWord_4926133) baseStart_4926133 baseEnd_4926133 := by
    simpa [prefixWord, tailWord_4926133, baseEnd_4926133] using wordTrace_append hprefix tailTrace_4926133
  have hstable : (prefixWord ++ tailWord_4926133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926133).length < 2 ^ (prefixWord ++ tailWord_4926133).sum := by decide
  have hdescent : baseEnd_4926133 < baseStart_4926133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926179 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 7]
def baseStart_4926179 : Nat := 118140960795 + 4926179 * 2 ^ 59
def prefixEnd_4926179 : Nat := 4983230072969 + 3 ^ 40 * 4926179 * 2
def baseEnd_4926179 : Nat := 281055290787220781745269

theorem tailTrace_4926179 : CollatzResearch.WordTrace tailWord_4926179 prefixEnd_4926179 281055290787220781745269 := by
  unfold tailWord_4926179
  simp only [CollatzResearch.WordTrace]
  refine ⟨179672508820302282237053591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119781672546868188158035727 179672508820302282237053591)
  ·
    refine ⟨269508763230453423355580387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179672508820302282237053591 269508763230453423355580387)
    ·
      refine ⟨404263144845680135033370581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269508763230453423355580387 404263144845680135033370581)
      ·
        refine ⟨9474917457320628164844623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 404263144845680135033370581 9474917457320628164844623)
        ·
          refine ⟨14212376185980942247266935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9474917457320628164844623 14212376185980942247266935)
          ·
            refine ⟨21318564278971413370900403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14212376185980942247266935 21318564278971413370900403)
            ·
              refine ⟨31977846418457120056350605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21318564278971413370900403 31977846418457120056350605)
              ·
                refine ⟨11991692406921420021131477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31977846418457120056350605 11991692406921420021131477)
                ·
                  refine ⟨281055290787220781745269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11991692406921420021131477 281055290787220781745269)
                  ·
                    rfl

theorem cell23_4926179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 7].length) (baseStart_4926179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926179 prefixEnd_4926179 := by exact prefixLift 4926179
  have htrace : WordTrace (prefixWord ++ tailWord_4926179) baseStart_4926179 baseEnd_4926179 := by
    simpa [prefixWord, tailWord_4926179, baseEnd_4926179] using wordTrace_append hprefix tailTrace_4926179
  have hstable : (prefixWord ++ tailWord_4926179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926179).length < 2 ^ (prefixWord ++ tailWord_4926179).sum := by decide
  have hdescent : baseEnd_4926179 < baseStart_4926179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926192 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 3, 7]
def baseStart_4926192 : Nat := 118140960795 + 4926192 * 2 ^ 59
def prefixEnd_4926192 : Nat := 4983230072969 + 3 ^ 40 * 4926192 * 2
def baseEnd_4926192 : Nat := 843168097444498494948287

theorem tailTrace_4926192 : CollatzResearch.WordTrace tailWord_4926192 prefixEnd_4926192 843168097444498494948287 := by
  unfold tailWord_4926192
  simp only [CollatzResearch.WordTrace]
  refine ⟨89836491484627592728638415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119781988646170123638184553 89836491484627592728638415)
  ·
    refine ⟨134754737226941389092957623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89836491484627592728638415 134754737226941389092957623)
    ·
      refine ⟨202132105840412083639436435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134754737226941389092957623 202132105840412083639436435)
      ·
        refine ⟨303198158760618125459154653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202132105840412083639436435 303198158760618125459154653)
        ·
          refine ⟨113699309535231797047182995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303198158760618125459154653 113699309535231797047182995)
          ·
            refine ⟨170548964302847695570774493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113699309535231797047182995 170548964302847695570774493)
            ·
              refine ⟨63955861613567885839040435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170548964302847695570774493 63955861613567885839040435)
              ·
                refine ⟨95933792420351828758560653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63955861613567885839040435 95933792420351828758560653)
                ·
                  refine ⟨35975172157631935784460245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95933792420351828758560653 35975172157631935784460245)
                  ·
                    refine ⟨843168097444498494948287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35975172157631935784460245 843168097444498494948287)
                    ·
                      rfl

theorem cell23_4926192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_4926192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926192 prefixEnd_4926192 := by exact prefixLift 4926192
  have htrace : WordTrace (prefixWord ++ tailWord_4926192) baseStart_4926192 baseEnd_4926192 := by
    simpa [prefixWord, tailWord_4926192, baseEnd_4926192] using wordTrace_append hprefix tailTrace_4926192
  have hstable : (prefixWord ++ tailWord_4926192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926192).length < 2 ^ (prefixWord ++ tailWord_4926192).sum := by decide
  have hdescent : baseEnd_4926192 < baseStart_4926192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926209 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4926209 : Nat := 118140960795 + 4926209 * 2 ^ 59
def prefixEnd_4926209 : Nat := 4983230072969 + 3 ^ 40 * 4926209 * 2
def baseEnd_4926209 : Nat := 843171007168207306110761

theorem tailTrace_4926209 : CollatzResearch.WordTrace tailWord_4926209 prefixEnd_4926209 843171007168207306110761 := by
  unfold tailWord_4926209
  simp only [CollatzResearch.WordTrace]
  refine ⟨179673603010193597360645681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119782402006795731573763787 179673603010193597360645681)
  ·
    refine ⟨134755202257645198020484261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179673603010193597360645681 134755202257645198020484261)
    ·
      refine ⟨25266600423308474628840799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134755202257645198020484261 25266600423308474628840799)
      ·
        refine ⟨37899900634962711943261199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25266600423308474628840799 37899900634962711943261199)
        ·
          refine ⟨56849850952444067914891799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37899900634962711943261199 56849850952444067914891799)
          ·
            refine ⟨85274776428666101872337699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56849850952444067914891799 85274776428666101872337699)
            ·
              refine ⟨127912164642999152808506549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85274776428666101872337699 127912164642999152808506549)
              ·
                refine ⟨11991765435281170575797489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127912164642999152808506549 11991765435281170575797489)
                ·
                  refine ⟨8993824076460877931848117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11991765435281170575797489 8993824076460877931848117)
                  ·
                    refine ⟨843171007168207306110761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8993824076460877931848117 843171007168207306110761)
                    ·
                      rfl

theorem cell23_4926209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4926209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926209 prefixEnd_4926209 := by exact prefixLift 4926209
  have htrace : WordTrace (prefixWord ++ tailWord_4926209) baseStart_4926209 baseEnd_4926209 := by
    simpa [prefixWord, tailWord_4926209, baseEnd_4926209] using wordTrace_append hprefix tailTrace_4926209
  have hstable : (prefixWord ++ tailWord_4926209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926209).length < 2 ^ (prefixWord ++ tailWord_4926209).sum := by decide
  have hdescent : baseEnd_4926209 < baseStart_4926209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926296 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_4926296 : Nat := 118140960795 + 4926296 * 2 ^ 59
def prefixEnd_4926296 : Nat := 4983230072969 + 3 ^ 40 * 4926296 * 2
def baseEnd_4926296 : Nat := 2529557694321563077944383

theorem tailTrace_4926296 : CollatzResearch.WordTrace tailWord_4926296 prefixEnd_4926296 2529557694321563077944383 := by
  unfold tailWord_4926296
  simp only [CollatzResearch.WordTrace]
  refine ⟨89838388080439205609531371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119784517440585607479375161 89838388080439205609531371)
  ·
    refine ⟨134757582120658808414297057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89838388080439205609531371 134757582120658808414297057)
    ·
      refine ⟨101068186590494106310722793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134757582120658808414297057 101068186590494106310722793)
      ·
        refine ⟨75801139942870579733042095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101068186590494106310722793 75801139942870579733042095)
        ·
          refine ⟨113701709914305869599563143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75801139942870579733042095 113701709914305869599563143)
          ·
            refine ⟨170552564871458804399344715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113701709914305869599563143 170552564871458804399344715)
            ·
              refine ⟨255828847307188206599017073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170552564871458804399344715 255828847307188206599017073)
              ·
                refine ⟨191871635480391154949262805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255828847307188206599017073 191871635480391154949262805)
                ·
                  refine ⟨4496991456571667694123347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 191871635480391154949262805 4496991456571667694123347)
                  ·
                    refine ⟨6745487184857501541185021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4496991456571667694123347 6745487184857501541185021)
                    ·
                      refine ⟨2529557694321563077944383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6745487184857501541185021 2529557694321563077944383)
                      ·
                        rfl

theorem cell23_4926296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_4926296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926296 prefixEnd_4926296 := by exact prefixLift 4926296
  have htrace : WordTrace (prefixWord ++ tailWord_4926296) baseStart_4926296 baseEnd_4926296 := by
    simpa [prefixWord, tailWord_4926296, baseEnd_4926296] using wordTrace_append hprefix tailTrace_4926296
  have hstable : (prefixWord ++ tailWord_4926296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926296).length < 2 ^ (prefixWord ++ tailWord_4926296).sum := by decide
  have hdescent : baseEnd_4926296 < baseStart_4926296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926316 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_4926316 : Nat := 118140960795 + 4926316 * 2 ^ 59
def prefixEnd_4926316 : Nat := 4983230072969 + 3 ^ 40 * 4926316 * 2
def baseEnd_4926316 : Nat := 843189321311550999898097

theorem tailTrace_4926316 : CollatzResearch.WordTrace tailWord_4926316 prefixEnd_4926316 843189321311550999898097 := by
  unfold tailWord_4926316
  simp only [CollatzResearch.WordTrace]
  refine ⟨89838752810402977317395401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119785003747203969756527201 89838752810402977317395401)
  ·
    refine ⟨67379064607802232988046551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89838752810402977317395401 67379064607802232988046551)
    ·
      refine ⟨101068596911703349482069827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67379064607802232988046551 101068596911703349482069827)
      ·
        refine ⟨151602895367555024223104741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101068596911703349482069827 151602895367555024223104741)
        ·
          refine ⟨28425542881416567041832139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151602895367555024223104741 28425542881416567041832139)
          ·
            refine ⟨42638314322124850562748209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28425542881416567041832139 42638314322124850562748209)
            ·
              refine ⟨31978735741593637922061157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42638314322124850562748209 31978735741593637922061157)
              ·
                refine ⟨5996012951548807110386467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31978735741593637922061157 5996012951548807110386467)
                ·
                  refine ⟨8994019427323210665579701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996012951548807110386467 8994019427323210665579701)
                  ·
                    refine ⟨843189321311550999898097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8994019427323210665579701 843189321311550999898097)
                    ·
                      rfl

theorem cell23_4926316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_4926316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926316 prefixEnd_4926316 := by exact prefixLift 4926316
  have htrace : WordTrace (prefixWord ++ tailWord_4926316) baseStart_4926316 baseEnd_4926316 := by
    simpa [prefixWord, tailWord_4926316, baseEnd_4926316] using wordTrace_append hprefix tailTrace_4926316
  have hstable : (prefixWord ++ tailWord_4926316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926316).length < 2 ^ (prefixWord ++ tailWord_4926316).sum := by decide
  have hdescent : baseEnd_4926316 < baseStart_4926316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926323 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 2, 3, 2]
def baseStart_4926323 : Nat := 118140960795 + 4926323 * 2 ^ 59
def prefixEnd_4926323 : Nat := 4983230072969 + 3 ^ 40 * 4926323 * 2
def baseEnd_4926323 : Nat := 2529571558299234472306759

theorem tailTrace_4926323 : CollatzResearch.WordTrace tailWord_4926323 prefixEnd_4926323 2529571558299234472306759 := by
  unfold tailWord_4926323
  simp only [CollatzResearch.WordTrace]
  refine ⟨179677760931780594830295623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119785173954520396553530415 179677760931780594830295623)
  ·
    refine ⟨269516641397670892245443435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179677760931780594830295623 269516641397670892245443435)
    ·
      refine ⟨404274962096506338368165153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269516641397670892245443435 404274962096506338368165153)
      ·
        refine ⟨303206221572379753776123865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404274962096506338368165153 303206221572379753776123865)
        ·
          refine ⟨227404666179284815332092899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303206221572379753776123865 227404666179284815332092899)
          ·
            refine ⟨341106999268927222998139349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227404666179284815332092899 341106999268927222998139349)
            ·
              refine ⟨7994695295365481789018891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 341106999268927222998139349 7994695295365481789018891)
              ·
                refine ⟨11992042943048222683528337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7994695295365481789018891 11992042943048222683528337)
                ·
                  refine ⟨8994032207286167012646253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11992042943048222683528337 8994032207286167012646253)
                  ·
                    refine ⟨3372762077732312629742345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8994032207286167012646253 3372762077732312629742345)
                    ·
                      refine ⟨2529571558299234472306759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3372762077732312629742345 2529571558299234472306759)
                      ·
                        rfl

theorem cell23_4926323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3, 2].length) (baseStart_4926323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926323 prefixEnd_4926323 := by exact prefixLift 4926323
  have htrace : WordTrace (prefixWord ++ tailWord_4926323) baseStart_4926323 baseEnd_4926323 := by
    simpa [prefixWord, tailWord_4926323, baseEnd_4926323] using wordTrace_append hprefix tailTrace_4926323
  have hstable : (prefixWord ++ tailWord_4926323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926323).length < 2 ^ (prefixWord ++ tailWord_4926323).sum := by decide
  have hdescent : baseEnd_4926323 < baseStart_4926323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926333 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_4926333 : Nat := 118140960795 + 4926333 * 2 ^ 59
def prefixEnd_4926333 : Nat := 4983230072969 + 3 ^ 40 * 4926333 * 2
def baseEnd_4926333 : Nat := 843192231035259811060571

theorem tailTrace_4926333 : CollatzResearch.WordTrace tailWord_4926333 prefixEnd_4926333 843192231035259811060571 := by
  unfold tailWord_4926333
  simp only [CollatzResearch.WordTrace]
  refine ⟨179678125661744366538159653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119785417107829577692106435 179678125661744366538159653)
  ·
    refine ⟨33689648561577068725904935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179678125661744366538159653 33689648561577068725904935)
    ·
      refine ⟨50534472842365603088857403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33689648561577068725904935 50534472842365603088857403)
      ·
        refine ⟨75801709263548404633286105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50534472842365603088857403 75801709263548404633286105)
        ·
          refine ⟨56851281947661303474964579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75801709263548404633286105 56851281947661303474964579)
          ·
            refine ⟨85276922921491955212446869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56851281947661303474964579 85276922921491955212446869)
            ·
              refine ⟨3997355761944935400583447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85276922921491955212446869 3997355761944935400583447)
              ·
                refine ⟨5996033642917403100875171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3997355761944935400583447 5996033642917403100875171)
                ·
                  refine ⟨8994050464376104651312757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996033642917403100875171 8994050464376104651312757)
                  ·
                    refine ⟨843192231035259811060571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8994050464376104651312757 843192231035259811060571)
                    ·
                      rfl

theorem cell23_4926333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_4926333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926333 prefixEnd_4926333 := by exact prefixLift 4926333
  have htrace : WordTrace (prefixWord ++ tailWord_4926333) baseStart_4926333 baseEnd_4926333 := by
    simpa [prefixWord, tailWord_4926333, baseEnd_4926333] using wordTrace_append hprefix tailTrace_4926333
  have hstable : (prefixWord ++ tailWord_4926333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926333).length < 2 ^ (prefixWord ++ tailWord_4926333).sum := by decide
  have hdescent : baseEnd_4926333 < baseStart_4926333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926359 : List Nat := [1, 1, 3, 3, 1, 2, 2, 10]
def baseStart_4926359 : Nat := 118140960795 + 4926359 * 2 ^ 59
def prefixEnd_4926359 : Nat := 4983230072969 + 3 ^ 40 * 4926359 * 2
def baseEnd_4926359 : Nat := 93688520133436901165059

theorem tailTrace_4926359 : CollatzResearch.WordTrace tailWord_4926359 prefixEnd_4926359 93688520133436901165059 := by
  unfold tailWord_4926359
  simp only [CollatzResearch.WordTrace]
  refine ⟨179679073959650172978606131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119786049306433448652404087 179679073959650172978606131)
  ·
    refine ⟨269518610939475259467909197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179679073959650172978606131 269518610939475259467909197)
    ·
      refine ⟨101069479102303222300465949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269518610939475259467909197 101069479102303222300465949)
      ·
        refine ⟨37901054663363708362674731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101069479102303222300465949 37901054663363708362674731)
        ·
          refine ⟨56851581995045562544012097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37901054663363708362674731 56851581995045562544012097)
          ·
            refine ⟨42638686496284171908009073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56851581995045562544012097 42638686496284171908009073)
            ·
              refine ⟨31979014872213128931006805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42638686496284171908009073 31979014872213128931006805)
              ·
                refine ⟨93688520133436901165059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31979014872213128931006805 93688520133436901165059)
                ·
                  rfl

theorem cell23_4926359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 10].length) (baseStart_4926359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926359 prefixEnd_4926359 := by exact prefixLift 4926359
  have htrace : WordTrace (prefixWord ++ tailWord_4926359) baseStart_4926359 baseEnd_4926359 := by
    simpa [prefixWord, tailWord_4926359, baseEnd_4926359] using wordTrace_append hprefix tailTrace_4926359
  have hstable : (prefixWord ++ tailWord_4926359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926359).length < 2 ^ (prefixWord ++ tailWord_4926359).sum := by decide
  have hdescent : baseEnd_4926359 < baseStart_4926359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926370 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4926370 : Nat := 118140960795 + 4926370 * 2 ^ 59
def prefixEnd_4926370 : Nat := 4983230072969 + 3 ^ 40 * 4926370 * 2
def baseEnd_4926370 : Nat := 2529595691889995788419043

theorem tailTrace_4926370 : CollatzResearch.WordTrace tailWord_4926370 prefixEnd_4926370 2529595691889995788419043 := by
  unfold tailWord_4926370
  simp only [CollatzResearch.WordTrace]
  refine ⟨44919868790652580464314141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119786316775073547904837709 44919868790652580464314141)
  ·
    refine ⟨16844950796494717674117803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44919868790652580464314141 16844950796494717674117803)
    ·
      refine ⟨25267426194742076511176705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16844950796494717674117803 25267426194742076511176705)
      ·
        refine ⟨18950569646056557383382529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25267426194742076511176705 18950569646056557383382529)
        ·
          refine ⟨14212927234542418037536897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18950569646056557383382529 14212927234542418037536897)
          ·
            refine ⟨10659695425906813528152673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14212927234542418037536897 10659695425906813528152673)
            ·
              refine ⟨7994771569430110146114505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10659695425906813528152673 7994771569430110146114505)
              ·
                refine ⟨5996078677072582609585879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7994771569430110146114505 5996078677072582609585879)
                ·
                  refine ⟨8994118015608873914378819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996078677072582609585879 8994118015608873914378819)
                  ·
                    refine ⟨13491177023413310871568229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8994118015608873914378819 13491177023413310871568229)
                    ·
                      refine ⟨2529595691889995788419043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13491177023413310871568229 2529595691889995788419043)
                      ·
                        rfl

theorem cell23_4926370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4926370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926370 prefixEnd_4926370 := by exact prefixLift 4926370
  have htrace : WordTrace (prefixWord ++ tailWord_4926370) baseStart_4926370 baseEnd_4926370 := by
    simpa [prefixWord, tailWord_4926370, baseEnd_4926370] using wordTrace_append hprefix tailTrace_4926370
  have hstable : (prefixWord ++ tailWord_4926370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926370).length < 2 ^ (prefixWord ++ tailWord_4926370).sum := by decide
  have hdescent : baseEnd_4926370 < baseStart_4926370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926381 : List Nat := [1, 5, 2, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4926381 : Nat := 118140960795 + 4926381 * 2 ^ 59
def prefixEnd_4926381 : Nat := 4983230072969 + 3 ^ 40 * 4926381 * 2
def baseEnd_4926381 : Nat := 2529601340177195245381493

theorem tailTrace_4926381 : CollatzResearch.WordTrace tailWord_4926381 prefixEnd_4926381 2529601340177195245381493 := by
  unfold tailWord_4926381
  simp only [CollatzResearch.WordTrace]
  refine ⟨179679876365570470735906997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119786584243713647157271331 179679876365570470735906997)
  ·
    refine ⟨16844988409272231631491281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179679876365570470735906997 16844988409272231631491281)
    ·
      refine ⟨12633741306954173723618461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16844988409272231631491281 12633741306954173723618461)
      ·
        refine ⟨4737652990107815146356923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12633741306954173723618461 4737652990107815146356923)
        ·
          refine ⟨7106479485161722719535385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4737652990107815146356923 7106479485161722719535385)
          ·
            refine ⟨5329859613871292039651539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7106479485161722719535385 5329859613871292039651539)
            ·
              refine ⟨7994789420806938059477309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329859613871292039651539 7994789420806938059477309)
              ·
                refine ⟨2998046032802601772303991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7994789420806938059477309 2998046032802601772303991)
                ·
                  refine ⟨4497069049203902658455987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998046032802601772303991 4497069049203902658455987)
                  ·
                    refine ⟨6745603573805853987683981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4497069049203902658455987 6745603573805853987683981)
                    ·
                      refine ⟨2529601340177195245381493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6745603573805853987683981 2529601340177195245381493)
                      ·
                        rfl

theorem cell23_4926381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4926381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926381 prefixEnd_4926381 := by exact prefixLift 4926381
  have htrace : WordTrace (prefixWord ++ tailWord_4926381) baseStart_4926381 baseEnd_4926381 := by
    simpa [prefixWord, tailWord_4926381, baseEnd_4926381] using wordTrace_append hprefix tailTrace_4926381
  have hstable : (prefixWord ++ tailWord_4926381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926381).length < 2 ^ (prefixWord ++ tailWord_4926381).sum := by decide
  have hdescent : baseEnd_4926381 < baseStart_4926381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926447 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 1, 3, 2]
def baseStart_4926447 : Nat := 118140960795 + 4926447 * 2 ^ 59
def prefixEnd_4926447 : Nat := 4983230072969 + 3 ^ 40 * 4926447 * 2
def baseEnd_4926447 : Nat := 2529635229900391987156189

theorem tailTrace_4926447 : CollatzResearch.WordTrace tailWord_4926447 prefixEnd_4926447 2529635229900391987156189 := by
  unfold tailWord_4926447
  simp only [CollatzResearch.WordTrace]
  refine ⟨179682283583331364007809595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119788189055554242671873063 179682283583331364007809595)
  ·
    refine ⟨269523425374997046011714393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179682283583331364007809595 269523425374997046011714393)
    ·
      refine ⟨202142569031247784508785795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269523425374997046011714393 202142569031247784508785795)
      ·
        refine ⟨303213853546871676763178693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202142569031247784508785795 303213853546871676763178693)
        ·
          refine ⟨56852597540038439393096005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303213853546871676763178693 56852597540038439393096005)
          ·
            refine ⟨10659862038757207386205501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56852597540038439393096005 10659862038757207386205501)
            ·
              refine ⟨3997448264533952769827063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10659862038757207386205501 3997448264533952769827063)
              ·
                refine ⟨5996172396800929154740595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3997448264533952769827063 5996172396800929154740595)
                ·
                  refine ⟨8994258595201393732110893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996172396800929154740595 8994258595201393732110893)
                  ·
                    refine ⟨3372846973200522649541585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8994258595201393732110893 3372846973200522649541585)
                    ·
                      refine ⟨2529635229900391987156189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3372846973200522649541585 2529635229900391987156189)
                      ·
                        rfl

theorem cell23_4926447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 3, 2].length) (baseStart_4926447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926447 prefixEnd_4926447 := by exact prefixLift 4926447
  have htrace : WordTrace (prefixWord ++ tailWord_4926447) baseStart_4926447 baseEnd_4926447 := by
    simpa [prefixWord, tailWord_4926447, baseEnd_4926447] using wordTrace_append hprefix tailTrace_4926447
  have hstable : (prefixWord ++ tailWord_4926447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926447).length < 2 ^ (prefixWord ++ tailWord_4926447).sum := by decide
  have hdescent : baseEnd_4926447 < baseStart_4926447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926456 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_4926456 : Nat := 118140960795 + 4926456 * 2 ^ 59
def prefixEnd_4926456 : Nat := 4983230072969 + 3 ^ 40 * 4926456 * 2
def baseEnd_4926456 : Nat := 2529639851226282451943647

theorem tailTrace_4926456 : CollatzResearch.WordTrace tailWord_4926456 prefixEnd_4926456 2529639851226282451943647 := by
  unfold tailWord_4926456
  simp only [CollatzResearch.WordTrace]
  refine ⟨89841305920149379272443611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119788407893532505696591481 89841305920149379272443611)
  ·
    refine ⟨134761958880224068908665417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89841305920149379272443611 134761958880224068908665417)
    ·
      refine ⟨101071469160168051681499063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134761958880224068908665417 101071469160168051681499063)
      ·
        refine ⟨151607203740252077522248595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101071469160168051681499063 151607203740252077522248595)
        ·
          refine ⟨227410805610378116283372893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151607203740252077522248595 227410805610378116283372893)
          ·
            refine ⟨85279052103891793606264835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227410805610378116283372893 85279052103891793606264835)
            ·
              refine ⟨127918578155837690409397253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85279052103891793606264835 127918578155837690409397253)
              ·
                refine ⟨23984733404219566951761985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127918578155837690409397253 23984733404219566951761985)
                ·
                  refine ⟨17988550053164675213821489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23984733404219566951761985 17988550053164675213821489)
                  ·
                    refine ⟨13491412539873506410366117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17988550053164675213821489 13491412539873506410366117)
                    ·
                      refine ⟨2529639851226282451943647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13491412539873506410366117 2529639851226282451943647)
                      ·
                        rfl

theorem cell23_4926456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_4926456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926456 prefixEnd_4926456 := by exact prefixLift 4926456
  have htrace : WordTrace (prefixWord ++ tailWord_4926456) baseStart_4926456 baseEnd_4926456 := by
    simpa [prefixWord, tailWord_4926456, baseEnd_4926456] using wordTrace_append hprefix tailTrace_4926456
  have hstable : (prefixWord ++ tailWord_4926456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926456).length < 2 ^ (prefixWord ++ tailWord_4926456).sum := by decide
  have hdescent : baseEnd_4926456 < baseStart_4926456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926500 : List Nat := [2, 3, 1, 4, 1, 1, 1, 5, 5]
def baseStart_4926500 : Nat := 118140960795 + 4926500 * 2 ^ 59
def prefixEnd_4926500 : Nat := 4983230072969 + 3 ^ 40 * 4926500 * 2
def baseEnd_4926500 : Nat := 281073604930564475532605

theorem tailTrace_4926500 : CollatzResearch.WordTrace tailWord_4926500 prefixEnd_4926500 281073604930564475532605 := by
  unfold tailWord_4926500
  simp only [CollatzResearch.WordTrace]
  refine ⟨89842108326069677029744477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119789477768092902706325969 89842108326069677029744477)
  ·
    refine ⟨33690790622276128886154179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89842108326069677029744477 33690790622276128886154179)
    ·
      refine ⟨50536185933414193329231269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33690790622276128886154179 50536185933414193329231269)
      ·
        refine ⟨9475534862515161249230863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50536185933414193329231269 9475534862515161249230863)
        ·
          refine ⟨14213302293772741873846295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9475534862515161249230863 14213302293772741873846295)
          ·
            refine ⟨21319953440659112810769443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14213302293772741873846295 21319953440659112810769443)
            ·
              refine ⟨31979930160988669216154165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21319953440659112810769443 31979930160988669216154165)
              ·
                refine ⟨2998118452592687739014453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31979930160988669216154165 2998118452592687739014453)
                ·
                  refine ⟨281073604930564475532605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998118452592687739014453 281073604930564475532605)
                  ·
                    rfl

theorem cell23_4926500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_4926500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926500 prefixEnd_4926500 := by exact prefixLift 4926500
  have htrace : WordTrace (prefixWord ++ tailWord_4926500) baseStart_4926500 baseEnd_4926500 := by
    simpa [prefixWord, tailWord_4926500, baseEnd_4926500] using wordTrace_append hprefix tailTrace_4926500
  have hstable : (prefixWord ++ tailWord_4926500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926500).length < 2 ^ (prefixWord ++ tailWord_4926500).sum := by decide
  have hdescent : baseEnd_4926500 < baseStart_4926500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926570 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_4926570 : Nat := 118140960795 + 4926570 * 2 ^ 59
def prefixEnd_4926570 : Nat := 4983230072969 + 3 ^ 40 * 4926570 * 2
def baseEnd_4926570 : Nat := 2529698388020895005918123

theorem tailTrace_4926570 : CollatzResearch.WordTrace tailWord_4926570 prefixEnd_4926570 2529698388020895005918123 := by
  unfold tailWord_4926570
  simp only [CollatzResearch.WordTrace]
  refine ⟨44921692440471439003634291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119791179841257170676358109 44921692440471439003634291)
  ·
    refine ⟨67382538660707158505451437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44921692440471439003634291 67382538660707158505451437)
    ·
      refine ⟨25268451997765184439544289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67382538660707158505451437 25268451997765184439544289)
      ·
        refine ⟨18951338998323888329658217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25268451997765184439544289 18951338998323888329658217)
        ·
          refine ⟨14213504248742916247243663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18951338998323888329658217 14213504248742916247243663)
          ·
            refine ⟨21320256373114374370865495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14213504248742916247243663 21320256373114374370865495)
            ·
              refine ⟨31980384559671561556298243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21320256373114374370865495 31980384559671561556298243)
              ·
                refine ⟨47970576839507342334447365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31980384559671561556298243 47970576839507342334447365)
                ·
                  refine ⟨8994483157407626687708881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47970576839507342334447365 8994483157407626687708881)
                  ·
                    refine ⟨6745862368055720015781661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8994483157407626687708881 6745862368055720015781661)
                    ·
                      refine ⟨2529698388020895005918123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6745862368055720015781661 2529698388020895005918123)
                      ·
                        rfl

theorem cell23_4926570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_4926570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926570 prefixEnd_4926570 := by exact prefixLift 4926570
  have htrace : WordTrace (prefixWord ++ tailWord_4926570) baseStart_4926570 baseEnd_4926570 := by
    simpa [prefixWord, tailWord_4926570, baseEnd_4926570] using wordTrace_append hprefix tailTrace_4926570
  have hstable : (prefixWord ++ tailWord_4926570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926570).length < 2 ^ (prefixWord ++ tailWord_4926570).sum := by decide
  have hdescent : baseEnd_4926570 < baseStart_4926570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926573 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 8]
def baseStart_4926573 : Nat := 118140960795 + 4926573 * 2 ^ 59
def prefixEnd_4926573 : Nat := 4983230072969 + 3 ^ 40 * 4926573 * 2
def baseEnd_4926573 : Nat := 281077769829206499353401

theorem tailTrace_4926573 : CollatzResearch.WordTrace tailWord_4926573 prefixEnd_4926573 281077769829206499353401 := by
  unfold tailWord_4926573
  simp only [CollatzResearch.WordTrace]
  refine ⟨179686879180874887526896373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119791252787249925017930915 179686879180874887526896373)
  ·
    refine ⟨16845644923207020705646535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179686879180874887526896373 16845644923207020705646535)
    ·
      refine ⟨25268467384810531058469803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16845644923207020705646535 25268467384810531058469803)
      ·
        refine ⟨37902701077215796587704705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25268467384810531058469803 37902701077215796587704705)
        ·
          refine ⟨28427025807911847440778529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37902701077215796587704705 28427025807911847440778529)
          ·
            refine ⟨21320269355933885580583897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28427025807911847440778529 21320269355933885580583897)
            ·
              refine ⟨15990202016950414185437923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21320269355933885580583897 15990202016950414185437923)
              ·
                refine ⟨23985303025425621278156885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15990202016950414185437923 23985303025425621278156885)
                ·
                  refine ⟨281077769829206499353401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23985303025425621278156885 281077769829206499353401)
                  ·
                    rfl

theorem cell23_4926573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_4926573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926573 prefixEnd_4926573 := by exact prefixLift 4926573
  have htrace : WordTrace (prefixWord ++ tailWord_4926573) baseStart_4926573 baseEnd_4926573 := by
    simpa [prefixWord, tailWord_4926573, baseEnd_4926573] using wordTrace_append hprefix tailTrace_4926573
  have hstable : (prefixWord ++ tailWord_4926573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926573).length < 2 ^ (prefixWord ++ tailWord_4926573).sum := by decide
  have hdescent : baseEnd_4926573 < baseStart_4926573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926643 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5]
def baseStart_4926643 : Nat := 118140960795 + 4926643 * 2 ^ 59
def prefixEnd_4926643 : Nat := 4983230072969 + 3 ^ 40 * 4926643 * 2
def baseEnd_4926643 : Nat := 2529735872108673220305287

theorem tailTrace_4926643 : CollatzResearch.WordTrace tailWord_4926643 prefixEnd_4926643 2529735872108673220305287 := by
  unfold tailWord_4926643
  simp only [CollatzResearch.WordTrace]
  refine ⟨179689432290621289481944583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119792954860414192987963055 179689432290621289481944583)
  ·
    refine ⟨269534148435931934222916875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179689432290621289481944583 269534148435931934222916875)
    ·
      refine ⟨404301222653897901334375313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269534148435931934222916875 404301222653897901334375313)
      ·
        refine ⟨303225916990423426000781485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404301222653897901334375313 303225916990423426000781485)
        ·
          refine ⟨113709718871408784750293057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303225916990423426000781485 113709718871408784750293057)
          ·
            refine ⟨85282289153556588562719793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113709718871408784750293057 85282289153556588562719793)
            ·
              refine ⟨63961716865167441422039845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85282289153556588562719793 63961716865167441422039845)
              ·
                refine ⟨11992821912218895266632471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63961716865167441422039845 11992821912218895266632471)
                ·
                  refine ⟨17989232868328342899948707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11992821912218895266632471 17989232868328342899948707)
                  ·
                    refine ⟨26983849302492514349923061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17989232868328342899948707 26983849302492514349923061)
                    ·
                      refine ⟨2529735872108673220305287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26983849302492514349923061 2529735872108673220305287)
                      ·
                        rfl

theorem cell23_4926643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_4926643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926643 prefixEnd_4926643 := by exact prefixLift 4926643
  have htrace : WordTrace (prefixWord ++ tailWord_4926643) baseStart_4926643 baseEnd_4926643 := by
    simpa [prefixWord, tailWord_4926643, baseEnd_4926643] using wordTrace_append hprefix tailTrace_4926643
  have hstable : (prefixWord ++ tailWord_4926643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926643).length < 2 ^ (prefixWord ++ tailWord_4926643).sum := by decide
  have hdescent : baseEnd_4926643 < baseStart_4926643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926653 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4926653 : Nat := 118140960795 + 4926653 * 2 ^ 59
def prefixEnd_4926653 : Nat := 4983230072969 + 3 ^ 40 * 4926653 * 2
def baseEnd_4926653 : Nat := 2529741006915218181180241

theorem tailTrace_4926653 : CollatzResearch.WordTrace tailWord_4926653 prefixEnd_4926653 2529741006915218181180241 := by
  unfold tailWord_4926653
  simp only [CollatzResearch.WordTrace]
  refine ⟨179689797020585061189808613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119793198013723374126539075 179689797020585061189808613)
  ·
    refine ⟨33691836941359698973089115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179689797020585061189808613 33691836941359698973089115)
    ·
      refine ⟨50537755412039548459633673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33691836941359698973089115 50537755412039548459633673)
      ·
        refine ⟨37903316559029661344725255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50537755412039548459633673 37903316559029661344725255)
        ·
          refine ⟨56854974838544492017087883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37903316559029661344725255 56854974838544492017087883)
          ·
            refine ⟨85282462257816738025631825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56854974838544492017087883 85282462257816738025631825)
            ·
              refine ⟨63961846693362553519223869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85282462257816738025631825 63961846693362553519223869)
              ·
                refine ⟨23985692510010957569708951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63961846693362553519223869 23985692510010957569708951)
                ·
                  refine ⟨35978538765016436354563427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23985692510010957569708951 35978538765016436354563427)
                  ·
                    refine ⟨53967808147524654531845141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35978538765016436354563427 53967808147524654531845141)
                    ·
                      refine ⟨2529741006915218181180241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53967808147524654531845141 2529741006915218181180241)
                      ·
                        rfl

theorem cell23_4926653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4926653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926653 prefixEnd_4926653 := by exact prefixLift 4926653
  have htrace : WordTrace (prefixWord ++ tailWord_4926653) baseStart_4926653 baseEnd_4926653 := by
    simpa [prefixWord, tailWord_4926653, baseEnd_4926653] using wordTrace_append hprefix tailTrace_4926653
  have hstable : (prefixWord ++ tailWord_4926653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926653).length < 2 ^ (prefixWord ++ tailWord_4926653).sum := by decide
  have hdescent : baseEnd_4926653 < baseStart_4926653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926657 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4926657 : Nat := 118140960795 + 4926657 * 2 ^ 59
def prefixEnd_4926657 : Nat := 4983230072969 + 3 ^ 40 * 4926657 * 2
def baseEnd_4926657 : Nat := 2529743060837836165530223

theorem tailTrace_4926657 : CollatzResearch.WordTrace tailWord_4926657 prefixEnd_4926657 2529743060837836165530223 := by
  unfold tailWord_4926657
  simp only [CollatzResearch.WordTrace]
  refine ⟨179689942912570569872954225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119793295275047046581969483 179689942912570569872954225)
  ·
    refine ⟨134767457184427927404715669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179689942912570569872954225 134767457184427927404715669)
    ·
      refine ⟨6317224555520059097096047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134767457184427927404715669 6317224555520059097096047)
      ·
        refine ⟨9475836833280088645644071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6317224555520059097096047 9475836833280088645644071)
        ·
          refine ⟨14213755249920132968466107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9475836833280088645644071 14213755249920132968466107)
          ·
            refine ⟨21320632874880199452699161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14213755249920132968466107 21320632874880199452699161)
            ·
              refine ⟨15990474656160149589524371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21320632874880199452699161 15990474656160149589524371)
              ·
                refine ⟨23985711984240224384286557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15990474656160149589524371 23985711984240224384286557)
                ·
                  refine ⟨8994641994090084144107459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23985711984240224384286557 8994641994090084144107459)
                  ·
                    refine ⟨13491962991135126216161189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8994641994090084144107459 13491962991135126216161189)
                    ·
                      refine ⟨2529743060837836165530223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13491962991135126216161189 2529743060837836165530223)
                      ·
                        rfl

theorem cell23_4926657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4926657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926657 prefixEnd_4926657 := by exact prefixLift 4926657
  have htrace : WordTrace (prefixWord ++ tailWord_4926657) baseStart_4926657 baseEnd_4926657 := by
    simpa [prefixWord, tailWord_4926657, baseEnd_4926657] using wordTrace_append hprefix tailTrace_4926657
  have hstable : (prefixWord ++ tailWord_4926657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926657).length < 2 ^ (prefixWord ++ tailWord_4926657).sum := by decide
  have hdescent : baseEnd_4926657 < baseStart_4926657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926707 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 3]
def baseStart_4926707 : Nat := 118140960795 + 4926707 * 2 ^ 59
def prefixEnd_4926707 : Nat := 4983230072969 + 3 ^ 40 * 4926707 * 2
def baseEnd_4926707 : Nat := 2529768734870560969904993

theorem tailTrace_4926707 : CollatzResearch.WordTrace tailWord_4926707 prefixEnd_4926707 2529768734870560969904993 := by
  unfold tailWord_4926707
  simp only [CollatzResearch.WordTrace]
  refine ⟨179691766562389428412274375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119794511041592952274849583 179691766562389428412274375)
  ·
    refine ⟨269537649843584142618411563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179691766562389428412274375 269537649843584142618411563)
    ·
      refine ⟨404306474765376213927617345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269537649843584142618411563 404306474765376213927617345)
      ·
        refine ⟨303229856074032160445713009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404306474765376213927617345 303229856074032160445713009)
        ·
          refine ⟨227422392055524120334284757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303229856074032160445713009 227422392055524120334284757)
          ·
            refine ⟨5330212313801346570334799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 227422392055524120334284757 5330212313801346570334799)
            ·
              refine ⟨7995318470702019855502199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330212313801346570334799 7995318470702019855502199)
              ·
                refine ⟨11992977706053029783253299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7995318470702019855502199 11992977706053029783253299)
                ·
                  refine ⟨17989466559079544674879949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11992977706053029783253299 17989466559079544674879949)
                  ·
                    refine ⟨6746049959654829253079981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17989466559079544674879949 6746049959654829253079981)
                    ·
                      refine ⟨2529768734870560969904993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6746049959654829253079981 2529768734870560969904993)
                      ·
                        rfl

theorem cell23_4926707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_4926707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926707 prefixEnd_4926707 := by exact prefixLift 4926707
  have htrace : WordTrace (prefixWord ++ tailWord_4926707) baseStart_4926707 baseEnd_4926707 := by
    simpa [prefixWord, tailWord_4926707, baseEnd_4926707] using wordTrace_append hprefix tailTrace_4926707
  have hstable : (prefixWord ++ tailWord_4926707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926707).length < 2 ^ (prefixWord ++ tailWord_4926707).sum := by decide
  have hdescent : baseEnd_4926707 < baseStart_4926707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926708 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4926708 : Nat := 118140960795 + 4926708 * 2 ^ 59
def prefixEnd_4926708 : Nat := 4983230072969 + 3 ^ 40 * 4926708 * 2
def baseEnd_4926708 : Nat := 2529769248351215465992489

theorem tailTrace_4926708 : CollatzResearch.WordTrace tailWord_4926708 prefixEnd_4926708 2529769248351215465992489 := by
  unfold tailWord_4926708
  simp only [CollatzResearch.WordTrace]
  refine ⟨89845901517692902791530389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119794535356923870388707185 89845901517692902791530389)
  ·
    refine ⟨4211526633641854818352987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89845901517692902791530389 4211526633641854818352987)
    ·
      refine ⟨6317289950462782227529481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4211526633641854818352987 6317289950462782227529481)
      ·
        refine ⟨4737967462847086670647111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6317289950462782227529481 4737967462847086670647111)
        ·
          refine ⟨7106951194270630005970667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4737967462847086670647111 7106951194270630005970667)
          ·
            refine ⟨10660426791405945008956001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7106951194270630005970667 10660426791405945008956001)
            ·
              refine ⟨7995320093554458756717001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10660426791405945008956001 7995320093554458756717001)
              ·
                refine ⟨5996490070165844067537751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7995320093554458756717001 5996490070165844067537751)
                ·
                  refine ⟨8994735105248766101306627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996490070165844067537751 8994735105248766101306627)
                  ·
                    refine ⟨13492102657873149151959941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8994735105248766101306627 13492102657873149151959941)
                    ·
                      refine ⟨2529769248351215465992489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13492102657873149151959941 2529769248351215465992489)
                      ·
                        rfl

theorem cell23_4926708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4926708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926708 prefixEnd_4926708 := by exact prefixLift 4926708
  have htrace : WordTrace (prefixWord ++ tailWord_4926708) baseStart_4926708 baseEnd_4926708 := by
    simpa [prefixWord, tailWord_4926708, baseEnd_4926708] using wordTrace_append hprefix tailTrace_4926708
  have hstable : (prefixWord ++ tailWord_4926708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926708).length < 2 ^ (prefixWord ++ tailWord_4926708).sum := by decide
  have hdescent : baseEnd_4926708 < baseStart_4926708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926734 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_4926734 : Nat := 118140960795 + 4926734 * 2 ^ 59
def prefixEnd_4926734 : Nat := 4983230072969 + 3 ^ 40 * 4926734 * 2
def baseEnd_4926734 : Nat := 2529782598848232364267369

theorem tailTrace_4926734 : CollatzResearch.WordTrace tailWord_4926734 prefixEnd_4926734 2529782598848232364267369 := by
  unfold tailWord_4926734
  simp only [CollatzResearch.WordTrace]
  refine ⟨22461593916661451502938407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119795167555527741349004837 22461593916661451502938407)
  ·
    refine ⟨33692390874992177254407611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22461593916661451502938407 33692390874992177254407611)
    ·
      refine ⟨50538586312488265881611417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33692390874992177254407611 50538586312488265881611417)
      ·
        refine ⟨37903939734366199411208563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50538586312488265881611417 37903939734366199411208563)
        ·
          refine ⟨56855909601549299116812845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37903939734366199411208563 56855909601549299116812845)
          ·
            refine ⟨21320966100580987168804817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56855909601549299116812845 21320966100580987168804817)
            ·
              refine ⟨15990724575435740376603613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21320966100580987168804817 15990724575435740376603613)
              ·
                refine ⟨5996521715788402641226355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15990724575435740376603613 5996521715788402641226355)
                ·
                  refine ⟨8994782573682603961839533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996521715788402641226355 8994782573682603961839533)
                  ·
                    refine ⟨3373043465130976485689825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8994782573682603961839533 3373043465130976485689825)
                    ·
                      refine ⟨2529782598848232364267369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373043465130976485689825 2529782598848232364267369)
                      ·
                        rfl

theorem cell23_4926734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_4926734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926734 prefixEnd_4926734 := by exact prefixLift 4926734
  have htrace : WordTrace (prefixWord ++ tailWord_4926734) baseStart_4926734 baseEnd_4926734 := by
    simpa [prefixWord, tailWord_4926734, baseEnd_4926734] using wordTrace_append hprefix tailTrace_4926734
  have hstable : (prefixWord ++ tailWord_4926734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926734).length < 2 ^ (prefixWord ++ tailWord_4926734).sum := by decide
  have hdescent : baseEnd_4926734 < baseStart_4926734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926781 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4926781 : Nat := 118140960795 + 4926781 * 2 ^ 59
def prefixEnd_4926781 : Nat := 4983230072969 + 3 ^ 40 * 4926781 * 2
def baseEnd_4926781 : Nat := 2529806732438993680379653

theorem tailTrace_4926781 : CollatzResearch.WordTrace tailWord_4926781 prefixEnd_4926781 2529806732438993680379653 := by
  unfold tailWord_4926781
  simp only [CollatzResearch.WordTrace]
  refine ⟨179694465564121339050468197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119796310376080892700312131 179694465564121339050468197)
  ·
    refine ⟨33692712293272751071962787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179694465564121339050468197 33692712293272751071962787)
    ·
      refine ⟨50539068439909126607944181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33692712293272751071962787 50539068439909126607944181)
      ·
        refine ⟨4738037666241480619494767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50539068439909126607944181 4738037666241480619494767)
        ·
          refine ⟨7107056499362220929242151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4738037666241480619494767 7107056499362220929242151)
          ·
            refine ⟨10660584749043331393863227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7107056499362220929242151 10660584749043331393863227)
            ·
              refine ⟨15990877123564997090794841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10660584749043331393863227 15990877123564997090794841)
              ·
                refine ⟨11993157842673747818096131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15990877123564997090794841 11993157842673747818096131)
                ·
                  refine ⟨17989736764010621727144197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11993157842673747818096131 17989736764010621727144197)
                  ·
                    refine ⟨3373075643251991573839537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17989736764010621727144197 3373075643251991573839537)
                    ·
                      refine ⟨2529806732438993680379653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373075643251991573839537 2529806732438993680379653)
                      ·
                        rfl

theorem cell23_4926781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4926781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926781 prefixEnd_4926781 := by exact prefixLift 4926781
  have htrace : WordTrace (prefixWord ++ tailWord_4926781) baseStart_4926781 baseEnd_4926781 := by
    simpa [prefixWord, tailWord_4926781, baseEnd_4926781] using wordTrace_append hprefix tailTrace_4926781
  have hstable : (prefixWord ++ tailWord_4926781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926781).length < 2 ^ (prefixWord ++ tailWord_4926781).sum := by decide
  have hdescent : baseEnd_4926781 < baseStart_4926781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926800 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 2, 5]
def baseStart_4926800 : Nat := 118140960795 + 4926800 * 2 ^ 59
def prefixEnd_4926800 : Nat := 4983230072969 + 3 ^ 40 * 4926800 * 2
def baseEnd_4926800 : Nat := 843272162857143035347355

theorem tailTrace_4926800 : CollatzResearch.WordTrace tailWord_4926800 prefixEnd_4926800 843272162857143035347355 := by
  unfold tailWord_4926800
  simp only [CollatzResearch.WordTrace]
  refine ⟨89847579275526252647704927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119796772367368336863606569 89847579275526252647704927)
  ·
    refine ⟨134771368913289378971557391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89847579275526252647704927 134771368913289378971557391)
    ·
      refine ⟨202157053369934068457336087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134771368913289378971557391 202157053369934068457336087)
      ·
        refine ⟨303235580054901102686004131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202157053369934068457336087 303235580054901102686004131)
        ·
          refine ⟨454853370082351654029006197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303235580054901102686004131 454853370082351654029006197)
          ·
            refine ⟨42642503445220467565219331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 454853370082351654029006197 42642503445220467565219331)
            ·
              refine ⟨63963755167830701347828997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42642503445220467565219331 63963755167830701347828997)
              ·
                refine ⟨11993204093968256502717937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63963755167830701347828997 11993204093968256502717937)
                ·
                  refine ⟨8994903070476192377038453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11993204093968256502717937 8994903070476192377038453)
                  ·
                    refine ⟨843272162857143035347355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8994903070476192377038453 843272162857143035347355)
                    ·
                      rfl

theorem cell23_4926800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_4926800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926800 prefixEnd_4926800 := by exact prefixLift 4926800
  have htrace : WordTrace (prefixWord ++ tailWord_4926800) baseStart_4926800 baseEnd_4926800 := by
    simpa [prefixWord, tailWord_4926800, baseEnd_4926800] using wordTrace_append hprefix tailTrace_4926800
  have hstable : (prefixWord ++ tailWord_4926800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926800).length < 2 ^ (prefixWord ++ tailWord_4926800).sum := by decide
  have hdescent : baseEnd_4926800 < baseStart_4926800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926807 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 2, 5, 2]
def baseStart_4926807 : Nat := 118140960795 + 4926807 * 2 ^ 59
def prefixEnd_4926807 : Nat := 4983230072969 + 3 ^ 40 * 4926807 * 2
def baseEnd_4926807 : Nat := 2529820082936010578654533

theorem tailTrace_4926807 : CollatzResearch.WordTrace tailWord_4926807 prefixEnd_4926807 2529820082936010578654533 := by
  unfold tailWord_4926807
  simp only [CollatzResearch.WordTrace]
  refine ⟨179695413862027145490914675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119796942574684763660609783 179695413862027145490914675)
  ·
    refine ⟨269543120793040718236372013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179695413862027145490914675 269543120793040718236372013)
    ·
      refine ⟨101078670297390269338639505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269543120793040718236372013 101078670297390269338639505)
      ·
        refine ⟨75809002723042702003979629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101078670297390269338639505 75809002723042702003979629)
        ·
          refine ⟨28428376021141013251492361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75809002723042702003979629 28428376021141013251492361)
          ·
            refine ⟨21321282015855759938619271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28428376021141013251492361 21321282015855759938619271)
            ·
              refine ⟨31981923023783639907928907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21321282015855759938619271 31981923023783639907928907)
              ·
                refine ⟨47972884535675459861893361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31981923023783639907928907 47972884535675459861893361)
                ·
                  refine ⟨35979663401756594896420021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47972884535675459861893361 35979663401756594896420021)
                  ·
                    refine ⟨3373093443914680771539377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35979663401756594896420021 3373093443914680771539377)
                    ·
                      refine ⟨2529820082936010578654533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373093443914680771539377 2529820082936010578654533)
                      ·
                        rfl

theorem cell23_4926807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_4926807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926807 prefixEnd_4926807 := by exact prefixLift 4926807
  have htrace : WordTrace (prefixWord ++ tailWord_4926807) baseStart_4926807 baseEnd_4926807 := by
    simpa [prefixWord, tailWord_4926807, baseEnd_4926807] using wordTrace_append hprefix tailTrace_4926807
  have hstable : (prefixWord ++ tailWord_4926807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926807).length < 2 ^ (prefixWord ++ tailWord_4926807).sum := by decide
  have hdescent : baseEnd_4926807 < baseStart_4926807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926810 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_4926810 : Nat := 118140960795 + 4926810 * 2 ^ 59
def prefixEnd_4926810 : Nat := 4983230072969 + 3 ^ 40 * 4926810 * 2
def baseEnd_4926810 : Nat := 2529821623377974066917019

theorem tailTrace_4926810 : CollatzResearch.WordTrace tailWord_4926810 prefixEnd_4926810 2529821623377974066917019 := by
  unfold tailWord_4926810
  simp only [CollatzResearch.WordTrace]
  refine ⟨44923880820254069250818471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119797015520677518002182589 44923880820254069250818471)
  ·
    refine ⟨67385821230381103876227707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44923880820254069250818471 67385821230381103876227707)
    ·
      refine ⟨101078731845571655814341561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67385821230381103876227707 101078731845571655814341561)
      ·
        refine ⟨75809048884178741860756171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101078731845571655814341561 75809048884178741860756171)
        ·
          refine ⟨113713573326268112791134257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75809048884178741860756171 113713573326268112791134257)
          ·
            refine ⟨85285179994701084593350693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113713573326268112791134257 85285179994701084593350693)
            ·
              refine ⟨15990971249006453361253255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85285179994701084593350693 15990971249006453361253255)
              ·
                refine ⟨23986456873509680041879883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15990971249006453361253255 23986456873509680041879883)
                ·
                  refine ⟨35979685310264520062819825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23986456873509680041879883 35979685310264520062819825)
                  ·
                    refine ⟨26984763982698390047114869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35979685310264520062819825 26984763982698390047114869)
                    ·
                      refine ⟨2529821623377974066917019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26984763982698390047114869 2529821623377974066917019)
                      ·
                        rfl

theorem cell23_4926810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_4926810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926810 prefixEnd_4926810 := by exact prefixLift 4926810
  have htrace : WordTrace (prefixWord ++ tailWord_4926810) baseStart_4926810 baseEnd_4926810 := by
    simpa [prefixWord, tailWord_4926810, baseEnd_4926810] using wordTrace_append hprefix tailTrace_4926810
  have hstable : (prefixWord ++ tailWord_4926810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926810).length < 2 ^ (prefixWord ++ tailWord_4926810).sum := by decide
  have hdescent : baseEnd_4926810 < baseStart_4926810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926860 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 8]
def baseStart_4926860 : Nat := 118140960795 + 4926860 * 2 ^ 59
def prefixEnd_4926860 : Nat := 4983230072969 + 3 ^ 40 * 4926860 * 2
def baseEnd_4926860 : Nat := 281094144156744319032421

theorem tailTrace_4926860 : CollatzResearch.WordTrace tailWord_4926860 prefixEnd_4926860 281094144156744319032421 := by
  unfold tailWord_4926860
  simp only [CollatzResearch.WordTrace]
  refine ⟨89848673465417567771297017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119798231287223423695062689 89848673465417567771297017)
  ·
    refine ⟨67386505099063175828472763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89848673465417567771297017 67386505099063175828472763)
    ·
      refine ⟨101079757648594763742709145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67386505099063175828472763 101079757648594763742709145)
      ·
        refine ⟨75809818236446072807031859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101079757648594763742709145 75809818236446072807031859)
        ·
          refine ⟨113714727354669109210547789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75809818236446072807031859 113714727354669109210547789)
          ·
            refine ⟨42643022758000915953955421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113714727354669109210547789 42643022758000915953955421)
            ·
              refine ⟨15991133534250343482733283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42643022758000915953955421 15991133534250343482733283)
              ·
                refine ⟨23986700301375515224099925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15991133534250343482733283 23986700301375515224099925)
                ·
                  refine ⟨281094144156744319032421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23986700301375515224099925 281094144156744319032421)
                  ·
                    rfl

theorem cell23_4926860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_4926860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926860 prefixEnd_4926860 := by exact prefixLift 4926860
  have htrace : WordTrace (prefixWord ++ tailWord_4926860) baseStart_4926860 baseEnd_4926860 := by
    simpa [prefixWord, tailWord_4926860, baseEnd_4926860] using wordTrace_append hprefix tailTrace_4926860
  have hstable : (prefixWord ++ tailWord_4926860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926860).length < 2 ^ (prefixWord ++ tailWord_4926860).sum := by decide
  have hdescent : baseEnd_4926860 < baseStart_4926860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926880 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4926880 : Nat := 118140960795 + 4926880 * 2 ^ 59
def prefixEnd_4926880 : Nat := 4983230072969 + 3 ^ 40 * 4926880 * 2
def baseEnd_4926880 : Nat := 2529857567023788793041697

theorem tailTrace_4926880 : CollatzResearch.WordTrace tailWord_4926880 prefixEnd_4926880 2529857567023788793041697 := by
  unfold tailWord_4926880
  simp only [CollatzResearch.WordTrace]
  refine ⟨89849038195381339479161047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119798717593841785972214729 89849038195381339479161047)
  ·
    refine ⟨134773557293072009218741571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89849038195381339479161047 134773557293072009218741571)
    ·
      refine ⟨202160335939608013828112357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134773557293072009218741571 202160335939608013828112357)
      ·
        refine ⟨37905062988676502592771067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202160335939608013828112357 37905062988676502592771067)
        ·
          refine ⟨56857594483014753889156601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37905062988676502592771067 56857594483014753889156601)
          ·
            refine ⟨42643195862261065416867451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56857594483014753889156601 42643195862261065416867451)
            ·
              refine ⟨63964793793391598125301177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42643195862261065416867451 63964793793391598125301177)
              ·
                refine ⟨47973595345043698593975883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63964793793391598125301177 47973595345043698593975883)
                ·
                  refine ⟨71960393017565547890963825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47973595345043698593975883 71960393017565547890963825)
                  ·
                    refine ⟨53970294763174160918222869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71960393017565547890963825 53970294763174160918222869)
                    ·
                      refine ⟨2529857567023788793041697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53970294763174160918222869 2529857567023788793041697)
                      ·
                        rfl

theorem cell23_4926880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4926880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926880 prefixEnd_4926880 := by exact prefixLift 4926880
  have htrace : WordTrace (prefixWord ++ tailWord_4926880) baseStart_4926880 baseEnd_4926880 := by
    simpa [prefixWord, tailWord_4926880, baseEnd_4926880] using wordTrace_append hprefix tailTrace_4926880
  have hstable : (prefixWord ++ tailWord_4926880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926880).length < 2 ^ (prefixWord ++ tailWord_4926880).sum := by decide
  have hdescent : baseEnd_4926880 < baseStart_4926880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926887 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4926887 : Nat := 118140960795 + 4926887 * 2 ^ 59
def prefixEnd_4926887 : Nat := 4983230072969 + 3 ^ 40 * 4926887 * 2
def baseEnd_4926887 : Nat := 2529861161388370265654165

theorem tailTrace_4926887 : CollatzResearch.WordTrace tailWord_4926887 prefixEnd_4926887 2529861161388370265654165 := by
  unfold tailWord_4926887
  simp only [CollatzResearch.WordTrace]
  refine ⟨179698331701737319153826915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119798887801158212769217943 179698331701737319153826915)
  ·
    refine ⟨269547497552605978730740373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179698331701737319153826915 269547497552605978730740373)
    ·
      refine ⟨12635038947778405253003455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 269547497552605978730740373 12635038947778405253003455)
      ·
        refine ⟨18952558421667607879505183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12635038947778405253003455 18952558421667607879505183)
        ·
          refine ⟨28428837632501411819257775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18952558421667607879505183 28428837632501411819257775)
          ·
            refine ⟨42643256448752117728886663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28428837632501411819257775 42643256448752117728886663)
            ·
              refine ⟨63964884673128176593329995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42643256448752117728886663 63964884673128176593329995)
              ·
                refine ⟨95947327009692264889994993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63964884673128176593329995 95947327009692264889994993)
                ·
                  refine ⟨71960495257269198667496245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95947327009692264889994993 71960495257269198667496245)
                  ·
                    refine ⟨6746296430368987375077773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71960495257269198667496245 6746296430368987375077773)
                    ·
                      refine ⟨2529861161388370265654165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6746296430368987375077773 2529861161388370265654165)
                      ·
                        rfl

theorem cell23_4926887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4926887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926887 prefixEnd_4926887 := by exact prefixLift 4926887
  have htrace : WordTrace (prefixWord ++ tailWord_4926887) baseStart_4926887 baseEnd_4926887 := by
    simpa [prefixWord, tailWord_4926887, baseEnd_4926887] using wordTrace_append hprefix tailTrace_4926887
  have hstable : (prefixWord ++ tailWord_4926887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926887).length < 2 ^ (prefixWord ++ tailWord_4926887).sum := by decide
  have hdescent : baseEnd_4926887 < baseStart_4926887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926941 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4926941 : Nat := 118140960795 + 4926941 * 2 ^ 59
def prefixEnd_4926941 : Nat := 4983230072969 + 3 ^ 40 * 4926941 * 2
def baseEnd_4926941 : Nat := 843296296447904351459639

theorem tailTrace_4926941 : CollatzResearch.WordTrace tailWord_4926941 prefixEnd_4926941 843296296447904351459639 := by
  unfold tailWord_4926941
  simp only [CollatzResearch.WordTrace]
  refine ⟨179700301243541686376292677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119800200829027790917528451 179700301243541686376292677)
  ·
    refine ⟨33693806483164066195554877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179700301243541686376292677 33693806483164066195554877)
    ·
      refine ⟨12635177431186524823333079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33693806483164066195554877 12635177431186524823333079)
      ·
        refine ⟨18952766146779787234999619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12635177431186524823333079 18952766146779787234999619)
        ·
          refine ⟨28429149220169680852499429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18952766146779787234999619 28429149220169680852499429)
          ·
            refine ⟨5330465478781815159843643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28429149220169680852499429 5330465478781815159843643)
            ·
              refine ⟨7995698218172722739765465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330465478781815159843643 7995698218172722739765465)
              ·
                refine ⟨5996773663629542054824099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7995698218172722739765465 5996773663629542054824099)
                ·
                  refine ⟨8995160495444313082236149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996773663629542054824099 8995160495444313082236149)
                  ·
                    refine ⟨843296296447904351459639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8995160495444313082236149 843296296447904351459639)
                    ·
                      rfl

theorem cell23_4926941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4926941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926941 prefixEnd_4926941 := by exact prefixLift 4926941
  have htrace : WordTrace (prefixWord ++ tailWord_4926941) baseStart_4926941 baseEnd_4926941 := by
    simpa [prefixWord, tailWord_4926941, baseEnd_4926941] using wordTrace_append hprefix tailTrace_4926941
  have hstable : (prefixWord ++ tailWord_4926941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926941).length < 2 ^ (prefixWord ++ tailWord_4926941).sum := by decide
  have hdescent : baseEnd_4926941 < baseStart_4926941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926954 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_4926954 : Nat := 118140960795 + 4926954 * 2 ^ 59
def prefixEnd_4926954 : Nat := 4983230072969 + 3 ^ 40 * 4926954 * 2
def baseEnd_4926954 : Nat := 843298521530740501172119

theorem tailTrace_4926954 : CollatzResearch.WordTrace tailWord_4926954 prefixEnd_4926954 843298521530740501172119 := by
  unfold tailWord_4926954
  simp only [CollatzResearch.WordTrace]
  refine ⟨44925193848123647399128979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119800516928329726397677277 44925193848123647399128979)
  ·
    refine ⟨67387790772185471098693469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44925193848123647399128979 67387790772185471098693469)
    ·
      refine ⟨25270421539569551662010051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67387790772185471098693469 25270421539569551662010051)
      ·
        refine ⟨37905632309354327493015077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25270421539569551662010051 37905632309354327493015077)
        ·
          refine ⟨7107306058003936404940327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37905632309354327493015077 7107306058003936404940327)
          ·
            refine ⟨10660959087005904607410491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7107306058003936404940327 10660959087005904607410491)
            ·
              refine ⟨15991438630508856911115737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10660959087005904607410491 15991438630508856911115737)
              ·
                refine ⟨11993578972881642683336803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15991438630508856911115737 11993578972881642683336803)
                ·
                  refine ⟨17990368459322464025005205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11993578972881642683336803 17990368459322464025005205)
                  ·
                    refine ⟨843298521530740501172119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17990368459322464025005205 843298521530740501172119)
                    ·
                      rfl

theorem cell23_4926954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_4926954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926954 prefixEnd_4926954 := by exact prefixLift 4926954
  have htrace : WordTrace (prefixWord ++ tailWord_4926954) baseStart_4926954 baseEnd_4926954 := by
    simpa [prefixWord, tailWord_4926954, baseEnd_4926954] using wordTrace_append hprefix tailTrace_4926954
  have hstable : (prefixWord ++ tailWord_4926954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926954).length < 2 ^ (prefixWord ++ tailWord_4926954).sum := by decide
  have hdescent : baseEnd_4926954 < baseStart_4926954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4926961 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 1, 1, 4]
def baseStart_4926961 : Nat := 118140960795 + 4926961 * 2 ^ 59
def prefixEnd_4926961 : Nat := 4983230072969 + 3 ^ 40 * 4926961 * 2
def baseEnd_4926961 : Nat := 2529899158956802976128825

theorem tailTrace_4926961 : CollatzResearch.WordTrace tailWord_4926961 prefixEnd_4926961 2529899158956802976128825 := by
  unfold tailWord_4926961
  simp only [CollatzResearch.WordTrace]
  refine ⟨179701030703469229792020737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119800687135646153194680491 179701030703469229792020737)
  ·
    refine ⟨134775773027601922344015553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179701030703469229792020737 134775773027601922344015553)
    ·
      refine ⟨101081829770701441758011665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134775773027601922344015553 101081829770701441758011665)
      ·
        refine ⟨75811372328026081318508749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101081829770701441758011665 75811372328026081318508749)
        ·
          refine ⟨28429264623009780494440781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75811372328026081318508749 28429264623009780494440781)
          ·
            refine ⟨10660974233628667685415293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28429264623009780494440781 10660974233628667685415293)
            ·
              refine ⟨3997865337610750382030735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10660974233628667685415293 3997865337610750382030735)
              ·
                refine ⟨5996798006416125573046103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3997865337610750382030735 5996798006416125573046103)
                ·
                  refine ⟨8995197009624188359569155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996798006416125573046103 8995197009624188359569155)
                  ·
                    refine ⟨13492795514436282539353733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8995197009624188359569155 13492795514436282539353733)
                    ·
                      refine ⟨2529899158956802976128825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13492795514436282539353733 2529899158956802976128825)
                      ·
                        rfl

theorem cell23_4926961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_4926961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4926961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4926961 prefixEnd_4926961 := by exact prefixLift 4926961
  have htrace : WordTrace (prefixWord ++ tailWord_4926961) baseStart_4926961 baseEnd_4926961 := by
    simpa [prefixWord, tailWord_4926961, baseEnd_4926961] using wordTrace_append hprefix tailTrace_4926961
  have hstable : (prefixWord ++ tailWord_4926961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4926961).length < 2 ^ (prefixWord ++ tailWord_4926961).sum := by decide
  have hdescent : baseEnd_4926961 < baseStart_4926961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4926961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927027 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 2, 6]
def baseStart_4927027 : Nat := 118140960795 + 4927027 * 2 ^ 59
def prefixEnd_4927027 : Nat := 4983230072969 + 3 ^ 40 * 4927027 * 2
def baseEnd_4927027 : Nat := 843311016226666572634507

theorem tailTrace_4927027 : CollatzResearch.WordTrace tailWord_4927027 prefixEnd_4927027 843311016226666572634507 := by
  unfold tailWord_4927027
  simp only [CollatzResearch.WordTrace]
  refine ⟨179703437921230123063923335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119802291947486748709282223 179703437921230123063923335)
  ·
    refine ⟨269555156881845184595885003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179703437921230123063923335 269555156881845184595885003)
    ·
      refine ⟨404332735322767776893827505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269555156881845184595885003 404332735322767776893827505)
      ·
        refine ⟨303249551492075832670370629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404332735322767776893827505 303249551492075832670370629)
        ·
          refine ⟨56859290904764218625694493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303249551492075832670370629 56859290904764218625694493)
          ·
            refine ⟨21322234089286581984635435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56859290904764218625694493 21322234089286581984635435)
            ·
              refine ⟨31983351133929872976953153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21322234089286581984635435 31983351133929872976953153)
              ·
                refine ⟨23987513350447404732714865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31983351133929872976953153 23987513350447404732714865)
                ·
                  refine ⟨17990635012835553549536149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23987513350447404732714865 17990635012835553549536149)
                  ·
                    refine ⟨843311016226666572634507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17990635012835553549536149 843311016226666572634507)
                    ·
                      rfl

theorem cell23_4927027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 6].length) (baseStart_4927027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927027 prefixEnd_4927027 := by exact prefixLift 4927027
  have htrace : WordTrace (prefixWord ++ tailWord_4927027) baseStart_4927027 baseEnd_4927027 := by
    simpa [prefixWord, tailWord_4927027, baseEnd_4927027] using wordTrace_append hprefix tailTrace_4927027
  have hstable : (prefixWord ++ tailWord_4927027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927027).length < 2 ^ (prefixWord ++ tailWord_4927027).sum := by decide
  have hdescent : baseEnd_4927027 < baseStart_4927027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927057 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 7]
def baseStart_4927057 : Nat := 118140960795 + 4927057 * 2 ^ 59
def prefixEnd_4927057 : Nat := 4983230072969 + 3 ^ 40 * 4927057 * 2
def baseEnd_4927057 : Nat := 281105383677737177836487

theorem tailTrace_4927057 : CollatzResearch.WordTrace tailWord_4927057 prefixEnd_4927057 281105383677737177836487 := by
  unfold tailWord_4927057
  simp only [CollatzResearch.WordTrace]
  refine ⟨179704532111121438187515425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119803021407414292125010283 179704532111121438187515425)
  ·
    refine ⟨134778399083341078640636569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179704532111121438187515425 134778399083341078640636569)
    ·
      refine ⟨101083799312505808980477427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134778399083341078640636569 101083799312505808980477427)
      ·
        refine ⟨151625698968758713470716141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101083799312505808980477427 151625698968758713470716141)
        ·
          refine ⟨56859637113284517551518553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151625698968758713470716141 56859637113284517551518553)
          ·
            refine ⟨42644727834963388163638915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56859637113284517551518553 42644727834963388163638915)
            ·
              refine ⟨63967091752445082245458373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42644727834963388163638915 63967091752445082245458373)
              ·
                refine ⟨11993829703583452921023445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63967091752445082245458373 11993829703583452921023445)
                ·
                  refine ⟨281105383677737177836487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11993829703583452921023445 281105383677737177836487)
                  ·
                    rfl

theorem cell23_4927057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 7].length) (baseStart_4927057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927057 prefixEnd_4927057 := by exact prefixLift 4927057
  have htrace : WordTrace (prefixWord ++ tailWord_4927057) baseStart_4927057 baseEnd_4927057 := by
    simpa [prefixWord, tailWord_4927057, baseEnd_4927057] using wordTrace_append hprefix tailTrace_4927057
  have hstable : (prefixWord ++ tailWord_4927057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927057).length < 2 ^ (prefixWord ++ tailWord_4927057).sum := by decide
  have hdescent : baseEnd_4927057 < baseStart_4927057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927068 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_4927068 : Nat := 118140960795 + 4927068 * 2 ^ 59
def prefixEnd_4927068 : Nat := 4983230072969 + 3 ^ 40 * 4927068 * 2
def baseEnd_4927068 : Nat := 2529954101386834057490833

theorem tailTrace_4927068 : CollatzResearch.WordTrace tailWord_4927068 prefixEnd_4927068 2529954101386834057490833 := by
  unfold tailWord_4927068
  simp only [CollatzResearch.WordTrace]
  refine ⟨89852466657040793533082929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119803288876054391377443905 89852466657040793533082929)
  ·
    refine ⟨67389349992780595149812197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89852466657040793533082929 67389349992780595149812197)
    ·
      refine ⟨12635503123646361590589787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67389349992780595149812197 12635503123646361590589787)
      ·
        refine ⟨18953254685469542385884681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12635503123646361590589787 18953254685469542385884681)
        ·
          refine ⟨14214941014102156789413511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18953254685469542385884681 14214941014102156789413511)
          ·
            refine ⟨21322411521153235184120267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14214941014102156789413511 21322411521153235184120267)
            ·
              refine ⟨31983617281729852776180401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21322411521153235184120267 31983617281729852776180401)
              ·
                refine ⟨23987712961297389582135301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31983617281729852776180401 23987712961297389582135301)
                ·
                  refine ⟨4497696180243260546650369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23987712961297389582135301 4497696180243260546650369)
                  ·
                    refine ⟨3373272135182445409987777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4497696180243260546650369 3373272135182445409987777)
                    ·
                      refine ⟨2529954101386834057490833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373272135182445409987777 2529954101386834057490833)
                      ·
                        rfl

theorem cell23_4927068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_4927068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927068 prefixEnd_4927068 := by exact prefixLift 4927068
  have htrace : WordTrace (prefixWord ++ tailWord_4927068) baseStart_4927068 baseEnd_4927068 := by
    simpa [prefixWord, tailWord_4927068, baseEnd_4927068] using wordTrace_append hprefix tailTrace_4927068
  have hstable : (prefixWord ++ tailWord_4927068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927068).length < 2 ^ (prefixWord ++ tailWord_4927068).sum := by decide
  have hdescent : baseEnd_4927068 < baseStart_4927068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927191 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_4927191 : Nat := 118140960795 + 4927191 * 2 ^ 59
def prefixEnd_4927191 : Nat := 4983230072969 + 3 ^ 40 * 4927191 * 2
def baseEnd_4927191 : Nat := 2530017259507337076252767

theorem tailTrace_4927191 : CollatzResearch.WordTrace tailWord_4927191 prefixEnd_4927191 2530017259507337076252767 := by
  unfold tailWord_4927191
  simp only [CollatzResearch.WordTrace]
  refine ⟨179709419492635979072893427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119806279661757319381928951 179709419492635979072893427)
  ·
    refine ⟨269564129238953968609340141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179709419492635979072893427 269564129238953968609340141)
    ·
      refine ⟨101086548464607738228502553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269564129238953968609340141 101086548464607738228502553)
      ·
        refine ⟨75814911348455803671376915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101086548464607738228502553 75814911348455803671376915)
        ·
          refine ⟨113722367022683705507065373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75814911348455803671376915 113722367022683705507065373)
          ·
            refine ⟨42645887633506389565149515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113722367022683705507065373 42645887633506389565149515)
            ·
              refine ⟨63968831450259584347724273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42645887633506389565149515 63968831450259584347724273)
              ·
                refine ⟨47976623587694688260793205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63968831450259584347724273 47976623587694688260793205)
                ·
                  refine ⟨4497808461346377024449363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47976623587694688260793205 4497808461346377024449363)
                  ·
                    refine ⟨6746712692019565536674045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4497808461346377024449363 6746712692019565536674045)
                    ·
                      refine ⟨2530017259507337076252767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6746712692019565536674045 2530017259507337076252767)
                      ·
                        rfl

theorem cell23_4927191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_4927191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927191 prefixEnd_4927191 := by exact prefixLift 4927191
  have htrace : WordTrace (prefixWord ++ tailWord_4927191) baseStart_4927191 baseEnd_4927191 := by
    simpa [prefixWord, tailWord_4927191, baseEnd_4927191] using wordTrace_append hprefix tailTrace_4927191
  have hstable : (prefixWord ++ tailWord_4927191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927191).length < 2 ^ (prefixWord ++ tailWord_4927191).sum := by decide
  have hdescent : baseEnd_4927191 < baseStart_4927191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927208 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4927208 : Nat := 118140960795 + 4927208 * 2 ^ 59
def prefixEnd_4927208 : Nat := 4983230072969 + 3 ^ 40 * 4927208 * 2
def baseEnd_4927208 : Nat := 2530025988678463509740189

theorem tailTrace_4927208 : CollatzResearch.WordTrace tailWord_4927208 prefixEnd_4927208 2530025988678463509740189 := by
  unfold tailWord_4927208
  simp only [CollatzResearch.WordTrace]
  refine ⟨89855019766787195488131139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119806693022382927317508185 89855019766787195488131139)
  ·
    refine ⟨134782529650180793232196709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89855019766787195488131139 134782529650180793232196709)
    ·
      refine ⟨25271724309408898731036883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134782529650180793232196709 25271724309408898731036883)
      ·
        refine ⟨37907586464113348096555325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25271724309408898731036883 37907586464113348096555325)
        ·
          refine ⟨14215344924042505536208247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37907586464113348096555325 14215344924042505536208247)
          ·
            refine ⟨21323017386063758304312371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14215344924042505536208247 21323017386063758304312371)
            ·
              refine ⟨31984526079095637456468557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21323017386063758304312371 31984526079095637456468557)
              ·
                refine ⟨11994197279660864046175709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31984526079095637456468557 11994197279660864046175709)
                ·
                  refine ⟨4497823979872824017315891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11994197279660864046175709 4497823979872824017315891)
                  ·
                    refine ⟨6746735969809236025973837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4497823979872824017315891 6746735969809236025973837)
                    ·
                      refine ⟨2530025988678463509740189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6746735969809236025973837 2530025988678463509740189)
                      ·
                        rfl

theorem cell23_4927208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4927208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927208 prefixEnd_4927208 := by exact prefixLift 4927208
  have htrace : WordTrace (prefixWord ++ tailWord_4927208) baseStart_4927208 baseEnd_4927208 := by
    simpa [prefixWord, tailWord_4927208, baseEnd_4927208] using wordTrace_append hprefix tailTrace_4927208
  have hstable : (prefixWord ++ tailWord_4927208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927208).length < 2 ^ (prefixWord ++ tailWord_4927208).sum := by decide
  have hdescent : baseEnd_4927208 < baseStart_4927208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927224 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 1, 6]
def baseStart_4927224 : Nat := 118140960795 + 4927224 * 2 ^ 59
def prefixEnd_4927224 : Nat := 4983230072969 + 3 ^ 40 * 4927224 * 2
def baseEnd_4927224 : Nat := 843344734789645149046705

theorem tailTrace_4927224 : CollatzResearch.WordTrace tailWord_4927224 prefixEnd_4927224 843344734789645149046705 := by
  unfold tailWord_4927224
  simp only [CollatzResearch.WordTrace]
  refine ⟨89855311550758212854422363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119807082067677617139229817 89855311550758212854422363)
  ·
    refine ⟨134782967326137319281633545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89855311550758212854422363 134782967326137319281633545)
    ·
      refine ⟨101087225494602989461225159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134782967326137319281633545 101087225494602989461225159)
      ·
        refine ⟨151630838241904484191837739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101087225494602989461225159 151630838241904484191837739)
        ·
          refine ⟨227446257362856726287756609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151630838241904484191837739 227446257362856726287756609)
          ·
            refine ⟨170584693022142544715817457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227446257362856726287756609 170584693022142544715817457)
            ·
              refine ⟨127938519766606908536863093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170584693022142544715817457 127938519766606908536863093)
              ·
                refine ⟨11994236228119397675330915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127938519766606908536863093 11994236228119397675330915)
                ·
                  refine ⟨17991354342179096512996373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11994236228119397675330915 17991354342179096512996373)
                  ·
                    refine ⟨843344734789645149046705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17991354342179096512996373 843344734789645149046705)
                    ·
                      rfl

theorem cell23_4927224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_4927224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927224 prefixEnd_4927224 := by exact prefixLift 4927224
  have htrace : WordTrace (prefixWord ++ tailWord_4927224) baseStart_4927224 baseEnd_4927224 := by
    simpa [prefixWord, tailWord_4927224, baseEnd_4927224] using wordTrace_append hprefix tailTrace_4927224
  have hstable : (prefixWord ++ tailWord_4927224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927224).length < 2 ^ (prefixWord ++ tailWord_4927224).sum := by decide
  have hdescent : baseEnd_4927224 < baseStart_4927224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927231 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 4]
def baseStart_4927231 : Nat := 118140960795 + 4927231 * 2 ^ 59
def prefixEnd_4927231 : Nat := 4983230072969 + 3 ^ 40 * 4927231 * 2
def baseEnd_4927231 : Nat := 2530037798733516919752583

theorem tailTrace_4927231 : CollatzResearch.WordTrace tailWord_4927231 prefixEnd_4927231 2530037798733516919752583 := by
  unfold tailWord_4927231
  simp only [CollatzResearch.WordTrace]
  refine ⟨179710878412491065904349547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119807252274994043936233031 179710878412491065904349547)
  ·
    refine ⟨269566317618736598856524321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179710878412491065904349547 269566317618736598856524321)
    ·
      refine ⟨202174738214052449142393241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269566317618736598856524321 202174738214052449142393241)
      ·
        refine ⟨151631053660539336856794931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202174738214052449142393241 151631053660539336856794931)
        ·
          refine ⟨227446580490809005285192397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151631053660539336856794931 227446580490809005285192397)
          ·
            refine ⟨85292467684053376981947149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227446580490809005285192397 85292467684053376981947149)
            ·
              refine ⟨31984675381520016368230181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85292467684053376981947149 31984675381520016368230181)
              ·
                refine ⟨5997126634035003069043159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31984675381520016368230181 5997126634035003069043159)
                ·
                  refine ⟨8995689951052504603564739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5997126634035003069043159 8995689951052504603564739)
                  ·
                    refine ⟨13493534926578756905347109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8995689951052504603564739 13493534926578756905347109)
                    ·
                      refine ⟨2530037798733516919752583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13493534926578756905347109 2530037798733516919752583)
                      ·
                        rfl

theorem cell23_4927231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_4927231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927231 prefixEnd_4927231 := by exact prefixLift 4927231
  have htrace : WordTrace (prefixWord ++ tailWord_4927231) baseStart_4927231 baseEnd_4927231 := by
    simpa [prefixWord, tailWord_4927231, baseEnd_4927231] using wordTrace_append hprefix tailTrace_4927231
  have hstable : (prefixWord ++ tailWord_4927231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927231).length < 2 ^ (prefixWord ++ tailWord_4927231).sum := by decide
  have hdescent : baseEnd_4927231 < baseStart_4927231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927242 : List Nat := [3, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_4927242 : Nat := 118140960795 + 4927242 * 2 ^ 59
def prefixEnd_4927242 : Nat := 4983230072969 + 3 ^ 40 * 4927242 * 2
def baseEnd_4927242 : Nat := 2530043447020716376715033

theorem tailTrace_4927242 : CollatzResearch.WordTrace tailWord_4927242 prefixEnd_4927242 2530043447020716376715033 := by
  unfold tailWord_4927242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44927819903862803695749995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119807519743634143188666653 44927819903862803695749995)
  ·
    refine ⟨67391729855794205543624993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44927819903862803695749995 67391729855794205543624993)
    ·
      refine ⟨50543797391845654157718745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67391729855794205543624993 50543797391845654157718745)
      ·
        refine ⟨37907848043884240618289059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50543797391845654157718745 37907848043884240618289059)
        ·
          refine ⟨56861772065826360927433589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37907848043884240618289059 56861772065826360927433589)
          ·
            refine ⟨5330791131171221336946899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56861772065826360927433589 5330791131171221336946899)
            ·
              refine ⟨7996186696756832005420349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330791131171221336946899 7996186696756832005420349)
              ·
                refine ⟨2998570011283812002032631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7996186696756832005420349 2998570011283812002032631)
                ·
                  refine ⟨4497855016925718003048947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998570011283812002032631 4497855016925718003048947)
                  ·
                    refine ⟨6746782525388577004573421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4497855016925718003048947 6746782525388577004573421)
                    ·
                      refine ⟨2530043447020716376715033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6746782525388577004573421 2530043447020716376715033)
                      ·
                        rfl

theorem cell23_4927242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_4927242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927242 prefixEnd_4927242 := by exact prefixLift 4927242
  have htrace : WordTrace (prefixWord ++ tailWord_4927242) baseStart_4927242 baseEnd_4927242 := by
    simpa [prefixWord, tailWord_4927242, baseEnd_4927242] using wordTrace_append hprefix tailTrace_4927242
  have hstable : (prefixWord ++ tailWord_4927242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927242).length < 2 ^ (prefixWord ++ tailWord_4927242).sum := by decide
  have hdescent : baseEnd_4927242 < baseStart_4927242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927265 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_4927265 : Nat := 118140960795 + 4927265 * 2 ^ 59
def prefixEnd_4927265 : Nat := 4983230072969 + 3 ^ 40 * 4927265 * 2
def baseEnd_4927265 : Nat := 2530055257075769786727427

theorem tailTrace_4927265 : CollatzResearch.WordTrace tailWord_4927265 prefixEnd_4927265 2530055257075769786727427 := by
  unfold tailWord_4927265
  simp only [CollatzResearch.WordTrace]
  refine ⟨179712118494367889711087249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119808078996245259807391499 179712118494367889711087249)
  ·
    refine ⟨134784088870775917283315437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179712118494367889711087249 134784088870775917283315437)
    ·
      refine ⟨50544033326540968981243289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134784088870775917283315437 50544033326540968981243289)
      ·
        refine ⟨37908024994905726735932467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50544033326540968981243289 37908024994905726735932467)
        ·
          refine ⟨56862037492358590103898701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37908024994905726735932467 56862037492358590103898701)
          ·
            refine ⟨21323264059634471288962013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56862037492358590103898701 21323264059634471288962013)
            ·
              refine ⟨7996224022362926733360755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21323264059634471288962013 7996224022362926733360755)
              ·
                refine ⟨11994336033544390100041133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7996224022362926733360755 11994336033544390100041133)
                ·
                  refine ⟨4497876012579146287515425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11994336033544390100041133 4497876012579146287515425)
                  ·
                    refine ⟨3373407009434359715636569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4497876012579146287515425 3373407009434359715636569)
                    ·
                      refine ⟨2530055257075769786727427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373407009434359715636569 2530055257075769786727427)
                      ·
                        rfl

theorem cell23_4927265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_4927265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927265 prefixEnd_4927265 := by exact prefixLift 4927265
  have htrace : WordTrace (prefixWord ++ tailWord_4927265) baseStart_4927265 baseEnd_4927265 := by
    simpa [prefixWord, tailWord_4927265, baseEnd_4927265] using wordTrace_append hprefix tailTrace_4927265
  have hstable : (prefixWord ++ tailWord_4927265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927265).length < 2 ^ (prefixWord ++ tailWord_4927265).sum := by decide
  have hdescent : baseEnd_4927265 < baseStart_4927265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927302 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4927302 : Nat := 118140960795 + 4927302 * 2 ^ 59
def prefixEnd_4927302 : Nat := 4983230072969 + 3 ^ 40 * 4927302 * 2
def baseEnd_4927302 : Nat := 2530074255859986141964757

theorem tailTrace_4927302 : CollatzResearch.WordTrace tailWord_4927302 prefixEnd_4927302 2530074255859986141964757 := by
  unfold tailWord_4927302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616045874851057657193255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 119808978663489230020122773 5616045874851057657193255)
  ·
    refine ⟨8424068812276586485789883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5616045874851057657193255 8424068812276586485789883)
    ·
      refine ⟨12636103218414879728684825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8424068812276586485789883 12636103218414879728684825)
      ·
        refine ⟨9477077413811159796513619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12636103218414879728684825 9477077413811159796513619)
        ·
          refine ⟨14215616120716739694770429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9477077413811159796513619 14215616120716739694770429)
          ·
            refine ⟨5330856045268777385538911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14215616120716739694770429 5330856045268777385538911)
            ·
              refine ⟨7996284067903166078308367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330856045268777385538911 7996284067903166078308367)
              ·
                refine ⟨11994426101854749117462551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7996284067903166078308367 11994426101854749117462551)
                ·
                  refine ⟨17991639152782123676193827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11994426101854749117462551 17991639152782123676193827)
                  ·
                    refine ⟨26987458729173185514290741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17991639152782123676193827 26987458729173185514290741)
                    ·
                      refine ⟨2530074255859986141964757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26987458729173185514290741 2530074255859986141964757)
                      ·
                        rfl

theorem cell23_4927302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4927302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927302 prefixEnd_4927302 := by exact prefixLift 4927302
  have htrace : WordTrace (prefixWord ++ tailWord_4927302) baseStart_4927302 baseEnd_4927302 := by
    simpa [prefixWord, tailWord_4927302, baseEnd_4927302] using wordTrace_append hprefix tailTrace_4927302
  have hstable : (prefixWord ++ tailWord_4927302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927302).length < 2 ^ (prefixWord ++ tailWord_4927302).sum := by decide
  have hdescent : baseEnd_4927302 < baseStart_4927302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927316 : List Nat := [2, 4, 1, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_4927316 : Nat := 118140960795 + 4927316 * 2 ^ 59
def prefixEnd_4927316 : Nat := 4983230072969 + 3 ^ 40 * 4927316 * 2
def baseEnd_4927316 : Nat := 2530081444589149087189693

theorem tailTrace_4927316 : CollatzResearch.WordTrace tailWord_4927316 prefixEnd_4927316 2530081444589149087189693 := by
  unfold tailWord_4927316
  simp only [CollatzResearch.WordTrace]
  refine ⟨89856989308591562710596901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119809319078122083614129201 89856989308591562710596901)
  ·
    refine ⟨16848185495360918008236919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89856989308591562710596901 16848185495360918008236919)
    ·
      refine ⟨25272278243041377012355379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16848185495360918008236919 25272278243041377012355379)
      ·
        refine ⟨37908417364562065518533069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25272278243041377012355379 37908417364562065518533069)
        ·
          refine ⟨14215656511710774569449901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37908417364562065518533069 14215656511710774569449901)
          ·
            refine ⟨5330871191891540463543713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14215656511710774569449901 5330871191891540463543713)
            ·
              refine ⟨3998153393918655347657785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5330871191891540463543713 3998153393918655347657785)
              ·
                refine ⟨2998615045438991510743339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998153393918655347657785 2998615045438991510743339)
                ·
                  refine ⟨4497922568158487266115009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998615045438991510743339 4497922568158487266115009)
                  ·
                    refine ⟨3373441926118865449586257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4497922568158487266115009 3373441926118865449586257)
                    ·
                      refine ⟨2530081444589149087189693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373441926118865449586257 2530081444589149087189693)
                      ·
                        rfl

theorem cell23_4927316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_4927316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927316 prefixEnd_4927316 := by exact prefixLift 4927316
  have htrace : WordTrace (prefixWord ++ tailWord_4927316) baseStart_4927316 baseEnd_4927316 := by
    simpa [prefixWord, tailWord_4927316, baseEnd_4927316] using wordTrace_append hprefix tailTrace_4927316
  have hstable : (prefixWord ++ tailWord_4927316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927316).length < 2 ^ (prefixWord ++ tailWord_4927316).sum := by decide
  have hdescent : baseEnd_4927316 < baseStart_4927316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927341 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4927341 : Nat := 118140960795 + 4927341 * 2 ^ 59
def prefixEnd_4927341 : Nat := 4983230072969 + 3 ^ 40 * 4927341 * 2
def baseEnd_4927341 : Nat := 2530094281605511489377077

theorem tailTrace_4927341 : CollatzResearch.WordTrace tailWord_4927341 prefixEnd_4927341 2530094281605511489377077 := by
  unfold tailWord_4927341
  simp only [CollatzResearch.WordTrace]
  refine ⟨179714890442092554690853877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119809926961395036460569251 179714890442092554690853877)
  ·
    refine ⟨16848270978946177002267551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179714890442092554690853877 16848270978946177002267551)
    ·
      refine ⟨25272406468419265503401327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16848270978946177002267551 25272406468419265503401327)
      ·
        refine ⟨37908609702628898255101991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25272406468419265503401327 37908609702628898255101991)
        ·
          refine ⟨56862914553943347382652987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37908609702628898255101991 56862914553943347382652987)
          ·
            refine ⟨85294371830915021073979481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56862914553943347382652987 85294371830915021073979481)
            ·
              refine ⟨63970778873186265805484611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85294371830915021073979481 63970778873186265805484611)
              ·
                refine ⟨95956168309779398708226917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63970778873186265805484611 95956168309779398708226917)
                ·
                  refine ⟨17991781558083637257792547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95956168309779398708226917 17991781558083637257792547)
                  ·
                    refine ⟨26987672337125455886688821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17991781558083637257792547 26987672337125455886688821)
                    ·
                      refine ⟨2530094281605511489377077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26987672337125455886688821 2530094281605511489377077)
                      ·
                        rfl

theorem cell23_4927341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4927341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927341 prefixEnd_4927341 := by exact prefixLift 4927341
  have htrace : WordTrace (prefixWord ++ tailWord_4927341) baseStart_4927341 baseEnd_4927341 := by
    simpa [prefixWord, tailWord_4927341, baseEnd_4927341] using wordTrace_append hprefix tailTrace_4927341
  have hstable : (prefixWord ++ tailWord_4927341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927341).length < 2 ^ (prefixWord ++ tailWord_4927341).sum := by decide
  have hdescent : baseEnd_4927341 < baseStart_4927341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927378 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 7]
def baseStart_4927378 : Nat := 118140960795 + 4927378 * 2 ^ 59
def prefixEnd_4927378 : Nat := 4983230072969 + 3 ^ 40 * 4927378 * 2
def baseEnd_4927378 : Nat := 281123697821080871623823

theorem tailTrace_4927378 : CollatzResearch.WordTrace tailWord_4927378 prefixEnd_4927378 281123697821080871623823 := by
  unfold tailWord_4927378
  simp only [CollatzResearch.WordTrace]
  refine ⟨44929059985739627502487697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119810826628639006673300525 44929059985739627502487697)
  ·
    refine ⟨33696794989304720626865773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44929059985739627502487697 33696794989304720626865773)
    ·
      refine ⟨12636298120989270235074665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33696794989304720626865773 12636298120989270235074665)
      ·
        refine ⟨9477223590741952676305999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12636298120989270235074665 9477223590741952676305999)
        ·
          refine ⟨14215835386112929014458999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9477223590741952676305999 14215835386112929014458999)
          ·
            refine ⟨21323753079169393521688499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14215835386112929014458999 21323753079169393521688499)
            ·
              refine ⟨31985629618754090282532749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21323753079169393521688499 31985629618754090282532749)
              ·
                refine ⟨11994611107032783855949781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31985629618754090282532749 11994611107032783855949781)
                ·
                  refine ⟨281123697821080871623823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11994611107032783855949781 281123697821080871623823)
                  ·
                    rfl

theorem cell23_4927378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_4927378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927378 prefixEnd_4927378 := by exact prefixLift 4927378
  have htrace : WordTrace (prefixWord ++ tailWord_4927378) baseStart_4927378 baseEnd_4927378 := by
    simpa [prefixWord, tailWord_4927378, baseEnd_4927378] using wordTrace_append hprefix tailTrace_4927378
  have hstable : (prefixWord ++ tailWord_4927378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927378).length < 2 ^ (prefixWord ++ tailWord_4927378).sum := by decide
  have hdescent : baseEnd_4927378 < baseStart_4927378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927389 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_4927389 : Nat := 118140960795 + 4927389 * 2 ^ 59
def prefixEnd_4927389 : Nat := 4983230072969 + 3 ^ 40 * 4927389 * 2
def baseEnd_4927389 : Nat := 2530118928676927301576857

theorem tailTrace_4927389 : CollatzResearch.WordTrace tailWord_4927389 prefixEnd_4927389 2530118928676927301576857 := by
  unfold tailWord_4927389
  simp only [CollatzResearch.WordTrace]
  refine ⟨179716641145918658888601221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119811094097279105925734147 179716641145918658888601221)
  ·
    refine ⟨33696870214859748541612729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179716641145918658888601221 33696870214859748541612729)
    ·
      refine ⟨25272652661144811406209547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33696870214859748541612729 25272652661144811406209547)
      ·
        refine ⟨37908978991717217109314321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25272652661144811406209547 37908978991717217109314321)
        ·
          refine ⟨28431734243787912831985741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37908978991717217109314321 28431734243787912831985741)
          ·
            refine ⟨10661900341420467311994653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28431734243787912831985741 10661900341420467311994653)
            ·
              refine ⟨3998212628032675241997995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10661900341420467311994653 3998212628032675241997995)
              ·
                refine ⟨5997318942049012862996993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998212628032675241997995 5997318942049012862996993)
                ·
                  refine ⟨4497989206536759647247745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5997318942049012862996993 4497989206536759647247745)
                  ·
                    refine ⟨3373491904902569735435809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4497989206536759647247745 3373491904902569735435809)
                    ·
                      refine ⟨2530118928676927301576857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373491904902569735435809 2530118928676927301576857)
                      ·
                        rfl

theorem cell23_4927389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_4927389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927389 prefixEnd_4927389 := by exact prefixLift 4927389
  have htrace : WordTrace (prefixWord ++ tailWord_4927389) baseStart_4927389 baseEnd_4927389 := by
    simpa [prefixWord, tailWord_4927389, baseEnd_4927389] using wordTrace_append hprefix tailTrace_4927389
  have hstable : (prefixWord ++ tailWord_4927389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927389).length < 2 ^ (prefixWord ++ tailWord_4927389).sum := by decide
  have hdescent : baseEnd_4927389 < baseStart_4927389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927411 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4]
def baseStart_4927411 : Nat := 118140960795 + 4927411 * 2 ^ 59
def prefixEnd_4927411 : Nat := 4983230072969 + 3 ^ 40 * 4927411 * 2
def baseEnd_4927411 : Nat := 2530130225251326215501755

theorem tailTrace_4927411 : CollatzResearch.WordTrace tailWord_4927411 prefixEnd_4927411 2530130225251326215501755 := by
  unfold tailWord_4927411
  simp only [CollatzResearch.WordTrace]
  refine ⟨179717443551838956645902087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119811629034559304430601391 179717443551838956645902087)
  ·
    refine ⟨269576165327758434968853131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179717443551838956645902087 269576165327758434968853131)
    ·
      refine ⟨404364247991637652453279697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269576165327758434968853131 404364247991637652453279697)
      ·
        refine ⟨303273185993728239339959773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404364247991637652453279697 303273185993728239339959773)
        ·
          refine ⟨113727444747648089752484915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303273185993728239339959773 113727444747648089752484915)
          ·
            refine ⟨170591167121472134628727373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113727444747648089752484915 170591167121472134628727373)
            ·
              refine ⟨63971687670552050485772765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170591167121472134628727373 63971687670552050485772765)
              ·
                refine ⟨23989382876457018932164787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63971687670552050485772765 23989382876457018932164787)
                ·
                  refine ⟨35984074314685528398247181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23989382876457018932164787 35984074314685528398247181)
                  ·
                    refine ⟨13494027868007073149342693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35984074314685528398247181 13494027868007073149342693)
                    ·
                      refine ⟨2530130225251326215501755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13494027868007073149342693 2530130225251326215501755)
                      ·
                        rfl

theorem cell23_4927411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_4927411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927411 prefixEnd_4927411 := by exact prefixLift 4927411
  have htrace : WordTrace (prefixWord ++ tailWord_4927411) baseStart_4927411 baseEnd_4927411 := by
    simpa [prefixWord, tailWord_4927411, baseEnd_4927411] using wordTrace_append hprefix tailTrace_4927411
  have hstable : (prefixWord ++ tailWord_4927411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927411).length < 2 ^ (prefixWord ++ tailWord_4927411).sum := by decide
  have hdescent : baseEnd_4927411 < baseStart_4927411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927441 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_4927441 : Nat := 118140960795 + 4927441 * 2 ^ 59
def prefixEnd_4927441 : Nat := 4983230072969 + 3 ^ 40 * 4927441 * 2
def baseEnd_4927441 : Nat := 2530145629670961098126617

theorem tailTrace_4927441 : CollatzResearch.WordTrace tailWord_4927441 prefixEnd_4927441 2530145629670961098126617 := by
  unfold tailWord_4927441
  simp only [CollatzResearch.WordTrace]
  refine ⟨179718537741730271769494177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119812358494486847846329451 179718537741730271769494177)
  ·
    refine ⟨134788903306297703827120633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179718537741730271769494177 134788903306297703827120633)
    ·
      refine ⟨101091677479723277870340475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134788903306297703827120633 101091677479723277870340475)
      ·
        refine ⟨151637516219584916805510713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101091677479723277870340475 151637516219584916805510713)
        ·
          refine ⟨113728137164688687604133035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151637516219584916805510713 113728137164688687604133035)
          ·
            refine ⟨170592205747033031406199553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113728137164688687604133035 170592205747033031406199553)
            ·
              refine ⟨127944154310274773554649665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170592205747033031406199553 127944154310274773554649665)
              ·
                refine ⟨95958115732706080165987249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127944154310274773554649665 95958115732706080165987249)
                ·
                  refine ⟨71968586799529560124490437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95958115732706080165987249 71968586799529560124490437)
                  ·
                    refine ⟨13494110024911792523341957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71968586799529560124490437 13494110024911792523341957)
                    ·
                      refine ⟨2530145629670961098126617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13494110024911792523341957 2530145629670961098126617)
                      ·
                        rfl

theorem cell23_4927441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_4927441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927441 prefixEnd_4927441 := by exact prefixLift 4927441
  have htrace : WordTrace (prefixWord ++ tailWord_4927441) baseStart_4927441 baseEnd_4927441 := by
    simpa [prefixWord, tailWord_4927441, baseEnd_4927441] using wordTrace_append hprefix tailTrace_4927441
  have hstable : (prefixWord ++ tailWord_4927441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927441).length < 2 ^ (prefixWord ++ tailWord_4927441).sum := by decide
  have hdescent : baseEnd_4927441 < baseStart_4927441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927448 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_4927448 : Nat := 118140960795 + 4927448 * 2 ^ 59
def prefixEnd_4927448 : Nat := 4983230072969 + 3 ^ 40 * 4927448 * 2
def baseEnd_4927448 : Nat := 2530149224035542570739085

theorem tailTrace_4927448 : CollatzResearch.WordTrace tailWord_4927448 prefixEnd_4927448 2530149224035542570739085 := by
  unfold tailWord_4927448
  simp only [CollatzResearch.WordTrace]
  refine ⟨89859396526352455982499499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119812528701803274643332665 89859396526352455982499499)
  ·
    refine ⟨134789094789528683973749249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89859396526352455982499499 134789094789528683973749249)
    ·
      refine ⟨101091821092146512980311937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134789094789528683973749249 101091821092146512980311937)
      ·
        refine ⟨75818865819109884735233953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101091821092146512980311937 75818865819109884735233953)
        ·
          refine ⟨56864149364332413551425465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75818865819109884735233953 56864149364332413551425465)
          ·
            refine ⟨42648112023249310163569099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56864149364332413551425465 42648112023249310163569099)
            ·
              refine ⟨63972168034873965245353649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42648112023249310163569099 63972168034873965245353649)
              ·
                refine ⟨47979126026155473934015237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63972168034873965245353649 47979126026155473934015237)
                ·
                  refine ⟨8996086129904151362627857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47979126026155473934015237 8996086129904151362627857)
                  ·
                    refine ⟨6747064597428113521970893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8996086129904151362627857 6747064597428113521970893)
                    ·
                      refine ⟨2530149224035542570739085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6747064597428113521970893 2530149224035542570739085)
                      ·
                        rfl

theorem cell23_4927448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_4927448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927448 prefixEnd_4927448 := by exact prefixLift 4927448
  have htrace : WordTrace (prefixWord ++ tailWord_4927448) baseStart_4927448 baseEnd_4927448 := by
    simpa [prefixWord, tailWord_4927448, baseEnd_4927448] using wordTrace_append hprefix tailTrace_4927448
  have hstable : (prefixWord ++ tailWord_4927448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927448).length < 2 ^ (prefixWord ++ tailWord_4927448).sum := by decide
  have hdescent : baseEnd_4927448 < baseStart_4927448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927491 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5]
def baseStart_4927491 : Nat := 118140960795 + 4927491 * 2 ^ 59
def prefixEnd_4927491 : Nat := 4983230072969 + 3 ^ 40 * 4927491 * 2
def baseEnd_4927491 : Nat := 2530171303703685902501387

theorem tailTrace_4927491 : CollatzResearch.WordTrace tailWord_4927491 prefixEnd_4927491 2530171303703685902501387 := by
  unfold tailWord_4927491
  simp only [CollatzResearch.WordTrace]
  refine ⟨179720361391549130308814327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119813574261032753539209551 179720361391549130308814327)
  ·
    refine ⟨269580542087323695463221491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179720361391549130308814327 269580542087323695463221491)
    ·
      refine ⟨404370813130985543194832237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269580542087323695463221491 404370813130985543194832237)
      ·
        refine ⟨151639054924119578698062089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404370813130985543194832237 151639054924119578698062089)
        ·
          refine ⟨113729291193089684023546567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151639054924119578698062089 113729291193089684023546567)
          ·
            refine ⟨170593936789634526035319851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113729291193089684023546567 170593936789634526035319851)
            ·
              refine ⟨255890905184451789052979777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170593936789634526035319851 255890905184451789052979777)
              ·
                refine ⟨191918178888338841789734833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255890905184451789052979777 191918178888338841789734833)
                ·
                  refine ⟨143938634166254131342301125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191918178888338841789734833 143938634166254131342301125)
                  ·
                    refine ⟨26988493906172649626681461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143938634166254131342301125 26988493906172649626681461)
                    ·
                      refine ⟨2530171303703685902501387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26988493906172649626681461 2530171303703685902501387)
                      ·
                        rfl

theorem cell23_4927491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_4927491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927491 prefixEnd_4927491 := by exact prefixLift 4927491
  have htrace : WordTrace (prefixWord ++ tailWord_4927491) baseStart_4927491 baseEnd_4927491 := by
    simpa [prefixWord, tailWord_4927491, baseEnd_4927491] using wordTrace_append hprefix tailTrace_4927491
  have hstable : (prefixWord ++ tailWord_4927491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927491).length < 2 ^ (prefixWord ++ tailWord_4927491).sum := by decide
  have hdescent : baseEnd_4927491 < baseStart_4927491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927548 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_4927548 : Nat := 118140960795 + 4927548 * 2 ^ 59
def prefixEnd_4927548 : Nat := 4983230072969 + 3 ^ 40 * 4927548 * 2
def baseEnd_4927548 : Nat := 2530200572100992179488625

theorem tailTrace_4927548 : CollatzResearch.WordTrace tailWord_4927548 prefixEnd_4927548 2530200572100992179488625 := by
  unfold tailWord_4927548
  simp only [CollatzResearch.WordTrace]
  refine ⟨89861220176171314521819649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119814960234895086029092865 89861220176171314521819649)
  ·
    refine ⟨67395915132128485891364737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89861220176171314521819649 67395915132128485891364737)
    ·
      refine ⟨50546936349096364418523553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67395915132128485891364737 50546936349096364418523553)
      ·
        refine ⟨37910202261822273313892665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50546936349096364418523553 37910202261822273313892665)
        ·
          refine ⟨28432651696366704985419499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37910202261822273313892665 28432651696366704985419499)
          ·
            refine ⟨42648977544550057478129249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28432651696366704985419499 42648977544550057478129249)
            ·
              refine ⟨31986733158412543108596937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42648977544550057478129249 31986733158412543108596937)
              ·
                refine ⟨23990049868809407331447703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31986733158412543108596937 23990049868809407331447703)
                ·
                  refine ⟨35985074803214110997171555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23990049868809407331447703 35985074803214110997171555)
                  ·
                    refine ⟨53977612204821166495757333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35985074803214110997171555 53977612204821166495757333)
                    ·
                      refine ⟨2530200572100992179488625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53977612204821166495757333 2530200572100992179488625)
                      ·
                        rfl

theorem cell23_4927548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_4927548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927548 prefixEnd_4927548 := by exact prefixLift 4927548
  have htrace : WordTrace (prefixWord ++ tailWord_4927548) baseStart_4927548 baseEnd_4927548 := by
    simpa [prefixWord, tailWord_4927548, baseEnd_4927548] using wordTrace_append hprefix tailTrace_4927548
  have hstable : (prefixWord ++ tailWord_4927548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927548).length < 2 ^ (prefixWord ++ tailWord_4927548).sum := by decide
  have hdescent : baseEnd_4927548 < baseStart_4927548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927552 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 3, 2, 2]
def baseStart_4927552 : Nat := 118140960795 + 4927552 * 2 ^ 59
def prefixEnd_4927552 : Nat := 4983230072969 + 3 ^ 40 * 4927552 * 2
def baseEnd_4927552 : Nat := 2530202626023610163838607

theorem tailTrace_4927552 : CollatzResearch.WordTrace tailWord_4927552 prefixEnd_4927552 2530202626023610163838607 := by
  unfold tailWord_4927552
  simp only [CollatzResearch.WordTrace]
  refine ⟨89861293122164068863392455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119815057496218758484523273 89861293122164068863392455)
  ·
    refine ⟨134791939683246103295088683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89861293122164068863392455 134791939683246103295088683)
    ·
      refine ⟨202187909524869154942633025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134791939683246103295088683 202187909524869154942633025)
      ·
        refine ⟨151640932143651866206974769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202187909524869154942633025 151640932143651866206974769)
        ·
          refine ⟨113730699107738899655231077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151640932143651866206974769 113730699107738899655231077)
          ·
            refine ⟨21324506082701043685355827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113730699107738899655231077 21324506082701043685355827)
            ·
              refine ⟨31986759124051565528033741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21324506082701043685355827 31986759124051565528033741)
              ·
                refine ⟨11995034671519337073012653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31986759124051565528033741 11995034671519337073012653)
                ·
                  refine ⟨4498138001819751402379745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11995034671519337073012653 4498138001819751402379745)
                  ·
                    refine ⟨3373603501364813551784809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4498138001819751402379745 3373603501364813551784809)
                    ·
                      refine ⟨2530202626023610163838607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373603501364813551784809 2530202626023610163838607)
                      ·
                        rfl

theorem cell23_4927552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_4927552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927552 prefixEnd_4927552 := by exact prefixLift 4927552
  have htrace : WordTrace (prefixWord ++ tailWord_4927552) baseStart_4927552 baseEnd_4927552 := by
    simpa [prefixWord, tailWord_4927552, baseEnd_4927552] using wordTrace_append hprefix tailTrace_4927552
  have hstable : (prefixWord ++ tailWord_4927552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927552).length < 2 ^ (prefixWord ++ tailWord_4927552).sum := by decide
  have hdescent : baseEnd_4927552 < baseStart_4927552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927565 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4927565 : Nat := 118140960795 + 4927565 * 2 ^ 59
def prefixEnd_4927565 : Nat := 4983230072969 + 3 ^ 40 * 4927565 * 2
def baseEnd_4927565 : Nat := 2530209301272118612976047

theorem tailTrace_4927565 : CollatzResearch.WordTrace tailWord_4927565 prefixEnd_4927565 2530209301272118612976047 := by
  unfold tailWord_4927565
  simp only [CollatzResearch.WordTrace]
  refine ⟨179723060393281040947008149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119815373595520693964672099 179723060393281040947008149)
  ·
    refine ⟨8424518455935048794391007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179723060393281040947008149 8424518455935048794391007)
    ·
      refine ⟨12636777683902573191586511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8424518455935048794391007 12636777683902573191586511)
      ·
        refine ⟨18955166525853859787379767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12636777683902573191586511 18955166525853859787379767)
        ·
          refine ⟨28432749788780789681069651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18955166525853859787379767 28432749788780789681069651)
          ·
            refine ⟨42649124683171184521604477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28432749788780789681069651 42649124683171184521604477)
            ·
              refine ⟨15993421756189194195601679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42649124683171184521604477 15993421756189194195601679)
              ·
                refine ⟨23990132634283791293402519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15993421756189194195601679 23990132634283791293402519)
                ·
                  refine ⟨35985198951425686940103779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23990132634283791293402519 35985198951425686940103779)
                  ·
                    refine ⟨53977798427138530410155669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35985198951425686940103779 53977798427138530410155669)
                    ·
                      refine ⟨2530209301272118612976047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53977798427138530410155669 2530209301272118612976047)
                      ·
                        rfl

theorem cell23_4927565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4927565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927565 prefixEnd_4927565 := by exact prefixLift 4927565
  have htrace : WordTrace (prefixWord ++ tailWord_4927565) baseStart_4927565 baseEnd_4927565 := by
    simpa [prefixWord, tailWord_4927565, baseEnd_4927565] using wordTrace_append hprefix tailTrace_4927565
  have hstable : (prefixWord ++ tailWord_4927565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927565).length < 2 ^ (prefixWord ++ tailWord_4927565).sum := by decide
  have hdescent : baseEnd_4927565 < baseStart_4927565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927602 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_4927602 : Nat := 118140960795 + 4927602 * 2 ^ 59
def prefixEnd_4927602 : Nat := 4983230072969 + 3 ^ 40 * 4927602 * 2
def baseEnd_4927602 : Nat := 2530228300056334968213377

theorem tailTrace_4927602 : CollatzResearch.WordTrace tailWord_4927602 prefixEnd_4927602 2530228300056334968213377 := by
  unfold tailWord_4927602
  simp only [CollatzResearch.WordTrace]
  refine ⟨44931102473536749066526265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119816273262764664177403373 44931102473536749066526265)
  ·
    refine ⟨33698326855152561799894699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44931102473536749066526265 33698326855152561799894699)
    ·
      refine ⟨50547490282728842699842049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33698326855152561799894699 50547490282728842699842049)
      ·
        refine ⟨37910617712046632024881537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50547490282728842699842049 37910617712046632024881537)
        ·
          refine ⟨28432963284034974018661153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37910617712046632024881537 28432963284034974018661153)
          ·
            refine ⟨21324722463026230513995865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28432963284034974018661153 21324722463026230513995865)
            ·
              refine ⟨15993541847269672885496899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21324722463026230513995865 15993541847269672885496899)
              ·
                refine ⟨23990312770904509328245349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15993541847269672885496899 23990312770904509328245349)
                ·
                  refine ⟨4498183644544595499046003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23990312770904509328245349 4498183644544595499046003)
                  ·
                    refine ⟨6747275466816893248569005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4498183644544595499046003 6747275466816893248569005)
                    ·
                      refine ⟨2530228300056334968213377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6747275466816893248569005 2530228300056334968213377)
                      ·
                        rfl

theorem cell23_4927602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_4927602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927602 prefixEnd_4927602 := by exact prefixLift 4927602
  have htrace : WordTrace (prefixWord ++ tailWord_4927602) baseStart_4927602 baseEnd_4927602 := by
    simpa [prefixWord, tailWord_4927602, baseEnd_4927602] using wordTrace_append hprefix tailTrace_4927602
  have hstable : (prefixWord ++ tailWord_4927602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927602).length < 2 ^ (prefixWord ++ tailWord_4927602).sum := by decide
  have hdescent : baseEnd_4927602 < baseStart_4927602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927608 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_4927608 : Nat := 118140960795 + 4927608 * 2 ^ 59
def prefixEnd_4927608 : Nat := 4983230072969 + 3 ^ 40 * 4927608 * 2
def baseEnd_4927608 : Nat := 2530231380940261944738349

theorem tailTrace_4927608 : CollatzResearch.WordTrace tailWord_4927608 prefixEnd_4927608 2530231380940261944738349 := by
  unfold tailWord_4927608
  simp only [CollatzResearch.WordTrace]
  refine ⟨89862314366062629645411739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119816419154750172860548985 89862314366062629645411739)
  ·
    refine ⟨134793471549093944468117609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89862314366062629645411739 134793471549093944468117609)
    ·
      refine ⟨101095103661820458351088207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134793471549093944468117609 101095103661820458351088207)
      ·
        refine ⟨151642655492730687526632311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101095103661820458351088207 151642655492730687526632311)
        ·
          refine ⟨227463983239096031289948467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151642655492730687526632311 227463983239096031289948467)
          ·
            refine ⟨341195974858644046934922701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227463983239096031289948467 341195974858644046934922701)
            ·
              refine ⟨127948490571991517600596013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341195974858644046934922701 127948490571991517600596013)
              ·
                refine ⟨47980683964496819100223505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127948490571991517600596013 47980683964496819100223505)
                ·
                  refine ⟨35985512973372614325167629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47980683964496819100223505 35985512973372614325167629)
                  ·
                    refine ⟨13494567365014730371937861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35985512973372614325167629 13494567365014730371937861)
                    ·
                      refine ⟨2530231380940261944738349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13494567365014730371937861 2530231380940261944738349)
                      ·
                        rfl

theorem cell23_4927608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_4927608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927608 prefixEnd_4927608 := by exact prefixLift 4927608
  have htrace : WordTrace (prefixWord ++ tailWord_4927608) baseStart_4927608 baseEnd_4927608 := by
    simpa [prefixWord, tailWord_4927608, baseEnd_4927608] using wordTrace_append hprefix tailTrace_4927608
  have hstable : (prefixWord ++ tailWord_4927608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927608).length < 2 ^ (prefixWord ++ tailWord_4927608).sum := by decide
  have hdescent : baseEnd_4927608 < baseStart_4927608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927619 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 2, 1, 3]
def baseStart_4927619 : Nat := 118140960795 + 4927619 * 2 ^ 59
def prefixEnd_4927619 : Nat := 4983230072969 + 3 ^ 40 * 4927619 * 2
def baseEnd_4927619 : Nat := 2530237029227461401700799

theorem tailTrace_4927619 : CollatzResearch.WordTrace tailWord_4927619 prefixEnd_4927619 2530237029227461401700799 := by
  unfold tailWord_4927619
  simp only [CollatzResearch.WordTrace]
  refine ⟨179725029935085408169473911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119816686623390272112982607 179725029935085408169473911)
  ·
    refine ⟨269587544902628112254210867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179725029935085408169473911 269587544902628112254210867)
    ·
      refine ⟨404381317353942168381316301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269587544902628112254210867 404381317353942168381316301)
      ·
        refine ⟨151642994007728313142993613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404381317353942168381316301 151642994007728313142993613)
        ·
          refine ⟨56866122752898117428622605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151642994007728313142993613 56866122752898117428622605)
          ·
            refine ⟨21324796032336794035733477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56866122752898117428622605 21324796032336794035733477)
            ·
              refine ⟨3998399256063148881700027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21324796032336794035733477 3998399256063148881700027)
              ·
                refine ⟨5997598884094723322550041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998399256063148881700027 5997598884094723322550041)
                ·
                  refine ⟨4498199163071042491912531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5997598884094723322550041 4498199163071042491912531)
                  ·
                    refine ⟨6747298744606563737868797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4498199163071042491912531 6747298744606563737868797)
                    ·
                      refine ⟨2530237029227461401700799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6747298744606563737868797 2530237029227461401700799)
                      ·
                        rfl

theorem cell23_4927619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_4927619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927619 prefixEnd_4927619 := by exact prefixLift 4927619
  have htrace : WordTrace (prefixWord ++ tailWord_4927619) baseStart_4927619 baseEnd_4927619 := by
    simpa [prefixWord, tailWord_4927619, baseEnd_4927619] using wordTrace_append hprefix tailTrace_4927619
  have hstable : (prefixWord ++ tailWord_4927619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927619).length < 2 ^ (prefixWord ++ tailWord_4927619).sum := by decide
  have hdescent : baseEnd_4927619 < baseStart_4927619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927645 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_4927645 : Nat := 118140960795 + 4927645 * 2 ^ 59
def prefixEnd_4927645 : Nat := 4983230072969 + 3 ^ 40 * 4927645 * 2
def baseEnd_4927645 : Nat := 2530250379724478299975679

theorem tailTrace_4927645 : CollatzResearch.WordTrace tailWord_4927645 prefixEnd_4927645 2530250379724478299975679 := by
  unfold tailWord_4927645
  simp only [CollatzResearch.WordTrace]
  refine ⟨179725978232991214609920389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119817318821994143073280259 179725978232991214609920389)
  ·
    refine ⟨33698620918685852739360073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179725978232991214609920389 33698620918685852739360073)
    ·
      refine ⟨25273965689014389554520055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33698620918685852739360073 25273965689014389554520055)
      ·
        refine ⟨37910948533521584331780083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25273965689014389554520055 37910948533521584331780083)
        ·
          refine ⟨56866422800282376497670125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37910948533521584331780083 56866422800282376497670125)
          ·
            refine ⟨21324908550105891186626297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56866422800282376497670125 21324908550105891186626297)
            ·
              refine ⟨15993681412579418389969723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21324908550105891186626297 15993681412579418389969723)
              ·
                refine ⟨23990522118869127584954585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15993681412579418389969723 23990522118869127584954585)
                ·
                  refine ⟨17992891589151845688715939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23990522118869127584954585 17992891589151845688715939)
                  ·
                    refine ⟨26989337383727768533073909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17992891589151845688715939 26989337383727768533073909)
                    ·
                      refine ⟨2530250379724478299975679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26989337383727768533073909 2530250379724478299975679)
                      ·
                        rfl

theorem cell23_4927645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_4927645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927645 prefixEnd_4927645 := by exact prefixLift 4927645
  have htrace : WordTrace (prefixWord ++ tailWord_4927645) baseStart_4927645 baseEnd_4927645 := by
    simpa [prefixWord, tailWord_4927645, baseEnd_4927645] using wordTrace_append hprefix tailTrace_4927645
  have hstable : (prefixWord ++ tailWord_4927645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927645).length < 2 ^ (prefixWord ++ tailWord_4927645).sum := by decide
  have hdescent : baseEnd_4927645 < baseStart_4927645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927675 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 3]
def baseStart_4927675 : Nat := 118140960795 + 4927675 * 2 ^ 59
def prefixEnd_4927675 : Nat := 4983230072969 + 3 ^ 40 * 4927675 * 2
def baseEnd_4927675 : Nat := 2530265784144113182600541

theorem tailTrace_4927675 : CollatzResearch.WordTrace tailWord_4927675 prefixEnd_4927675 2530265784144113182600541 := by
  unfold tailWord_4927675
  simp only [CollatzResearch.WordTrace]
  refine ⟨179727072422882529733512479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119818048281921686489008319 179727072422882529733512479)
  ·
    refine ⟨269590608634323794600268719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179727072422882529733512479 269590608634323794600268719)
    ·
      refine ⟨404385912951485691900403079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269590608634323794600268719 404385912951485691900403079)
      ·
        refine ⟨606578869427228537850604619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404385912951485691900403079 606578869427228537850604619)
        ·
          refine ⟨909868304140842806775906929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606578869427228537850604619 909868304140842806775906929)
          ·
            refine ⟨682401228105632105081930197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909868304140842806775906929 682401228105632105081930197)
            ·
              refine ⟨15993778783725752462857739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 682401228105632105081930197 15993778783725752462857739)
              ·
                refine ⟨23990668175588628694286609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15993778783725752462857739 23990668175588628694286609)
                ·
                  refine ⟨17993001131691471520714957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23990668175588628694286609 17993001131691471520714957)
                  ·
                    refine ⟨6747375424384301820268109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17993001131691471520714957 6747375424384301820268109)
                    ·
                      refine ⟨2530265784144113182600541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6747375424384301820268109 2530265784144113182600541)
                      ·
                        rfl

theorem cell23_4927675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 3].length) (baseStart_4927675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927675 prefixEnd_4927675 := by exact prefixLift 4927675
  have htrace : WordTrace (prefixWord ++ tailWord_4927675) baseStart_4927675 baseEnd_4927675 := by
    simpa [prefixWord, tailWord_4927675, baseEnd_4927675] using wordTrace_append hprefix tailTrace_4927675
  have hstable : (prefixWord ++ tailWord_4927675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927675).length < 2 ^ (prefixWord ++ tailWord_4927675).sum := by decide
  have hdescent : baseEnd_4927675 < baseStart_4927675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927745 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4927745 : Nat := 118140960795 + 4927745 * 2 ^ 59
def prefixEnd_4927745 : Nat := 4983230072969 + 3 ^ 40 * 4927745 * 2
def baseEnd_4927745 : Nat := 2530301727789927908725219

theorem tailTrace_4927745 : CollatzResearch.WordTrace tailWord_4927745 prefixEnd_4927745 2530301727789927908725219 := by
  unfold tailWord_4927745
  simp only [CollatzResearch.WordTrace]
  refine ⟨179729625532628931688560689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119819750355085954459040459 179729625532628931688560689)
  ·
    refine ⟨134797219149471698766420517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179729625532628931688560689 134797219149471698766420517)
    ·
      refine ⟨25274478590525943518703847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134797219149471698766420517 25274478590525943518703847)
      ·
        refine ⟨37911717885788915278055771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25274478590525943518703847 37911717885788915278055771)
        ·
          refine ⟨56867576828683372917083657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37911717885788915278055771 56867576828683372917083657)
          ·
            refine ⟨42650682621512529687812743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56867576828683372917083657 42650682621512529687812743)
            ·
              refine ⟨63976023932268794531719115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42650682621512529687812743 63976023932268794531719115)
              ·
                refine ⟨95964035898403191797578673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63976023932268794531719115 95964035898403191797578673)
                ·
                  refine ⟨71973026923802393848184005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95964035898403191797578673 71973026923802393848184005)
                  ·
                    refine ⟨13494942548212948846534501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71973026923802393848184005 13494942548212948846534501)
                    ·
                      refine ⟨2530301727789927908725219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13494942548212948846534501 2530301727789927908725219)
                      ·
                        rfl

theorem cell23_4927745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4927745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927745 prefixEnd_4927745 := by exact prefixLift 4927745
  have htrace : WordTrace (prefixWord ++ tailWord_4927745) baseStart_4927745 baseEnd_4927745 := by
    simpa [prefixWord, tailWord_4927745, baseEnd_4927745] using wordTrace_append hprefix tailTrace_4927745
  have hstable : (prefixWord ++ tailWord_4927745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927745).length < 2 ^ (prefixWord ++ tailWord_4927745).sum := by decide
  have hdescent : baseEnd_4927745 < baseStart_4927745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927752 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_4927752 : Nat := 118140960795 + 4927752 * 2 ^ 59
def prefixEnd_4927752 : Nat := 4983230072969 + 3 ^ 40 * 4927752 * 2
def baseEnd_4927752 : Nat := 2530305322154509381337687

theorem tailTrace_4927752 : CollatzResearch.WordTrace tailWord_4927752 prefixEnd_4927752 2530305322154509381337687 := by
  unfold tailWord_4927752
  simp only [CollatzResearch.WordTrace]
  refine ⟨89864940421801785942032755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119819920562402381256043673 89864940421801785942032755)
  ·
    refine ⟨134797410632702678913049133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89864940421801785942032755 134797410632702678913049133)
    ·
      refine ⟨50549028987263504592393425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134797410632702678913049133 50549028987263504592393425)
      ·
        refine ⟨37911771740447628444295069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50549028987263504592393425 37911771740447628444295069)
        ·
          refine ⟨14216914402667860666610651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37911771740447628444295069 14216914402667860666610651)
          ·
            refine ⟨21325371604001790999915977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14216914402667860666610651 21325371604001790999915977)
            ·
              refine ⟨15994028703001343249936983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21325371604001790999915977 15994028703001343249936983)
              ·
                refine ⟨23991043054502014874905475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15994028703001343249936983 23991043054502014874905475)
                ·
                  refine ⟨35986564581753022312358213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23991043054502014874905475 35986564581753022312358213)
                  ·
                    refine ⟨6747480859078691683567165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35986564581753022312358213 6747480859078691683567165)
                    ·
                      refine ⟨2530305322154509381337687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6747480859078691683567165 2530305322154509381337687)
                      ·
                        rfl

theorem cell23_4927752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_4927752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927752 prefixEnd_4927752 := by exact prefixLift 4927752
  have htrace : WordTrace (prefixWord ++ tailWord_4927752) baseStart_4927752 baseEnd_4927752 := by
    simpa [prefixWord, tailWord_4927752, baseEnd_4927752] using wordTrace_append hprefix tailTrace_4927752
  have hstable : (prefixWord ++ tailWord_4927752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927752).length < 2 ^ (prefixWord ++ tailWord_4927752).sum := by decide
  have hdescent : baseEnd_4927752 < baseStart_4927752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927792 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 1, 5, 2]
def baseStart_4927792 : Nat := 118140960795 + 4927792 * 2 ^ 59
def prefixEnd_4927792 : Nat := 4983230072969 + 3 ^ 40 * 4927792 * 2
def baseEnd_4927792 : Nat := 2530325861380689224837503

theorem tailTrace_4927792 : CollatzResearch.WordTrace tailWord_4927792 prefixEnd_4927792 2530325861380689224837503 := by
  unfold tailWord_4927792
  simp only [CollatzResearch.WordTrace]
  refine ⟨89865669881729329357760815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119820893175639105810347753 89865669881729329357760815)
  ·
    refine ⟨134798504822593994036641223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89865669881729329357760815 134798504822593994036641223)
    ·
      refine ⟨202197757233890991054961835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134798504822593994036641223 202197757233890991054961835)
      ·
        refine ⟨303296635850836486582442753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202197757233890991054961835 303296635850836486582442753)
        ·
          refine ⟨227472476888127364936832065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303296635850836486582442753 227472476888127364936832065)
          ·
            refine ⟨170604357666095523702624049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227472476888127364936832065 170604357666095523702624049)
            ·
              refine ⟨127953268249571642776968037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170604357666095523702624049 127953268249571642776968037)
              ·
                refine ⟨23991237796794683020681507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127953268249571642776968037 23991237796794683020681507)
                ·
                  refine ⟨35986856695192024531022261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23991237796794683020681507 35986856695192024531022261)
                  ·
                    refine ⟨3373767815174252299783337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35986856695192024531022261 3373767815174252299783337)
                    ·
                      refine ⟨2530325861380689224837503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373767815174252299783337 2530325861380689224837503)
                      ·
                        rfl

theorem cell23_4927792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 5, 2].length) (baseStart_4927792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927792 prefixEnd_4927792 := by exact prefixLift 4927792
  have htrace : WordTrace (prefixWord ++ tailWord_4927792) baseStart_4927792 baseEnd_4927792 := by
    simpa [prefixWord, tailWord_4927792, baseEnd_4927792] using wordTrace_append hprefix tailTrace_4927792
  have hstable : (prefixWord ++ tailWord_4927792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927792).length < 2 ^ (prefixWord ++ tailWord_4927792).sum := by decide
  have hdescent : baseEnd_4927792 < baseStart_4927792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927802 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_4927802 : Nat := 118140960795 + 4927802 * 2 ^ 59
def prefixEnd_4927802 : Nat := 4983230072969 + 3 ^ 40 * 4927802 * 2
def baseEnd_4927802 : Nat := 843443665395744728570819

theorem tailTrace_4927802 : CollatzResearch.WordTrace tailWord_4927802 prefixEnd_4927802 843443665395744728570819 := by
  unfold tailWord_4927802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44932926123355607605846415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119821136328948286948923773 44932926123355607605846415)
  ·
    refine ⟨67399389185033411408769623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44932926123355607605846415 67399389185033411408769623)
    ·
      refine ⟨101099083777550117113154435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67399389185033411408769623 101099083777550117113154435)
      ·
        refine ⟨151648625666325175669731653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101099083777550117113154435 151648625666325175669731653)
        ·
          refine ⟨28434117312435970438074685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151648625666325175669731653 28434117312435970438074685)
          ·
            refine ⟨10662793992163488914278007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28434117312435970438074685 10662793992163488914278007)
            ·
              refine ⟨15994190988245233371417011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10662793992163488914278007 15994190988245233371417011)
              ·
                refine ⟨23991286482367850057125517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15994190988245233371417011 23991286482367850057125517)
                ·
                  refine ⟨8996732430887943771422069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23991286482367850057125517 8996732430887943771422069)
                  ·
                    refine ⟨843443665395744728570819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8996732430887943771422069 843443665395744728570819)
                    ·
                      rfl

theorem cell23_4927802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_4927802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927802 prefixEnd_4927802 := by exact prefixLift 4927802
  have htrace : WordTrace (prefixWord ++ tailWord_4927802) baseStart_4927802 baseEnd_4927802 := by
    simpa [prefixWord, tailWord_4927802, baseEnd_4927802] using wordTrace_append hprefix tailTrace_4927802
  have hstable : (prefixWord ++ tailWord_4927802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927802).length < 2 ^ (prefixWord ++ tailWord_4927802).sum := by decide
  have hdescent : baseEnd_4927802 < baseStart_4927802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927856 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 3, 2, 2]
def baseStart_4927856 : Nat := 118140960795 + 4927856 * 2 ^ 59
def prefixEnd_4927856 : Nat := 4983230072969 + 3 ^ 40 * 4927856 * 2
def baseEnd_4927856 : Nat := 2530358724142576974437209

theorem tailTrace_4927856 : CollatzResearch.WordTrace tailWord_4927856 prefixEnd_4927856 2530358724142576974437209 := by
  unfold tailWord_4927856
  simp only [CollatzResearch.WordTrace]
  refine ⟨89866837017613398822925711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119822449356817865097234281 89866837017613398822925711)
  ·
    refine ⟨134800255526420098234388567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89866837017613398822925711 134800255526420098234388567)
    ·
      refine ⟨202200383289630147351582851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134800255526420098234388567 202200383289630147351582851)
      ·
        refine ⟨303300574934445221027374277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202200383289630147351582851 303300574934445221027374277)
        ·
          refine ⟨56868857800208478942632677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303300574934445221027374277 56868857800208478942632677)
          ·
            refine ⟨10662910837539089801743627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56868857800208478942632677 10662910837539089801743627)
            ·
              refine ⟨15994366256308634702615441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10662910837539089801743627 15994366256308634702615441)
              ·
                refine ⟨11995774692231476026961581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15994366256308634702615441 11995774692231476026961581)
                ·
                  refine ⟨4498415509586803510110593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11995774692231476026961581 4498415509586803510110593)
                  ·
                    refine ⟨3373811632190102632582945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4498415509586803510110593 3373811632190102632582945)
                    ·
                      refine ⟨2530358724142576974437209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373811632190102632582945 2530358724142576974437209)
                      ·
                        rfl

theorem cell23_4927856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 2, 2].length) (baseStart_4927856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927856 prefixEnd_4927856 := by exact prefixLift 4927856
  have htrace : WordTrace (prefixWord ++ tailWord_4927856) baseStart_4927856 baseEnd_4927856 := by
    simpa [prefixWord, tailWord_4927856, baseEnd_4927856] using wordTrace_append hprefix tailTrace_4927856
  have hstable : (prefixWord ++ tailWord_4927856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927856).length < 2 ^ (prefixWord ++ tailWord_4927856).sum := by decide
  have hdescent : baseEnd_4927856 < baseStart_4927856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927873 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4927873 : Nat := 118140960795 + 4927873 * 2 ^ 59
def prefixEnd_4927873 : Nat := 4983230072969 + 3 ^ 40 * 4927873 * 2
def baseEnd_4927873 : Nat := 2530367453313703407924631

theorem tailTrace_4927873 : CollatzResearch.WordTrace tailWord_4927873 prefixEnd_4927873 2530367453313703407924631 := by
  unfold tailWord_4927873
  simp only [CollatzResearch.WordTrace]
  refine ⟨179734294076165209549220273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119822862717443473032813515 179734294076165209549220273)
  ·
    refine ⟨134800720557123907161915205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179734294076165209549220273 134800720557123907161915205)
    ·
      refine ⟨25275135104460732592859101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134800720557123907161915205 25275135104460732592859101)
      ·
        refine ⟨9478175664172774722322163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25275135104460732592859101 9478175664172774722322163)
        ·
          refine ⟨14217263496259162083483245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478175664172774722322163 14217263496259162083483245)
          ·
            refine ⟨5331473811097185781306217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14217263496259162083483245 5331473811097185781306217)
            ·
              refine ⟨3998605358322889335979663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5331473811097185781306217 3998605358322889335979663)
              ·
                refine ⟨5997908037484334003969495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998605358322889335979663 5997908037484334003969495)
                ·
                  refine ⟨8996862056226501005954243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5997908037484334003969495 8996862056226501005954243)
                  ·
                    refine ⟨13495293084339751508931365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8996862056226501005954243 13495293084339751508931365)
                    ·
                      refine ⟨2530367453313703407924631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13495293084339751508931365 2530367453313703407924631)
                      ·
                        rfl

theorem cell23_4927873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4927873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927873 prefixEnd_4927873 := by exact prefixLift 4927873
  have htrace : WordTrace (prefixWord ++ tailWord_4927873) baseStart_4927873 baseEnd_4927873 := by
    simpa [prefixWord, tailWord_4927873, baseEnd_4927873] using wordTrace_append hprefix tailTrace_4927873
  have hstable : (prefixWord ++ tailWord_4927873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927873).length < 2 ^ (prefixWord ++ tailWord_4927873).sum := by decide
  have hdescent : baseEnd_4927873 < baseStart_4927873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927946 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_4927946 : Nat := 118140960795 + 4927946 * 2 ^ 59
def prefixEnd_4927946 : Nat := 4983230072969 + 3 ^ 40 * 4927946 * 2
def baseEnd_4927946 : Nat := 2530404937401481622311795

theorem tailTrace_4927946 : CollatzResearch.WordTrace tailWord_4927946 prefixEnd_4927946 2530404937401481622311795 := by
  unfold tailWord_4927946
  simp only [CollatzResearch.WordTrace]
  refine ⟨44934239151225185754156923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119824637736600495344418461 44934239151225185754156923)
  ·
    refine ⟨67401358726837778631235385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44934239151225185754156923 67401358726837778631235385)
    ·
      refine ⟨50551019045128333973426539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67401358726837778631235385 50551019045128333973426539)
      ·
        refine ⟨75826528567692500960139809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50551019045128333973426539 75826528567692500960139809)
        ·
          refine ⟨56869896425769375720104857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75826528567692500960139809 56869896425769375720104857)
          ·
            refine ⟨42652422319327031790078643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56869896425769375720104857 42652422319327031790078643)
            ·
              refine ⟨63978633478990547685117965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42652422319327031790078643 63978633478990547685117965)
              ·
                refine ⟨23991987554621455381919237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63978633478990547685117965 23991987554621455381919237)
                ·
                  refine ⟨4498497666491522884109857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23991987554621455381919237 4498497666491522884109857)
                  ·
                    refine ⟨3373873249868642163082393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4498497666491522884109857 3373873249868642163082393)
                    ·
                      refine ⟨2530404937401481622311795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373873249868642163082393 2530404937401481622311795)
                      ·
                        rfl

theorem cell23_4927946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_4927946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927946 prefixEnd_4927946 := by exact prefixLift 4927946
  have htrace : WordTrace (prefixWord ++ tailWord_4927946) baseStart_4927946 baseEnd_4927946 := by
    simpa [prefixWord, tailWord_4927946, baseEnd_4927946] using wordTrace_append hprefix tailTrace_4927946
  have hstable : (prefixWord ++ tailWord_4927946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927946).length < 2 ^ (prefixWord ++ tailWord_4927946).sum := by decide
  have hdescent : baseEnd_4927946 < baseStart_4927946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4927992 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_4927992 : Nat := 118140960795 + 4927992 * 2 ^ 59
def prefixEnd_4927992 : Nat := 4983230072969 + 3 ^ 40 * 4927992 * 2
def baseEnd_4927992 : Nat := 2530428557511588442336583

theorem tailTrace_4927992 : CollatzResearch.WordTrace tailWord_4927992 prefixEnd_4927992 2530428557511588442336583 := by
  unfold tailWord_4927992
  simp only [CollatzResearch.WordTrace]
  refine ⟨89869317181367046436401115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119825756241822728581868153 89869317181367046436401115)
  ·
    refine ⟨134803975772050569654601673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89869317181367046436401115 134803975772050569654601673)
    ·
      refine ⟨101102981829037927240951255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134803975772050569654601673 101102981829037927240951255)
      ·
        refine ⟨151654472743556890861426883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101102981829037927240951255 151654472743556890861426883)
        ·
          refine ⟨227481709115335336292140325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151654472743556890861426883 227481709115335336292140325)
          ·
            refine ⟨42652820459125375554776311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227481709115335336292140325 42652820459125375554776311)
            ·
              refine ⟨63979230688688063332164467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42652820459125375554776311 63979230688688063332164467)
              ·
                refine ⟨95968846033032094998246701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63979230688688063332164467 95968846033032094998246701)
                ·
                  refine ⟨35988317262387035624342513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95968846033032094998246701 35988317262387035624342513)
                  ·
                    refine ⟨26991237946790276718256885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35988317262387035624342513 26991237946790276718256885)
                    ·
                      refine ⟨2530428557511588442336583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26991237946790276718256885 2530428557511588442336583)
                      ·
                        rfl

theorem cell23_4927992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_4927992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4927992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4927992 prefixEnd_4927992 := by exact prefixLift 4927992
  have htrace : WordTrace (prefixWord ++ tailWord_4927992) baseStart_4927992 baseEnd_4927992 := by
    simpa [prefixWord, tailWord_4927992, baseEnd_4927992] using wordTrace_append hprefix tailTrace_4927992
  have hstable : (prefixWord ++ tailWord_4927992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4927992).length < 2 ^ (prefixWord ++ tailWord_4927992).sum := by decide
  have hdescent : baseEnd_4927992 < baseStart_4927992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4927992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928013 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4928013 : Nat := 118140960795 + 4928013 * 2 ^ 59
def prefixEnd_4928013 : Nat := 4983230072969 + 3 ^ 40 * 4928013 * 2
def baseEnd_4928013 : Nat := 2530439340605332860173987

theorem tailTrace_4928013 : CollatzResearch.WordTrace tailWord_4928013 prefixEnd_4928013 2530439340605332860173987 := by
  unfold tailWord_4928013
  simp only [CollatzResearch.WordTrace]
  refine ⟨179739400295658013459316693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119826266863772008972877795 179739400295658013459316693)
  ·
    refine ⟨4212642194429484690452735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 179739400295658013459316693 4212642194429484690452735)
    ·
      refine ⟨6318963291644227035679103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212642194429484690452735 6318963291644227035679103)
      ·
        refine ⟨9478444937466340553518655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6318963291644227035679103 9478444937466340553518655)
        ·
          refine ⟨14217667406199510830277983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478444937466340553518655 14217667406199510830277983)
          ·
            refine ⟨21326501109299266245416975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14217667406199510830277983 21326501109299266245416975)
            ·
              refine ⟨31989751663948899368125463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21326501109299266245416975 31989751663948899368125463)
              ·
                refine ⟨47984627495923349052188195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31989751663948899368125463 47984627495923349052188195)
                ·
                  refine ⟨71976941243885023578282293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47984627495923349052188195 71976941243885023578282293)
                  ·
                    refine ⟨6747838241614220960463965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71976941243885023578282293 6747838241614220960463965)
                    ·
                      refine ⟨2530439340605332860173987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6747838241614220960463965 2530439340605332860173987)
                      ·
                        rfl

theorem cell23_4928013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4928013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928013 prefixEnd_4928013 := by exact prefixLift 4928013
  have htrace : WordTrace (prefixWord ++ tailWord_4928013) baseStart_4928013 baseEnd_4928013 := by
    simpa [prefixWord, tailWord_4928013, baseEnd_4928013] using wordTrace_append hprefix tailTrace_4928013
  have hstable : (prefixWord ++ tailWord_4928013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928013).length < 2 ^ (prefixWord ++ tailWord_4928013).sum := by decide
  have hdescent : baseEnd_4928013 < baseStart_4928013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928070 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_4928070 : Nat := 118140960795 + 4928070 * 2 ^ 59
def prefixEnd_4928070 : Nat := 4983230072969 + 3 ^ 40 * 4928070 * 2
def baseEnd_4928070 : Nat := 2530468609002639137161225

theorem tailTrace_4928070 : CollatzResearch.WordTrace tailWord_4928070 prefixEnd_4928070 2530468609002639137161225 := by
  unfold tailWord_4928070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616921226764109756066927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 119827652837634341462761109 5616921226764109756066927)
  ·
    refine ⟨8425381840146164634100391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5616921226764109756066927 8425381840146164634100391)
    ·
      refine ⟨12638072760219246951150587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8425381840146164634100391 12638072760219246951150587)
      ·
        refine ⟨18957109140328870426725881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12638072760219246951150587 18957109140328870426725881)
        ·
          refine ⟨14217831855246652820044411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18957109140328870426725881 14217831855246652820044411)
          ·
            refine ⟨21326747782869979230066617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14217831855246652820044411 21326747782869979230066617)
            ·
              refine ⟨15995060837152484422549963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21326747782869979230066617 15995060837152484422549963)
              ·
                refine ⟨23992591255728726633824945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15995060837152484422549963 23992591255728726633824945)
                ·
                  refine ⟨17994443441796544975368709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23992591255728726633824945 17994443441796544975368709)
                  ·
                    refine ⟨3373958145336852182881633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17994443441796544975368709 3373958145336852182881633)
                    ·
                      refine ⟨2530468609002639137161225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373958145336852182881633 2530468609002639137161225)
                      ·
                        rfl

theorem cell23_4928070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_4928070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928070 prefixEnd_4928070 := by exact prefixLift 4928070
  have htrace : WordTrace (prefixWord ++ tailWord_4928070) baseStart_4928070 baseEnd_4928070 := by
    simpa [prefixWord, tailWord_4928070, baseEnd_4928070] using wordTrace_append hprefix tailTrace_4928070
  have hstable : (prefixWord ++ tailWord_4928070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928070).length < 2 ^ (prefixWord ++ tailWord_4928070).sum := by decide
  have hdescent : baseEnd_4928070 < baseStart_4928070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928076 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 6]
def baseStart_4928076 : Nat := 118140960795 + 4928076 * 2 ^ 59
def prefixEnd_4928076 : Nat := 4983230072969 + 3 ^ 40 * 4928076 * 2
def baseEnd_4928076 : Nat := 281163521098507345965133

theorem tailTrace_4928076 : CollatzResearch.WordTrace tailWord_4928076 prefixEnd_4928076 281163521098507345965133 := by
  unfold tailWord_4928076
  simp only [CollatzResearch.WordTrace]
  refine ⟨89870849047214887609430041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119827798729619850145906721 89870849047214887609430041)
  ·
    refine ⟨67403136785411165707072531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89870849047214887609430041 67403136785411165707072531)
    ·
      refine ⟨101104705178116748560608797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67403136785411165707072531 101104705178116748560608797)
      ·
        refine ⟨37914264441793780710228299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101104705178116748560608797 37914264441793780710228299)
        ·
          refine ⟨56871396662690671065342449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37914264441793780710228299 56871396662690671065342449)
          ·
            refine ⟨42653547497018003299006837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56871396662690671065342449 42653547497018003299006837)
            ·
              refine ⟨3998770077845437809281891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42653547497018003299006837 3998770077845437809281891)
              ·
                refine ⟨5998155116768156713922837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998770077845437809281891 5998155116768156713922837)
                ·
                  refine ⟨281163521098507345965133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5998155116768156713922837 281163521098507345965133)
                  ·
                    rfl

theorem cell23_4928076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_4928076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928076 prefixEnd_4928076 := by exact prefixLift 4928076
  have htrace : WordTrace (prefixWord ++ tailWord_4928076) baseStart_4928076 baseEnd_4928076 := by
    simpa [prefixWord, tailWord_4928076, baseEnd_4928076] using wordTrace_append hprefix tailTrace_4928076
  have hstable : (prefixWord ++ tailWord_4928076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928076).length < 2 ^ (prefixWord ++ tailWord_4928076).sum := by decide
  have hdescent : baseEnd_4928076 < baseStart_4928076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928096 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 1, 5, 2]
def baseStart_4928096 : Nat := 118140960795 + 4928096 * 2 ^ 59
def prefixEnd_4928096 : Nat := 4983230072969 + 3 ^ 40 * 4928096 * 2
def baseEnd_4928096 : Nat := 2530481959499656035436105

theorem tailTrace_4928096 : CollatzResearch.WordTrace tailWord_4928096 prefixEnd_4928096 2530481959499656035436105 := by
  unfold tailWord_4928096
  simp only [CollatzResearch.WordTrace]
  refine ⟨89871213777178659317294071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119828285036238212423058761 89871213777178659317294071)
  ·
    refine ⟨134806820665767988975941107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89871213777178659317294071 134806820665767988975941107)
    ·
      refine ⟨202210230998651983463911661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134806820665767988975941107 202210230998651983463911661)
      ·
        refine ⟨75828836624494493798966873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202210230998651983463911661 75828836624494493798966873)
        ·
          refine ⟨56871627468370870349225155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75828836624494493798966873 56871627468370870349225155)
          ·
            refine ⟨85307441202556305523837733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56871627468370870349225155 85307441202556305523837733)
            ·
              refine ⟨15995145225479307285719575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85307441202556305523837733 15995145225479307285719575)
              ·
                refine ⟨23992717838218960928579363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15995145225479307285719575 23992717838218960928579363)
                ·
                  refine ⟨35989076757328441392869045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23992717838218960928579363 35989076757328441392869045)
                  ·
                    refine ⟨3373975945999541380581473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35989076757328441392869045 3373975945999541380581473)
                    ·
                      refine ⟨2530481959499656035436105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3373975945999541380581473 2530481959499656035436105)
                      ·
                        rfl

theorem cell23_4928096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_4928096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928096 prefixEnd_4928096 := by exact prefixLift 4928096
  have htrace : WordTrace (prefixWord ++ tailWord_4928096) baseStart_4928096 baseEnd_4928096 := by
    simpa [prefixWord, tailWord_4928096, baseEnd_4928096] using wordTrace_append hprefix tailTrace_4928096
  have hstable : (prefixWord ++ tailWord_4928096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928096).length < 2 ^ (prefixWord ++ tailWord_4928096).sum := by decide
  have hdescent : baseEnd_4928096 < baseStart_4928096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928106 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_4928106 : Nat := 118140960795 + 4928106 * 2 ^ 59
def prefixEnd_4928106 : Nat := 4983230072969 + 3 ^ 40 * 4928106 * 2
def baseEnd_4928106 : Nat := 843495698102066998770353

theorem tailTrace_4928106 : CollatzResearch.WordTrace tailWord_4928106 prefixEnd_4928106 843495698102066998770353 := by
  unfold tailWord_4928106
  simp only [CollatzResearch.WordTrace]
  refine ⟨44935698071080272585613043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119828528189547393561634781 44935698071080272585613043)
  ·
    refine ⟨67403547106620408878419565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44935698071080272585613043 67403547106620408878419565)
    ·
      refine ⟨25276330164982653329407337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67403547106620408878419565 25276330164982653329407337)
      ·
        refine ⟨18957247623736989997055503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25276330164982653329407337 18957247623736989997055503)
        ·
          refine ⟨28435871435605484995583255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18957247623736989997055503 28435871435605484995583255)
          ·
            refine ⟨42653807153408227493374883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28435871435605484995583255 42653807153408227493374883)
            ·
              refine ⟨63980710730112341240062325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42653807153408227493374883 63980710730112341240062325)
              ·
                refine ⟨5998191630948031991255843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63980710730112341240062325 5998191630948031991255843)
                ·
                  refine ⟨8997287446422047986883765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5998191630948031991255843 8997287446422047986883765)
                  ·
                    refine ⟨843495698102066998770353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8997287446422047986883765 843495698102066998770353)
                    ·
                      rfl

theorem cell23_4928106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_4928106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928106 prefixEnd_4928106 := by exact prefixLift 4928106
  have htrace : WordTrace (prefixWord ++ tailWord_4928106) baseStart_4928106 baseEnd_4928106 := by
    simpa [prefixWord, tailWord_4928106, baseEnd_4928106] using wordTrace_append hprefix tailTrace_4928106
  have hstable : (prefixWord ++ tailWord_4928106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928106).length < 2 ^ (prefixWord ++ tailWord_4928106).sum := by decide
  have hdescent : baseEnd_4928106 < baseStart_4928106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928156 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4928156 : Nat := 118140960795 + 4928156 * 2 ^ 59
def prefixEnd_4928156 : Nat := 4983230072969 + 3 ^ 40 * 4928156 * 2
def baseEnd_4928156 : Nat := 2530512768338925800685829

theorem tailTrace_4928156 : CollatzResearch.WordTrace tailWord_4928156 prefixEnd_4928156 2530512768338925800685829 := by
  unfold tailWord_4928156
  simp only [CollatzResearch.WordTrace]
  refine ⟨89872307967069974440886161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119829743956093299254514881 89872307967069974440886161)
  ·
    refine ⟨67404230975302480830664621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89872307967069974440886161 67404230975302480830664621)
    ·
      refine ⟨25276586615738430311499233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67404230975302480830664621 25276586615738430311499233)
      ·
        refine ⟨18957439961803822733624425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25276586615738430311499233 18957439961803822733624425)
        ·
          refine ⟨14218079971352867050218319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18957439961803822733624425 14218079971352867050218319)
          ·
            refine ⟨21327119957029300575327479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14218079971352867050218319 21327119957029300575327479)
            ·
              refine ⟨31990679935543950862991219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21327119957029300575327479 31990679935543950862991219)
              ·
                refine ⟨47986019903315926294486829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31990679935543950862991219 47986019903315926294486829)
                ·
                  refine ⟨17994757463743472360432561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47986019903315926294486829 17994757463743472360432561)
                  ·
                    refine ⟨13496068097807604270324421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17994757463743472360432561 13496068097807604270324421)
                    ·
                      refine ⟨2530512768338925800685829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13496068097807604270324421 2530512768338925800685829)
                      ·
                        rfl

theorem cell23_4928156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4928156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928156 prefixEnd_4928156 := by exact prefixLift 4928156
  have htrace : WordTrace (prefixWord ++ tailWord_4928156) baseStart_4928156 baseEnd_4928156 := by
    simpa [prefixWord, tailWord_4928156, baseEnd_4928156] using wordTrace_append hprefix tailTrace_4928156
  have hstable : (prefixWord ++ tailWord_4928156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928156).length < 2 ^ (prefixWord ++ tailWord_4928156).sum := by decide
  have hdescent : baseEnd_4928156 < baseStart_4928156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928160 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 1, 1, 4]
def baseStart_4928160 : Nat := 118140960795 + 4928160 * 2 ^ 59
def prefixEnd_4928160 : Nat := 4983230072969 + 3 ^ 40 * 4928160 * 2
def baseEnd_4928160 : Nat := 2530514822261543785035811

theorem tailTrace_4928160 : CollatzResearch.WordTrace tailWord_4928160 prefixEnd_4928160 2530514822261543785035811 := by
  unfold tailWord_4928160
  simp only [CollatzResearch.WordTrace]
  refine ⟨89872380913062728782458967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119829841217416971709945289 89872380913062728782458967)
  ·
    refine ⟨134808571369594093173688451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89872380913062728782458967 134808571369594093173688451)
    ·
      refine ⟨202212857054391139760532677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134808571369594093173688451 202212857054391139760532677)
      ·
        refine ⟨37914910697698338705099877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202212857054391139760532677 37914910697698338705099877)
        ·
          refine ⟨7109045755818438507206227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37914910697698338705099877 7109045755818438507206227)
          ·
            refine ⟨10663568633727657760809341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109045755818438507206227 10663568633727657760809341)
            ·
              refine ⟨3998838237647871660303503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10663568633727657760809341 3998838237647871660303503)
              ·
                refine ⟨5998257356471807490455255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998838237647871660303503 5998257356471807490455255)
                ·
                  refine ⟨8997386034707711235682883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5998257356471807490455255 8997386034707711235682883)
                  ·
                    refine ⟨13496079052061566853524325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8997386034707711235682883 13496079052061566853524325)
                    ·
                      refine ⟨2530514822261543785035811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13496079052061566853524325 2530514822261543785035811)
                      ·
                        rfl

theorem cell23_4928160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_4928160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928160 prefixEnd_4928160 := by exact prefixLift 4928160
  have htrace : WordTrace (prefixWord ++ tailWord_4928160) baseStart_4928160 baseEnd_4928160 := by
    simpa [prefixWord, tailWord_4928160, baseEnd_4928160] using wordTrace_append hprefix tailTrace_4928160
  have hstable : (prefixWord ++ tailWord_4928160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928160).length < 2 ^ (prefixWord ++ tailWord_4928160).sum := by decide
  have hdescent : baseEnd_4928160 < baseStart_4928160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928179 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 2, 7]
def baseStart_4928179 : Nat := 118140960795 + 4928179 * 2 ^ 59
def prefixEnd_4928179 : Nat := 4983230072969 + 3 ^ 40 * 4928179 * 2
def baseEnd_4928179 : Nat := 843508192797993070232741

theorem tailTrace_4928179 : CollatzResearch.WordTrace tailWord_4928179 prefixEnd_4928179 843508192797993070232741 := by
  unfold tailWord_4928179
  simp only [CollatzResearch.WordTrace]
  refine ⟨179745454813056623809859591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119830303208704415873239727 179745454813056623809859591)
  ·
    refine ⟨269618182219584935714789387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179745454813056623809859591 269618182219584935714789387)
    ·
      refine ⟨404427273329377403572184081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269618182219584935714789387 404427273329377403572184081)
      ·
        refine ⟨303320454997033052679138061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404427273329377403572184081 303320454997033052679138061)
        ·
          refine ⟨113745170623887394754676773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303320454997033052679138061 113745170623887394754676773)
          ·
            refine ⟨21327219491978886516501895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113745170623887394754676773 21327219491978886516501895)
            ·
              refine ⟨31990829237968329774752843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21327219491978886516501895 31990829237968329774752843)
              ·
                refine ⟨47986243856952494662129265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31990829237968329774752843 47986243856952494662129265)
                ·
                  refine ⟨35989682892714370996596949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47986243856952494662129265 35989682892714370996596949)
                  ·
                    refine ⟨843508192797993070232741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35989682892714370996596949 843508192797993070232741)
                    ·
                      rfl

theorem cell23_4928179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 7].length) (baseStart_4928179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928179 prefixEnd_4928179 := by exact prefixLift 4928179
  have htrace : WordTrace (prefixWord ++ tailWord_4928179) baseStart_4928179 baseEnd_4928179 := by
    simpa [prefixWord, tailWord_4928179, baseEnd_4928179] using wordTrace_append hprefix tailTrace_4928179
  have hstable : (prefixWord ++ tailWord_4928179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928179).length < 2 ^ (prefixWord ++ tailWord_4928179).sum := by decide
  have hdescent : baseEnd_4928179 < baseStart_4928179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928183 : List Nat := [1, 1, 3, 1, 7, 1, 1, 8]
def baseStart_4928183 : Nat := 118140960795 + 4928183 * 2 ^ 59
def prefixEnd_4928183 : Nat := 4983230072969 + 3 ^ 40 * 4928183 * 2
def baseEnd_4928183 : Nat := 93723208604318414631415

theorem tailTrace_4928183 : CollatzResearch.WordTrace tailWord_4928183 prefixEnd_4928183 93723208604318414631415 := by
  unfold tailWord_4928183
  simp only [CollatzResearch.WordTrace]
  refine ⟨179745600705042132493005203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119830400470028088328670135 179745600705042132493005203)
  ·
    refine ⟨269618401057563198739507805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179745600705042132493005203 269618401057563198739507805)
    ·
      refine ⟨101106900396586199527315427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269618401057563198739507805 101106900396586199527315427)
      ·
        refine ⟨151660350594879299290973141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101106900396586199527315427 151660350594879299290973141)
        ·
          refine ⟨3554539467067483577132183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 151660350594879299290973141 3554539467067483577132183)
          ·
            refine ⟨5331809200601225365698275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554539467067483577132183 5331809200601225365698275)
            ·
              refine ⟨7997713800901838048547413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331809200601225365698275 7997713800901838048547413)
              ·
                refine ⟨93723208604318414631415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7997713800901838048547413 93723208604318414631415)
                ·
                  rfl

theorem cell23_4928183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 8].length) (baseStart_4928183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928183 prefixEnd_4928183 := by exact prefixLift 4928183
  have htrace : WordTrace (prefixWord ++ tailWord_4928183) baseStart_4928183 baseEnd_4928183 := by
    simpa [prefixWord, tailWord_4928183, baseEnd_4928183] using wordTrace_append hprefix tailTrace_4928183
  have hstable : (prefixWord ++ tailWord_4928183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928183).length < 2 ^ (prefixWord ++ tailWord_4928183).sum := by decide
  have hdescent : baseEnd_4928183 < baseStart_4928183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928209 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 1, 8]
def baseStart_4928209 : Nat := 118140960795 + 4928209 * 2 ^ 59
def prefixEnd_4928209 : Nat := 4983230072969 + 3 ^ 40 * 4928209 * 2
def baseEnd_4928209 : Nat := 843513327604538031107695

theorem tailTrace_4928209 : CollatzResearch.WordTrace tailWord_4928209 prefixEnd_4928209 843513327604538031107695 := by
  unfold tailWord_4928209
  simp only [CollatzResearch.WordTrace]
  refine ⟨179746549002947938933451681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119831032668631959288967787 179746549002947938933451681)
  ·
    refine ⟨134809911752210954200088761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179746549002947938933451681 134809911752210954200088761)
    ·
      refine ⟨101107433814158215650066571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134809911752210954200088761 101107433814158215650066571)
      ·
        refine ⟨151661150721237323475099857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101107433814158215650066571 151661150721237323475099857)
        ·
          refine ⟨113745863040927992606324893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151661150721237323475099857 113745863040927992606324893)
          ·
            refine ⟨42654698640347997227371835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113745863040927992606324893 42654698640347997227371835)
            ·
              refine ⟨63982047960521995841057753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42654698640347997227371835 63982047960521995841057753)
              ·
                refine ⟨47986535970391496880793315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63982047960521995841057753 47986535970391496880793315)
                ·
                  refine ⟨71979803955587245321189973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47986535970391496880793315 71979803955587245321189973)
                  ·
                    refine ⟨843513327604538031107695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71979803955587245321189973 843513327604538031107695)
                    ·
                      rfl

theorem cell23_4928209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_4928209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928209 prefixEnd_4928209 := by exact prefixLift 4928209
  have htrace : WordTrace (prefixWord ++ tailWord_4928209) baseStart_4928209 baseEnd_4928209 := by
    simpa [prefixWord, tailWord_4928209, baseEnd_4928209] using wordTrace_append hprefix tailTrace_4928209
  have hstable : (prefixWord ++ tailWord_4928209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928209).length < 2 ^ (prefixWord ++ tailWord_4928209).sum := by decide
  have hdescent : baseEnd_4928209 < baseStart_4928209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928227 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4928227 : Nat := 118140960795 + 4928227 * 2 ^ 59
def prefixEnd_4928227 : Nat := 4983230072969 + 3 ^ 40 * 4928227 * 2
def baseEnd_4928227 : Nat := 2530549225465395022898003

theorem tailTrace_4928227 : CollatzResearch.WordTrace tailWord_4928227 prefixEnd_4928227 2530549225465395022898003 := by
  unfold tailWord_4928227
  simp only [CollatzResearch.WordTrace]
  refine ⟨179747205516882728007606935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119831470344588485338404623 179747205516882728007606935)
  ·
    refine ⟨269620808275324092011410403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179747205516882728007606935 269620808275324092011410403)
    ·
      refine ⟨404431212412986138017115605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269620808275324092011410403 404431212412986138017115605)
      ·
        refine ⟨9478856540929362609776147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 404431212412986138017115605 9478856540929362609776147)
        ·
          refine ⟨14218284811394043914664221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478856540929362609776147 14218284811394043914664221)
          ·
            refine ⟨5331856804272766467999083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14218284811394043914664221 5331856804272766467999083)
            ·
              refine ⟨7997785206409149701998625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331856804272766467999083 7997785206409149701998625)
              ·
                refine ⟨5998338904806862276498969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7997785206409149701998625 5998338904806862276498969)
                ·
                  refine ⟨4498754178605146707374227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5998338904806862276498969 4498754178605146707374227)
                  ·
                    refine ⟨6748131267907720061061341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4498754178605146707374227 6748131267907720061061341)
                    ·
                      refine ⟨2530549225465395022898003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6748131267907720061061341 2530549225465395022898003)
                      ·
                        rfl

theorem cell23_4928227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4928227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928227 prefixEnd_4928227 := by exact prefixLift 4928227
  have htrace : WordTrace (prefixWord ++ tailWord_4928227) baseStart_4928227 baseEnd_4928227 := by
    simpa [prefixWord, tailWord_4928227, baseEnd_4928227] using wordTrace_append hprefix tailTrace_4928227
  have hstable : (prefixWord ++ tailWord_4928227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928227).length < 2 ^ (prefixWord ++ tailWord_4928227).sum := by decide
  have hdescent : baseEnd_4928227 < baseStart_4928227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928244 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4928244 : Nat := 118140960795 + 4928244 * 2 ^ 59
def prefixEnd_4928244 : Nat := 4983230072969 + 3 ^ 40 * 4928244 * 2
def baseEnd_4928244 : Nat := 2530557954636521456385425

theorem tailTrace_4928244 : CollatzResearch.WordTrace tailWord_4928244 prefixEnd_4928244 2530557954636521456385425 := by
  unfold tailWord_4928244
  simp only [CollatzResearch.WordTrace]
  refine ⟨89873912778910569955487893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119831883705214093273983857 89873912778910569955487893)
  ·
    refine ⟨4212839661511432966663495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89873912778910569955487893 4212839661511432966663495)
    ·
      refine ⟨6319259492267149449995243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212839661511432966663495 6319259492267149449995243)
      ·
        refine ⟨9478889238400724174992865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319259492267149449995243 9478889238400724174992865)
        ·
          refine ⟨7109166928800543131244649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9478889238400724174992865 7109166928800543131244649)
          ·
            refine ⟨5331875196600407348433487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7109166928800543131244649 5331875196600407348433487)
            ·
              refine ⟨7997812794900611022650231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331875196600407348433487 7997812794900611022650231)
              ·
                refine ⟨11996719192350916533975347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7997812794900611022650231 11996719192350916533975347)
                ·
                  refine ⟨17995078788526374800963021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11996719192350916533975347 17995078788526374800963021)
                  ·
                    refine ⟨6748154545697390550361133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17995078788526374800963021 6748154545697390550361133)
                    ·
                      refine ⟨2530557954636521456385425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6748154545697390550361133 2530557954636521456385425)
                      ·
                        rfl

theorem cell23_4928244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4928244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928244 prefixEnd_4928244 := by exact prefixLift 4928244
  have htrace : WordTrace (prefixWord ++ tailWord_4928244) baseStart_4928244 baseEnd_4928244 := by
    simpa [prefixWord, tailWord_4928244, baseEnd_4928244] using wordTrace_append hprefix tailTrace_4928244
  have hstable : (prefixWord ++ tailWord_4928244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928244).length < 2 ^ (prefixWord ++ tailWord_4928244).sum := by decide
  have hdescent : baseEnd_4928244 < baseStart_4928244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928249 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_4928249 : Nat := 118140960795 + 4928249 * 2 ^ 59
def prefixEnd_4928249 : Nat := 4983230072969 + 3 ^ 40 * 4928249 * 2
def baseEnd_4928249 : Nat := 2530560522039793936822901

theorem tailTrace_4928249 : CollatzResearch.WordTrace tailWord_4928249 prefixEnd_4928249 2530560522039793936822901 := by
  unfold tailWord_4928249
  simp only [CollatzResearch.WordTrace]
  refine ⟨179748007922803025764907801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119832005281868683843271867 179748007922803025764907801)
  ·
    refine ⟨134811005942102269323680851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179748007922803025764907801 134811005942102269323680851)
    ·
      refine ⟨202216508913153403985521277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134811005942102269323680851 202216508913153403985521277)
      ·
        refine ⟨75831190842432526494570479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202216508913153403985521277 75831190842432526494570479)
        ·
          refine ⟨113746786263648789741855719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75831190842432526494570479 113746786263648789741855719)
          ·
            refine ⟨170620179395473184612783579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113746786263648789741855719 170620179395473184612783579)
            ·
              refine ⟨255930269093209776919175369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170620179395473184612783579 255930269093209776919175369)
              ·
                refine ⟨191947701819907332689381527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255930269093209776919175369 191947701819907332689381527)
                ·
                  refine ⟨287921552729860999034072291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191947701819907332689381527 287921552729860999034072291)
                  ·
                    refine ⟨431882329094791498551108437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287921552729860999034072291 431882329094791498551108437)
                    ·
                      refine ⟨2530560522039793936822901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 431882329094791498551108437 2530560522039793936822901)
                      ·
                        rfl

theorem cell23_4928249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_4928249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928249 prefixEnd_4928249 := by exact prefixLift 4928249
  have htrace : WordTrace (prefixWord ++ tailWord_4928249) baseStart_4928249 baseEnd_4928249 := by
    simpa [prefixWord, tailWord_4928249, baseEnd_4928249] using wordTrace_append hprefix tailTrace_4928249
  have hstable : (prefixWord ++ tailWord_4928249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928249).length < 2 ^ (prefixWord ++ tailWord_4928249).sum := by decide
  have hdescent : baseEnd_4928249 < baseStart_4928249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928250 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2]
def baseStart_4928250 : Nat := 118140960795 + 4928250 * 2 ^ 59
def prefixEnd_4928250 : Nat := 4983230072969 + 3 ^ 40 * 4928250 * 2
def baseEnd_4928250 : Nat := 2530561035520448432910397

theorem tailTrace_4928250 : CollatzResearch.WordTrace tailWord_4928250 prefixEnd_4928250 2530561035520448432910397 := by
  unfold tailWord_4928250
  simp only [CollatzResearch.WordTrace]
  refine ⟨44937011098949850733923551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119832029597199601957129469 44937011098949850733923551)
  ·
    refine ⟨67405516648424776100885327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44937011098949850733923551 67405516648424776100885327)
    ·
      refine ⟨101108274972637164151327991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67405516648424776100885327 101108274972637164151327991)
      ·
        refine ⟨151662412458955746226991987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101108274972637164151327991 151662412458955746226991987)
        ·
          refine ⟨227493618688433619340487981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151662412458955746226991987 227493618688433619340487981)
          ·
            refine ⟨85310107008162607252682993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227493618688433619340487981 85310107008162607252682993)
            ·
              refine ⟨63982580256121955439512245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85310107008162607252682993 63982580256121955439512245)
              ·
                refine ⟨5998366899011433322454273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63982580256121955439512245 5998366899011433322454273)
                ·
                  refine ⟨4498775174258574991840705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5998366899011433322454273 4498775174258574991840705)
                  ·
                    refine ⟨3374081380693931243880529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4498775174258574991840705 3374081380693931243880529)
                    ·
                      refine ⟨2530561035520448432910397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374081380693931243880529 2530561035520448432910397)
                      ·
                        rfl

theorem cell23_4928250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_4928250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928250 prefixEnd_4928250 := by exact prefixLift 4928250
  have htrace : WordTrace (prefixWord ++ tailWord_4928250) baseStart_4928250 baseEnd_4928250 := by
    simpa [prefixWord, tailWord_4928250, baseEnd_4928250] using wordTrace_append hprefix tailTrace_4928250
  have hstable : (prefixWord ++ tailWord_4928250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928250).length < 2 ^ (prefixWord ++ tailWord_4928250).sum := by decide
  have hdescent : baseEnd_4928250 < baseStart_4928250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928273 : List Nat := [1, 2, 2, 1, 1, 3, 5, 3, 5]
def baseStart_4928273 : Nat := 118140960795 + 4928273 * 2 ^ 59
def prefixEnd_4928273 : Nat := 4983230072969 + 3 ^ 40 * 4928273 * 2
def baseEnd_4928273 : Nat := 281174760619500204769199

theorem tailTrace_4928273 : CollatzResearch.WordTrace tailWord_4928273 prefixEnd_4928273 281174760619500204769199 := by
  unfold tailWord_4928273
  simp only [CollatzResearch.WordTrace]
  refine ⟨179748883274716077863781473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119832588849810718575854315 179748883274716077863781473)
  ·
    refine ⟨134811662456037058397836105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179748883274716077863781473 134811662456037058397836105)
    ·
      refine ⟨101108746842027793798377079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134811662456037058397836105 101108746842027793798377079)
      ·
        refine ⟨151663120263041690697565619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101108746842027793798377079 151663120263041690697565619)
        ·
          refine ⟨227494680394562536046348429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151663120263041690697565619 227494680394562536046348429)
          ·
            refine ⟨85310505147960951017380661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227494680394562536046348429 85310505147960951017380661)
            ·
              refine ⟨7997859857621339157879437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85310505147960951017380661 7997859857621339157879437)
              ·
                refine ⟨2999197446608002184204789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7997859857621339157879437 2999197446608002184204789)
                ·
                  refine ⟨281174760619500204769199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2999197446608002184204789 281174760619500204769199)
                  ·
                    rfl

theorem cell23_4928273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 5].length) (baseStart_4928273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928273 prefixEnd_4928273 := by exact prefixLift 4928273
  have htrace : WordTrace (prefixWord ++ tailWord_4928273) baseStart_4928273 baseEnd_4928273 := by
    simpa [prefixWord, tailWord_4928273, baseEnd_4928273] using wordTrace_append hprefix tailTrace_4928273
  have hstable : (prefixWord ++ tailWord_4928273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928273).length < 2 ^ (prefixWord ++ tailWord_4928273).sum := by decide
  have hdescent : baseEnd_4928273 < baseStart_4928273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928293 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 2, 5, 2]
def baseStart_4928293 : Nat := 118140960795 + 4928293 * 2 ^ 59
def prefixEnd_4928293 : Nat := 4983230072969 + 3 ^ 40 * 4928293 * 2
def baseEnd_4928293 : Nat := 2530583115188591764672699

theorem tailTrace_4928293 : CollatzResearch.WordTrace tailWord_4928293 prefixEnd_4928293 2530583115188591764672699 := by
  unfold tailWord_4928293
  simp only [CollatzResearch.WordTrace]
  refine ⟨179749612734643621279509533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119833075156429080853006355 179749612734643621279509533)
  ·
    refine ⟨67406104775491357979816075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179749612734643621279509533 67406104775491357979816075)
    ·
      refine ⟨101109157163237036969724113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67406104775491357979816075 101109157163237036969724113)
      ·
        refine ⟨75831867872427777727293085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101109157163237036969724113 75831867872427777727293085)
        ·
          refine ⟨28436950452160416647734907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75831867872427777727293085 28436950452160416647734907)
          ·
            refine ⟨42655425678240624971602361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28436950452160416647734907 42655425678240624971602361)
            ·
              refine ⟨31991569258680468728701771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42655425678240624971602361 31991569258680468728701771)
              ·
                refine ⟨47987353888020703093052657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31991569258680468728701771 47987353888020703093052657)
                ·
                  refine ⟨35990515416015527319789493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47987353888020703093052657 35990515416015527319789493)
                  ·
                    refine ⟨3374110820251455686230265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35990515416015527319789493 3374110820251455686230265)
                    ·
                      refine ⟨2530583115188591764672699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374110820251455686230265 2530583115188591764672699)
                      ·
                        rfl

theorem cell23_4928293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_4928293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928293 prefixEnd_4928293 := by exact prefixLift 4928293
  have htrace : WordTrace (prefixWord ++ tailWord_4928293) baseStart_4928293 baseEnd_4928293 := by
    simpa [prefixWord, tailWord_4928293, baseEnd_4928293] using wordTrace_append hprefix tailTrace_4928293
  have hstable : (prefixWord ++ tailWord_4928293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928293).length < 2 ^ (prefixWord ++ tailWord_4928293).sum := by decide
  have hdescent : baseEnd_4928293 < baseStart_4928293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928301 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4928301 : Nat := 118140960795 + 4928301 * 2 ^ 59
def prefixEnd_4928301 : Nat := 4983230072969 + 3 ^ 40 * 4928301 * 2
def baseEnd_4928301 : Nat := 2530587223033827733372663

theorem tailTrace_4928301 : CollatzResearch.WordTrace tailWord_4928301 prefixEnd_4928301 2530587223033827733372663 := by
  unfold tailWord_4928301
  simp only [CollatzResearch.WordTrace]
  refine ⟨179749904518614638645800757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119833269679076425763867171 179749904518614638645800757)
  ·
    refine ⟨16851553548620122373043821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179749904518614638645800757 16851553548620122373043821)
    ·
      refine ⟨6319332580732545889891433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16851553548620122373043821 6319332580732545889891433)
      ·
        refine ⟨4739499435549409417418575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6319332580732545889891433 4739499435549409417418575)
        ·
          refine ⟨7109249153324114126127863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4739499435549409417418575 7109249153324114126127863)
          ·
            refine ⟨10663873729986171189191795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109249153324114126127863 10663873729986171189191795)
            ·
              refine ⟨15995810594979256783787693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10663873729986171189191795 15995810594979256783787693)
              ·
                refine ⟨5998428973117221293920385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15995810594979256783787693 5998428973117221293920385)
                ·
                  refine ⟨4498821729837915970440289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5998428973117221293920385 4498821729837915970440289)
                  ·
                    refine ⟨3374116297378436977830217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4498821729837915970440289 3374116297378436977830217)
                    ·
                      refine ⟨2530587223033827733372663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374116297378436977830217 2530587223033827733372663)
                      ·
                        rfl

theorem cell23_4928301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4928301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928301 prefixEnd_4928301 := by exact prefixLift 4928301
  have htrace : WordTrace (prefixWord ++ tailWord_4928301) baseStart_4928301 baseEnd_4928301 := by
    simpa [prefixWord, tailWord_4928301, baseEnd_4928301] using wordTrace_append hprefix tailTrace_4928301
  have hstable : (prefixWord ++ tailWord_4928301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928301).length < 2 ^ (prefixWord ++ tailWord_4928301).sum := by decide
  have hdescent : baseEnd_4928301 < baseStart_4928301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928323 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 4]
def baseStart_4928323 : Nat := 118140960795 + 4928323 * 2 ^ 59
def prefixEnd_4928323 : Nat := 4983230072969 + 3 ^ 40 * 4928323 * 2
def baseEnd_4928323 : Nat := 2530598519608226647297561

theorem tailTrace_4928323 : CollatzResearch.WordTrace tailWord_4928323 prefixEnd_4928323 2530598519608226647297561 := by
  unfold tailWord_4928323
  simp only [CollatzResearch.WordTrace]
  refine ⟨179750706924534936403101623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119833804616356624268734415 179750706924534936403101623)
  ·
    refine ⟨269626060386802404604652435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179750706924534936403101623 269626060386802404604652435)
    ·
      refine ⟨404439090580203606906978653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269626060386802404604652435 404439090580203606906978653)
      ·
        refine ⟨151664658967576352590116995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404439090580203606906978653 151664658967576352590116995)
        ·
          refine ⟨227496988451364528885175493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151664658967576352590116995 227496988451364528885175493)
          ·
            refine ⟨42655685334630849165970405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227496988451364528885175493 42655685334630849165970405)
            ·
              refine ⟨7997941000243284218619451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42655685334630849165970405 7997941000243284218619451)
              ·
                refine ⟨11996911500364926327929177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7997941000243284218619451 11996911500364926327929177)
                ·
                  refine ⟨8997683625273694745946883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11996911500364926327929177 8997683625273694745946883)
                  ·
                    refine ⟨13496525437910542118920325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8997683625273694745946883 13496525437910542118920325)
                    ·
                      refine ⟨2530598519608226647297561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13496525437910542118920325 2530598519608226647297561)
                      ·
                        rfl

theorem cell23_4928323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_4928323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928323 prefixEnd_4928323 := by exact prefixLift 4928323
  have htrace : WordTrace (prefixWord ++ tailWord_4928323) baseStart_4928323 baseEnd_4928323 := by
    simpa [prefixWord, tailWord_4928323, baseEnd_4928323] using wordTrace_append hprefix tailTrace_4928323
  have hstable : (prefixWord ++ tailWord_4928323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928323).length < 2 ^ (prefixWord ++ tailWord_4928323).sum := by decide
  have hdescent : baseEnd_4928323 < baseStart_4928323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928407 : List Nat := [1, 1, 3, 3, 1, 2, 1, 6, 1, 1, 3]
def baseStart_4928407 : Nat := 118140960795 + 4928407 * 2 ^ 59
def prefixEnd_4928407 : Nat := 4983230072969 + 3 ^ 40 * 4928407 * 2
def baseEnd_4928407 : Nat := 2530641651983204318647175

theorem tailTrace_4928407 : CollatzResearch.WordTrace tailWord_4928407 prefixEnd_4928407 2530641651983204318647175 := by
  unfold tailWord_4928407
  simp only [CollatzResearch.WordTrace]
  refine ⟨179753770656230618749159475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119835847104153745832772983 179753770656230618749159475)
  ·
    refine ⟨269630655984345928123739213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179753770656230618749159475 269630655984345928123739213)
    ·
      refine ⟨101111495994129723046402205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269630655984345928123739213 101111495994129723046402205)
      ·
        refine ⟨37916810997798646142400827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101111495994129723046402205 37916810997798646142400827)
        ·
          refine ⟨56875216496697969213601241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37916810997798646142400827 56875216496697969213601241)
          ·
            refine ⟨42656412372523476910200931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56875216496697969213601241 42656412372523476910200931)
            ·
              refine ⟨63984618558785215365301397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42656412372523476910200931 63984618558785215365301397)
              ·
                refine ⟨2999278994943056970248503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63984618558785215365301397 2999278994943056970248503)
                ·
                  refine ⟨4498918492414585455372755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999278994943056970248503 4498918492414585455372755)
                  ·
                    refine ⟨6748377738621878183059133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4498918492414585455372755 6748377738621878183059133)
                    ·
                      refine ⟨2530641651983204318647175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6748377738621878183059133 2530641651983204318647175)
                      ·
                        rfl

theorem cell23_4928407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_4928407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928407 prefixEnd_4928407 := by exact prefixLift 4928407
  have htrace : WordTrace (prefixWord ++ tailWord_4928407) baseStart_4928407 baseEnd_4928407 := by
    simpa [prefixWord, tailWord_4928407, baseEnd_4928407] using wordTrace_append hprefix tailTrace_4928407
  have hstable : (prefixWord ++ tailWord_4928407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928407).length < 2 ^ (prefixWord ++ tailWord_4928407).sum := by decide
  have hdescent : baseEnd_4928407 < baseStart_4928407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928470 : List Nat := [5, 2, 1, 1, 2, 1, 1, 10]
def baseStart_4928470 : Nat := 118140960795 + 4928470 * 2 ^ 59
def prefixEnd_4928470 : Nat := 4983230072969 + 3 ^ 40 * 4928470 * 2
def baseEnd_4928470 : Nat := 93728666713497687857755

theorem tailTrace_4928470 : CollatzResearch.WordTrace tailWord_4928470 prefixEnd_4928470 93728666713497687857755 := by
  unfold tailWord_4928470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11234754278437648781793929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119837378970001587005801909 11234754278437648781793929)
  ·
    refine ⟨8426065708828236586345447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11234754278437648781793929 8426065708828236586345447)
    ·
      refine ⟨12639098563242354879518171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8426065708828236586345447 12639098563242354879518171)
      ·
        refine ⟨18958647844863532319277257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12639098563242354879518171 18958647844863532319277257)
        ·
          refine ⟨14218985883647649239457943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18958647844863532319277257 14218985883647649239457943)
          ·
            refine ⟨21328478825471473859186915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14218985883647649239457943 21328478825471473859186915)
            ·
              refine ⟨31992718238207210788780373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21328478825471473859186915 31992718238207210788780373)
              ·
                refine ⟨93728666713497687857755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31992718238207210788780373 93728666713497687857755)
                ·
                  rfl

theorem cell23_4928470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_4928470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928470 prefixEnd_4928470 := by exact prefixLift 4928470
  have htrace : WordTrace (prefixWord ++ tailWord_4928470) baseStart_4928470 baseEnd_4928470 := by
    simpa [prefixWord, tailWord_4928470, baseEnd_4928470] using wordTrace_append hprefix tailTrace_4928470
  have hstable : (prefixWord ++ tailWord_4928470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928470).length < 2 ^ (prefixWord ++ tailWord_4928470).sum := by decide
  have hdescent : baseEnd_4928470 < baseStart_4928470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928474 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_4928474 : Nat := 118140960795 + 4928474 * 2 ^ 59
def prefixEnd_4928474 : Nat := 4983230072969 + 3 ^ 40 * 4928474 * 2
def baseEnd_4928474 : Nat := 843558685062351852169789

theorem tailTrace_4928474 : CollatzResearch.WordTrace tailWord_4928474 prefixEnd_4928474 843558685062351852169789 := by
  unfold tailWord_4928474
  simp only [CollatzResearch.WordTrace]
  refine ⟨44939053586746972297962119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119837476231325259461232317 44939053586746972297962119)
  ·
    refine ⟨67408580380120458446943179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44939053586746972297962119 67408580380120458446943179)
    ·
      refine ⟨101112870570180687670414769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67408580380120458446943179 101112870570180687670414769)
      ·
        refine ⟨75834652927635515752811077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101112870570180687670414769 75834652927635515752811077)
        ·
          refine ⟨14218997423931659203652077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75834652927635515752811077 14218997423931659203652077)
          ·
            refine ⟨5332124033974372201369529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14218997423931659203652077 5332124033974372201369529)
            ·
              refine ⟨3999093025480779151027147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5332124033974372201369529 3999093025480779151027147)
              ·
                refine ⟨5998639538221168726540721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999093025480779151027147 5998639538221168726540721)
                ·
                  refine ⟨4498979653665876544905541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5998639538221168726540721 4498979653665876544905541)
                  ·
                    refine ⟨843558685062351852169789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4498979653665876544905541 843558685062351852169789)
                    ·
                      rfl

theorem cell23_4928474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_4928474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928474 prefixEnd_4928474 := by exact prefixLift 4928474
  have htrace : WordTrace (prefixWord ++ tailWord_4928474) baseStart_4928474 baseEnd_4928474 := by
    simpa [prefixWord, tailWord_4928474, baseEnd_4928474] using wordTrace_append hprefix tailTrace_4928474
  have hstable : (prefixWord ++ tailWord_4928474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928474).length < 2 ^ (prefixWord ++ tailWord_4928474).sum := by decide
  have hdescent : baseEnd_4928474 < baseStart_4928474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928501 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4928501 : Nat := 118140960795 + 4928501 * 2 ^ 59
def prefixEnd_4928501 : Nat := 4983230072969 + 3 ^ 40 * 4928501 * 2
def baseEnd_4928501 : Nat := 2530689919164726950871743

theorem tailTrace_4928501 : CollatzResearch.WordTrace tailWord_4928501 prefixEnd_4928501 2530689919164726950871743 := by
  unfold tailWord_4928501
  simp only [CollatzResearch.WordTrace]
  refine ⟨179757199117890072803081357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119838132745260048535387571 179757199117890072803081357)
  ·
    refine ⟨67408949669208777301155509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179757199117890072803081357 67408949669208777301155509)
    ·
      refine ⟨6319589031488322871983329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67408949669208777301155509 6319589031488322871983329)
      ·
        refine ⟨4739691773616242153987497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6319589031488322871983329 4739691773616242153987497)
        ·
          refine ⟨3554768830212181615490623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4739691773616242153987497 3554768830212181615490623)
          ·
            refine ⟨5332153245318272423235935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554768830212181615490623 5332153245318272423235935)
            ·
              refine ⟨7998229867977408634853903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5332153245318272423235935 7998229867977408634853903)
              ·
                refine ⟨11997344801966112952280855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7998229867977408634853903 11997344801966112952280855)
                ·
                  refine ⟨17996017202949169428421283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11997344801966112952280855 17996017202949169428421283)
                  ·
                    refine ⟨26994025804423754142631925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17996017202949169428421283 26994025804423754142631925)
                    ·
                      refine ⟨2530689919164726950871743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26994025804423754142631925 2530689919164726950871743)
                      ·
                        rfl

theorem cell23_4928501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4928501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928501 prefixEnd_4928501 := by exact prefixLift 4928501
  have htrace : WordTrace (prefixWord ++ tailWord_4928501) baseStart_4928501 baseEnd_4928501 := by
    simpa [prefixWord, tailWord_4928501, baseEnd_4928501] using wordTrace_append hprefix tailTrace_4928501
  have hstable : (prefixWord ++ tailWord_4928501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928501).length < 2 ^ (prefixWord ++ tailWord_4928501).sum := by decide
  have hdescent : baseEnd_4928501 < baseStart_4928501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928543 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 9]
def baseStart_4928543 : Nat := 118140960795 + 4928543 * 2 ^ 59
def prefixEnd_4928543 : Nat := 4983230072969 + 3 ^ 40 * 4928543 * 2
def baseEnd_4928543 : Nat := 281190165039135087394061

theorem tailTrace_4928543 : CollatzResearch.WordTrace tailWord_4928543 prefixEnd_4928543 281190165039135087394061 := by
  unfold tailWord_4928543
  simp only [CollatzResearch.WordTrace]
  refine ⟨179758730983737913976110283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119839153989158609317406855 179758730983737913976110283)
  ·
    refine ⟨269638096475606870964165425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179758730983737913976110283 269638096475606870964165425)
    ·
      refine ⟨202228572356705153223124069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269638096475606870964165425 202228572356705153223124069)
      ·
        refine ⟨37917857316882216229335763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202228572356705153223124069 37917857316882216229335763)
        ·
          refine ⟨56876785975323324344003645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37917857316882216229335763 56876785975323324344003645)
          ·
            refine ⟨21328794740746246629001367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56876785975323324344003645 21328794740746246629001367)
            ·
              refine ⟨31993192111119369943502051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21328794740746246629001367 31993192111119369943502051)
              ·
                refine ⟨47989788166679054915253077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31993192111119369943502051 47989788166679054915253077)
                ·
                  refine ⟨281190165039135087394061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47989788166679054915253077 281190165039135087394061)
                  ·
                    rfl

theorem cell23_4928543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 9].length) (baseStart_4928543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928543 prefixEnd_4928543 := by exact prefixLift 4928543
  have htrace : WordTrace (prefixWord ++ tailWord_4928543) baseStart_4928543 baseEnd_4928543 := by
    simpa [prefixWord, tailWord_4928543, baseEnd_4928543] using wordTrace_append hprefix tailTrace_4928543
  have hstable : (prefixWord ++ tailWord_4928543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928543).length < 2 ^ (prefixWord ++ tailWord_4928543).sum := by decide
  have hdescent : baseEnd_4928543 < baseStart_4928543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928570 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_4928570 : Nat := 118140960795 + 4928570 * 2 ^ 59
def prefixEnd_4928570 : Nat := 4983230072969 + 3 ^ 40 * 4928570 * 2
def baseEnd_4928570 : Nat := 2530725349329887180908925

theorem tailTrace_4928570 : CollatzResearch.WordTrace tailWord_4928570 prefixEnd_4928570 2530725349329887180908925 := by
  unfold tailWord_4928570
  simp only [CollatzResearch.WordTrace]
  refine ⟨44939928938660024396835791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119839810503093398391562109 44939928938660024396835791)
  ·
    refine ⟨67409893407990036595253687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44939928938660024396835791 67409893407990036595253687)
    ·
      refine ⟨101114840111985054892880531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67409893407990036595253687 101114840111985054892880531)
      ·
        refine ⟨151672260167977582339320797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101114840111985054892880531 151672260167977582339320797)
        ·
          refine ⟨56877097562991593377245299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151672260167977582339320797 56877097562991593377245299)
          ·
            refine ⟨85315646344487390065867949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56877097562991593377245299 85315646344487390065867949)
            ·
              refine ⟨31993367379182771274700481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85315646344487390065867949 31993367379182771274700481)
              ·
                refine ⟨23995025534387078456025361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31993367379182771274700481 23995025534387078456025361)
                ·
                  refine ⟨17996269150790308842019021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23995025534387078456025361 17996269150790308842019021)
                  ·
                    refine ⟨6748600931546365815757133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17996269150790308842019021 6748600931546365815757133)
                    ·
                      refine ⟨2530725349329887180908925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6748600931546365815757133 2530725349329887180908925)
                      ·
                        rfl

theorem cell23_4928570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_4928570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928570 prefixEnd_4928570 := by exact prefixLift 4928570
  have htrace : WordTrace (prefixWord ++ tailWord_4928570) baseStart_4928570 baseEnd_4928570 := by
    simpa [prefixWord, tailWord_4928570, baseEnd_4928570] using wordTrace_append hprefix tailTrace_4928570
  have hstable : (prefixWord ++ tailWord_4928570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928570).length < 2 ^ (prefixWord ++ tailWord_4928570).sum := by decide
  have hdescent : baseEnd_4928570 < baseStart_4928570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928577 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 7]
def baseStart_4928577 : Nat := 118140960795 + 4928577 * 2 ^ 59
def prefixEnd_4928577 : Nat := 4983230072969 + 3 ^ 40 * 4928577 * 2
def baseEnd_4928577 : Nat := 281192104854940961502377

theorem tailTrace_4928577 : CollatzResearch.WordTrace tailWord_4928577 prefixEnd_4928577 281192104854940961502377 := by
  unfold tailWord_4928577
  simp only [CollatzResearch.WordTrace]
  refine ⟨179759971065614737782847985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119839980710409825188565323 179759971065614737782847985)
  ·
    refine ⟨134819978299211053337135989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179759971065614737782847985 134819978299211053337135989)
    ·
      refine ⟨12639372965551036250356499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134819978299211053337135989 12639372965551036250356499)
      ·
        refine ⟨18959059448326554375534749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12639372965551036250356499 18959059448326554375534749)
        ·
          refine ⟨7109647293122457890825531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18959059448326554375534749 7109647293122457890825531)
          ·
            refine ⟨10664470939683686836238297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109647293122457890825531 10664470939683686836238297)
            ·
              refine ⟨7998353204762765127178723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10664470939683686836238297 7998353204762765127178723)
              ·
                refine ⟨11997529807144147690768085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7998353204762765127178723 11997529807144147690768085)
                ·
                  refine ⟨281192104854940961502377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11997529807144147690768085 281192104854940961502377)
                  ·
                    rfl

theorem cell23_4928577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 7].length) (baseStart_4928577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928577 prefixEnd_4928577 := by exact prefixLift 4928577
  have htrace : WordTrace (prefixWord ++ tailWord_4928577) baseStart_4928577 baseEnd_4928577 := by
    simpa [prefixWord, tailWord_4928577, baseEnd_4928577] using wordTrace_append hprefix tailTrace_4928577
  have hstable : (prefixWord ++ tailWord_4928577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928577).length < 2 ^ (prefixWord ++ tailWord_4928577).sum := by decide
  have hdescent : baseEnd_4928577 < baseStart_4928577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928664 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4928664 : Nat := 118140960795 + 4928664 * 2 ^ 59
def prefixEnd_4928664 : Nat := 4983230072969 + 3 ^ 40 * 4928664 * 2
def baseEnd_4928664 : Nat := 2530773616511409813133493

theorem tailTrace_4928664 : CollatzResearch.WordTrace tailWord_4928664 prefixEnd_4928664 2530773616511409813133493 := by
  unfold tailWord_4928664
  simp only [CollatzResearch.WordTrace]
  refine ⟨89881572108149775820632523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119842096144199701094176697 89881572108149775820632523)
  ·
    refine ⟨134822358162224663730948785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89881572108149775820632523 134822358162224663730948785)
    ·
      refine ⟨101116768621668497798211589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134822358162224663730948785 101116768621668497798211589)
      ·
        refine ⟨18959394116562843337164673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101116768621668497798211589 18959394116562843337164673)
        ·
          refine ⟨14219545587422132502873505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18959394116562843337164673 14219545587422132502873505)
          ·
            refine ⟨10664659190566599377155129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14219545587422132502873505 10664659190566599377155129)
            ·
              refine ⟨7998494392924949532866347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10664659190566599377155129 7998494392924949532866347)
              ·
                refine ⟨11997741589387424299299521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7998494392924949532866347 11997741589387424299299521)
                ·
                  refine ⟨8998306192040568224474641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11997741589387424299299521 8998306192040568224474641)
                  ·
                    refine ⟨6748729644030426168355981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8998306192040568224474641 6748729644030426168355981)
                    ·
                      refine ⟨2530773616511409813133493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6748729644030426168355981 2530773616511409813133493)
                      ·
                        rfl

theorem cell23_4928664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4928664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928664 prefixEnd_4928664 := by exact prefixLift 4928664
  have htrace : WordTrace (prefixWord ++ tailWord_4928664) baseStart_4928664 baseEnd_4928664 := by
    simpa [prefixWord, tailWord_4928664, baseEnd_4928664] using wordTrace_append hprefix tailTrace_4928664
  have hstable : (prefixWord ++ tailWord_4928664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928664).length < 2 ^ (prefixWord ++ tailWord_4928664).sum := by decide
  have hdescent : baseEnd_4928664 < baseStart_4928664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928728 : List Nat := [2, 1, 2, 2, 5, 1, 2, 3, 1, 1, 3]
def baseStart_4928728 : Nat := 118140960795 + 4928728 * 2 ^ 59
def prefixEnd_4928728 : Nat := 4983230072969 + 3 ^ 40 * 4928728 * 2
def baseEnd_4928728 : Nat := 2530806479273297562733199

theorem tailTrace_4928728 : CollatzResearch.WordTrace tailWord_4928728 prefixEnd_4928728 2530806479273297562733199 := by
  unfold tailWord_4928728
  simp only [CollatzResearch.WordTrace]
  refine ⟨89882739244033845285797419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119843652325378460381063225 89882739244033845285797419)
  ·
    refine ⟨134824108866050767928696129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89882739244033845285797419 134824108866050767928696129)
    ·
      refine ⟨101118081649538075946522097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134824108866050767928696129 101118081649538075946522097)
      ·
        refine ⟨75838561237153556959891573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101118081649538075946522097 75838561237153556959891573)
        ·
          refine ⟨7109865115983145964989835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75838561237153556959891573 7109865115983145964989835)
          ·
            refine ⟨10664797673974718947484753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109865115983145964989835 10664797673974718947484753)
            ·
              refine ⟨7998598255481039210613565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10664797673974718947484753 7998598255481039210613565)
              ·
                refine ⟨2999474345805389703980087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7998598255481039210613565 2999474345805389703980087)
                ·
                  refine ⟨4499211518708084555970131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999474345805389703980087 4499211518708084555970131)
                  ·
                    refine ⟨6748817278062126833955197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4499211518708084555970131 6748817278062126833955197)
                    ·
                      refine ⟨2530806479273297562733199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6748817278062126833955197 2530806479273297562733199)
                      ·
                        rfl

theorem cell23_4928728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_4928728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928728 prefixEnd_4928728 := by exact prefixLift 4928728
  have htrace : WordTrace (prefixWord ++ tailWord_4928728) baseStart_4928728 baseEnd_4928728 := by
    simpa [prefixWord, tailWord_4928728, baseEnd_4928728] using wordTrace_append hprefix tailTrace_4928728
  have hstable : (prefixWord ++ tailWord_4928728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928728).length < 2 ^ (prefixWord ++ tailWord_4928728).sum := by decide
  have hdescent : baseEnd_4928728 < baseStart_4928728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928730 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_4928730 : Nat := 118140960795 + 4928730 * 2 ^ 59
def prefixEnd_4928730 : Nat := 4983230072969 + 3 ^ 40 * 4928730 * 2
def baseEnd_4928730 : Nat := 2530807506234606554908189

theorem tailTrace_4928730 : CollatzResearch.WordTrace tailWord_4928730 prefixEnd_4928730 2530807506234606554908189 := by
  unfold tailWord_4928730
  simp only [CollatzResearch.WordTrace]
  refine ⟨44941387858515111228291911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119843700956040296608778429 44941387858515111228291911)
  ·
    refine ⟨67412081787772666842437867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44941387858515111228291911 67412081787772666842437867)
    ·
      refine ⟨101118122681659000263656801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67412081787772666842437867 101118122681659000263656801)
      ·
        refine ⟨75838592011244250197742601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101118122681659000263656801 75838592011244250197742601)
        ·
          refine ⟨56878944008433187648306951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75838592011244250197742601 56878944008433187648306951)
          ·
            refine ⟨85318416012649781472460427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56878944008433187648306951 85318416012649781472460427)
            ·
              refine ⟨127977624018974672208690641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85318416012649781472460427 127977624018974672208690641)
              ·
                refine ⟨95983218014231004156517981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127977624018974672208690641 95983218014231004156517981)
                ·
                  refine ⟨35993706755336626558694243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95983218014231004156517981 35993706755336626558694243)
                  ·
                    refine ⟨53990560133004939838041365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35993706755336626558694243 53990560133004939838041365)
                    ·
                      refine ⟨2530807506234606554908189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53990560133004939838041365 2530807506234606554908189)
                      ·
                        rfl

theorem cell23_4928730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_4928730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928730 prefixEnd_4928730 := by exact prefixLift 4928730
  have htrace : WordTrace (prefixWord ++ tailWord_4928730) baseStart_4928730 baseEnd_4928730 := by
    simpa [prefixWord, tailWord_4928730, baseEnd_4928730] using wordTrace_append hprefix tailTrace_4928730
  have hstable : (prefixWord ++ tailWord_4928730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928730).length < 2 ^ (prefixWord ++ tailWord_4928730).sum := by decide
  have hdescent : baseEnd_4928730 < baseStart_4928730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928754 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_4928754 : Nat := 118140960795 + 4928754 * 2 ^ 59
def prefixEnd_4928754 : Nat := 4983230072969 + 3 ^ 40 * 4928754 * 2
def baseEnd_4928754 : Nat := 2530819829770314461008079

theorem tailTrace_4928754 : CollatzResearch.WordTrace tailWord_4928754 prefixEnd_4928754 2530819829770314461008079 := by
  unfold tailWord_4928754
  simp only [CollatzResearch.WordTrace]
  refine ⟨44941606696493374253010329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119844284523982331341360877 44941606696493374253010329)
  ·
    refine ⟨33706205022370030689757747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44941606696493374253010329 33706205022370030689757747)
    ·
      refine ⟨50559307533555046034636621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33706205022370030689757747 50559307533555046034636621)
      ·
        refine ⟨18959740325083142262988733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50559307533555046034636621 18959740325083142262988733)
        ·
          refine ⟨7109902621906178348620775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18959740325083142262988733 7109902621906178348620775)
          ·
            refine ⟨10664853932859267522931163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109902621906178348620775 10664853932859267522931163)
            ·
              refine ⟨15997280899288901284396745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10664853932859267522931163 15997280899288901284396745)
              ·
                refine ⟨11997960674466675963297559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15997280899288901284396745 11997960674466675963297559)
                ·
                  refine ⟨17996941011700013944946339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11997960674466675963297559 17996941011700013944946339)
                  ·
                    refine ⟨26995411517550020917419509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17996941011700013944946339 26995411517550020917419509)
                    ·
                      refine ⟨2530819829770314461008079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26995411517550020917419509 2530819829770314461008079)
                      ·
                        rfl

theorem cell23_4928754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_4928754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928754 prefixEnd_4928754 := by exact prefixLift 4928754
  have htrace : WordTrace (prefixWord ++ tailWord_4928754) baseStart_4928754 baseEnd_4928754 := by
    simpa [prefixWord, tailWord_4928754, baseEnd_4928754] using wordTrace_append hprefix tailTrace_4928754
  have hstable : (prefixWord ++ tailWord_4928754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928754).length < 2 ^ (prefixWord ++ tailWord_4928754).sum := by decide
  have hdescent : baseEnd_4928754 < baseStart_4928754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928802 : List Nat := [3, 3, 1, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_4928802 : Nat := 118140960795 + 4928802 * 2 ^ 59
def prefixEnd_4928802 : Nat := 4983230072969 + 3 ^ 40 * 4928802 * 2
def baseEnd_4928802 : Nat := 2530844476841730273207859

theorem tailTrace_4928802 : CollatzResearch.WordTrace tailWord_4928802 prefixEnd_4928802 2530844476841730273207859 := by
  unfold tailWord_4928802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44942044372449900302447165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119845451659866400806525773 44942044372449900302447165)
  ·
    refine ⟨16853266639668712613417687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44942044372449900302447165 16853266639668712613417687)
    ·
      refine ⟨25279899959503068920126531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16853266639668712613417687 25279899959503068920126531)
      ·
        refine ⟨37919849939254603380189797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25279899959503068920126531 37919849939254603380189797)
        ·
          refine ⟨7109971863610238133785587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37919849939254603380189797 7109971863610238133785587)
          ·
            refine ⟨10664957795415357200678381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109971863610238133785587 10664957795415357200678381)
            ·
              refine ⟨3999359173280758950254393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10664957795415357200678381 3999359173280758950254393)
              ·
                refine ⟨2999519379960569212690795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3999359173280758950254393 2999519379960569212690795)
                ·
                  refine ⟨4499279069940853819036193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999519379960569212690795 4499279069940853819036193)
                  ·
                    refine ⟨3374459302455640364277145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4499279069940853819036193 3374459302455640364277145)
                    ·
                      refine ⟨2530844476841730273207859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374459302455640364277145 2530844476841730273207859)
                      ·
                        rfl

theorem cell23_4928802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_4928802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928802 prefixEnd_4928802 := by exact prefixLift 4928802
  have htrace : WordTrace (prefixWord ++ tailWord_4928802) baseStart_4928802 baseEnd_4928802 := by
    simpa [prefixWord, tailWord_4928802, baseEnd_4928802] using wordTrace_append hprefix tailTrace_4928802
  have hstable : (prefixWord ++ tailWord_4928802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928802).length < 2 ^ (prefixWord ++ tailWord_4928802).sum := by decide
  have hdescent : baseEnd_4928802 < baseStart_4928802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928818 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_4928818 : Nat := 118140960795 + 4928818 * 2 ^ 59
def prefixEnd_4928818 : Nat := 4983230072969 + 3 ^ 40 * 4928818 * 2
def baseEnd_4928818 : Nat := 2530852692532202210607785

theorem tailTrace_4928818 : CollatzResearch.WordTrace tailWord_4928818 prefixEnd_4928818 2530852692532202210607785 := by
  unfold tailWord_4928818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44942190264435408985592777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119845840705161090628247405 44942190264435408985592777)
  ·
    refine ⟨33706642698326556739194583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44942190264435408985592777 33706642698326556739194583)
    ·
      refine ⟨50559964047489835108791875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33706642698326556739194583 50559964047489835108791875)
      ·
        refine ⟨75839946071234752663187813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50559964047489835108791875 75839946071234752663187813)
        ·
          refine ⟨14219989888356516124347715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75839946071234752663187813 14219989888356516124347715)
          ·
            refine ⟨21329984832534774186521573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14219989888356516124347715 21329984832534774186521573)
            ·
              refine ⟨3999372156100270159972795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21329984832534774186521573 3999372156100270159972795)
              ·
                refine ⟨5999058234150405239959193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999372156100270159972795 5999058234150405239959193)
                ·
                  refine ⟨4499293675612803929969395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5999058234150405239959193 4499293675612803929969395)
                  ·
                    refine ⟨6748940513419205894954093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4499293675612803929969395 6748940513419205894954093)
                    ·
                      refine ⟨2530852692532202210607785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6748940513419205894954093 2530852692532202210607785)
                      ·
                        rfl

theorem cell23_4928818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_4928818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928818 prefixEnd_4928818 := by exact prefixLift 4928818
  have htrace : WordTrace (prefixWord ++ tailWord_4928818) baseStart_4928818 baseEnd_4928818 := by
    simpa [prefixWord, tailWord_4928818, baseEnd_4928818] using wordTrace_append hprefix tailTrace_4928818
  have hstable : (prefixWord ++ tailWord_4928818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928818).length < 2 ^ (prefixWord ++ tailWord_4928818).sum := by decide
  have hdescent : baseEnd_4928818 < baseStart_4928818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928822 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4928822 : Nat := 118140960795 + 4928822 * 2 ^ 59
def prefixEnd_4928822 : Nat := 4983230072969 + 3 ^ 40 * 4928822 * 2
def baseEnd_4928822 : Nat := 2530854746454820194957767

theorem tailTrace_4928822 : CollatzResearch.WordTrace tailWord_4928822 prefixEnd_4928822 2530854746454820194957767 := by
  unfold tailWord_4928822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235556684357946539094795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119845937966484763083677813 11235556684357946539094795)
  ·
    refine ⟨16853335026536919808642193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11235556684357946539094795 16853335026536919808642193)
    ·
      refine ⟨12640001269902689856481645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16853335026536919808642193 12640001269902689856481645)
      ·
        refine ⟨4740000476213508696180617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12640001269902689856481645 4740000476213508696180617)
        ·
          refine ⟨3555000357160131522135463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4740000476213508696180617 3555000357160131522135463)
          ·
            refine ⟨5332500535740197283203195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3555000357160131522135463 5332500535740197283203195)
            ·
              refine ⟨7998750803610295924804793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5332500535740197283203195 7998750803610295924804793)
              ·
                refine ⟨5999063102707721943603595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7998750803610295924804793 5999063102707721943603595)
                ·
                  refine ⟨8998594654061582915405393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999063102707721943603595 8998594654061582915405393)
                  ·
                    refine ⟨6748945990546187186554045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8998594654061582915405393 6748945990546187186554045)
                    ·
                      refine ⟨2530854746454820194957767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6748945990546187186554045 2530854746454820194957767)
                      ·
                        rfl

theorem cell23_4928822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4928822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928822 prefixEnd_4928822 := by exact prefixLift 4928822
  have htrace : WordTrace (prefixWord ++ tailWord_4928822) baseStart_4928822 baseEnd_4928822 := by
    simpa [prefixWord, tailWord_4928822, baseEnd_4928822] using wordTrace_append hprefix tailTrace_4928822
  have hstable : (prefixWord ++ tailWord_4928822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928822).length < 2 ^ (prefixWord ++ tailWord_4928822).sum := by decide
  have hdescent : baseEnd_4928822 < baseStart_4928822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928824 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 1, 4, 2]
def baseStart_4928824 : Nat := 118140960795 + 4928824 * 2 ^ 59
def prefixEnd_4928824 : Nat := 4983230072969 + 3 ^ 40 * 4928824 * 2
def baseEnd_4928824 : Nat := 2530855773416129187132757

theorem tailTrace_4928824 : CollatzResearch.WordTrace tailWord_4928824 prefixEnd_4928824 2530855773416129187132757 := by
  unfold tailWord_4928824
  simp only [CollatzResearch.WordTrace]
  refine ⟨89884489947859949483544763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119845986597146599311393017 89884489947859949483544763)
  ·
    refine ⟨134826734921789924225317145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89884489947859949483544763 134826734921789924225317145)
    ·
      refine ⟨101120051191342443168987859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134826734921789924225317145 101120051191342443168987859)
      ·
        refine ⟨151680076787013664753481789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101120051191342443168987859 151680076787013664753481789)
        ·
          refine ⟨56880028795130124282555671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151680076787013664753481789 56880028795130124282555671)
          ·
            refine ⟨85320043192695186423833507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56880028795130124282555671 85320043192695186423833507)
            ·
              refine ⟨127980064789042779635750261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85320043192695186423833507 127980064789042779635750261)
              ·
                refine ⟨11998131073972760590851587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127980064789042779635750261 11998131073972760590851587)
                ·
                  refine ⟨17997196610959140886277381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11998131073972760590851587 17997196610959140886277381)
                  ·
                    refine ⟨3374474364554838916177009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17997196610959140886277381 3374474364554838916177009)
                    ·
                      refine ⟨2530855773416129187132757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374474364554838916177009 2530855773416129187132757)
                      ·
                        rfl

theorem cell23_4928824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_4928824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928824 prefixEnd_4928824 := by exact prefixLift 4928824
  have htrace : WordTrace (prefixWord ++ tailWord_4928824) baseStart_4928824 baseEnd_4928824 := by
    simpa [prefixWord, tailWord_4928824, baseEnd_4928824] using wordTrace_append hprefix tailTrace_4928824
  have hstable : (prefixWord ++ tailWord_4928824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928824).length < 2 ^ (prefixWord ++ tailWord_4928824).sum := by decide
  have hdescent : baseEnd_4928824 < baseStart_4928824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928828 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_4928828 : Nat := 118140960795 + 4928828 * 2 ^ 59
def prefixEnd_4928828 : Nat := 4983230072969 + 3 ^ 40 * 4928828 * 2
def baseEnd_4928828 : Nat := 2530857827338747171482739

theorem tailTrace_4928828 : CollatzResearch.WordTrace tailWord_4928828 prefixEnd_4928828 2530857827338747171482739 := by
  unfold tailWord_4928828
  simp only [CollatzResearch.WordTrace]
  refine ⟨89884562893852703825117569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119846083858470271766823425 89884562893852703825117569)
  ·
    refine ⟨67413422170389527868838177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89884562893852703825117569 67413422170389527868838177)
    ·
      refine ⟨50560066627792145901628633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67413422170389527868838177 50560066627792145901628633)
      ·
        refine ⟨37920049970844109426221475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50560066627792145901628633 37920049970844109426221475)
        ·
          refine ⟨56880074956266164139332213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37920049970844109426221475 56880074956266164139332213)
          ·
            refine ⟨5332507027149952888062395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56880074956266164139332213 5332507027149952888062395)
            ·
              refine ⟨7998760540724929332093593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5332507027149952888062395 7998760540724929332093593)
              ·
                refine ⟨5999070405543696999070195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7998760540724929332093593 5999070405543696999070195)
                ·
                  refine ⟨8998605608315545498605293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999070405543696999070195 8998605608315545498605293)
                  ·
                    refine ⟨3374477103118329561976985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8998605608315545498605293 3374477103118329561976985)
                    ·
                      refine ⟨2530857827338747171482739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374477103118329561976985 2530857827338747171482739)
                      ·
                        rfl

theorem cell23_4928828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_4928828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928828 prefixEnd_4928828 := by exact prefixLift 4928828
  have htrace : WordTrace (prefixWord ++ tailWord_4928828) baseStart_4928828 baseEnd_4928828 := by
    simpa [prefixWord, tailWord_4928828, baseEnd_4928828] using wordTrace_append hprefix tailTrace_4928828
  have hstable : (prefixWord ++ tailWord_4928828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928828).length < 2 ^ (prefixWord ++ tailWord_4928828).sum := by decide
  have hdescent : baseEnd_4928828 < baseStart_4928828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928898 : List Nat := [3, 4, 2, 1, 1, 1, 1, 5, 5]
def baseStart_4928898 : Nat := 118140960795 + 4928898 * 2 ^ 59
def prefixEnd_4928898 : Nat := 4983230072969 + 3 ^ 40 * 4928898 * 2
def baseEnd_4928898 : Nat := 281210418998284655289713

theorem tailTrace_4928898 : CollatzResearch.WordTrace tailWord_4928898 prefixEnd_4928898 281210418998284655289713 := by
  unfold tailWord_4928898
  simp only [CollatzResearch.WordTrace]
  refine ⟨44942919724362952401320837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119847785931634539736855565 44942919724362952401320837)
  ·
    refine ⟨8426797448318053575247657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44942919724362952401320837 8426797448318053575247657)
    ·
      refine ⟨6320098086238540181435743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8426797448318053575247657 6320098086238540181435743)
      ·
        refine ⟨9480147129357810272153615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6320098086238540181435743 9480147129357810272153615)
        ·
          refine ⟨14220220694036715408230423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9480147129357810272153615 14220220694036715408230423)
          ·
            refine ⟨21330331041055073112345635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14220220694036715408230423 21330331041055073112345635)
            ·
              refine ⟨31995496561582609668518453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21330331041055073112345635 31995496561582609668518453)
              ·
                refine ⟨2999577802648369656423605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31995496561582609668518453 2999577802648369656423605)
                ·
                  refine ⟨281210418998284655289713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2999577802648369656423605 281210418998284655289713)
                  ·
                    rfl

theorem cell23_4928898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_4928898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928898 prefixEnd_4928898 := by exact prefixLift 4928898
  have htrace : WordTrace (prefixWord ++ tailWord_4928898) baseStart_4928898 baseEnd_4928898 := by
    simpa [prefixWord, tailWord_4928898, baseEnd_4928898] using wordTrace_append hprefix tailTrace_4928898
  have hstable : (prefixWord ++ tailWord_4928898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928898).length < 2 ^ (prefixWord ++ tailWord_4928898).sum := by decide
  have hdescent : baseEnd_4928898 < baseStart_4928898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928917 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_4928917 : Nat := 118140960795 + 4928917 * 2 ^ 59
def prefixEnd_4928917 : Nat := 4983230072969 + 3 ^ 40 * 4928917 * 2
def baseEnd_4928917 : Nat := 2530903527116997323269829

theorem tailTrace_4928917 : CollatzResearch.WordTrace tailWord_4928917 prefixEnd_4928917 2530903527116997323269829 := by
  unfold tailWord_4928917
  simp only [CollatzResearch.WordTrace]
  refine ⟨179772371884382975850225005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119848247922921983900150003 179772371884382975850225005)
  ·
    refine ⟨67414639456643615943834377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179772371884382975850225005 67414639456643615943834377)
    ·
      refine ⟨50560979592482711957875783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67414639456643615943834377 50560979592482711957875783)
      ·
        refine ⟨75841469388724067936813675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50560979592482711957875783 75841469388724067936813675)
        ·
          refine ⟨113762204083086101905220513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75841469388724067936813675 113762204083086101905220513)
          ·
            refine ⟨85321653062314576428915385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113762204083086101905220513 85321653062314576428915385)
            ·
              refine ⟨63991239796735932321686539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85321653062314576428915385 63991239796735932321686539)
              ·
                refine ⟨95986859695103898482529809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63991239796735932321686539 95986859695103898482529809)
                ·
                  refine ⟨71990144771327923861897357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95986859695103898482529809 71990144771327923861897357)
                  ·
                    refine ⟨26996304289247971448211509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71990144771327923861897357 26996304289247971448211509)
                    ·
                      refine ⟨2530903527116997323269829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26996304289247971448211509 2530903527116997323269829)
                      ·
                        rfl

theorem cell23_4928917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_4928917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928917 prefixEnd_4928917 := by exact prefixLift 4928917
  have htrace : WordTrace (prefixWord ++ tailWord_4928917) baseStart_4928917 baseEnd_4928917 := by
    simpa [prefixWord, tailWord_4928917, baseEnd_4928917] using wordTrace_append hprefix tailTrace_4928917
  have hstable : (prefixWord ++ tailWord_4928917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928917).length < 2 ^ (prefixWord ++ tailWord_4928917).sum := by decide
  have hdescent : baseEnd_4928917 < baseStart_4928917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928962 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4928962 : Nat := 118140960795 + 4928962 * 2 ^ 59
def prefixEnd_4928962 : Nat := 4983230072969 + 3 ^ 40 * 4928962 * 2
def baseEnd_4928962 : Nat := 843642211248816549069041

theorem tailTrace_4928962 : CollatzResearch.WordTrace tailWord_4928962 prefixEnd_4928962 843642211248816549069041 := by
  unfold tailWord_4928962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44943503292304987133903285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119849342112813299023742093 44943503292304987133903285)
  ·
    refine ⟨4213453433653592543803433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44943503292304987133903285 4213453433653592543803433)
    ·
      refine ⟨3160090075240194407852575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4213453433653592543803433 3160090075240194407852575)
      ·
        refine ⟨4740135112860291611778863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160090075240194407852575 4740135112860291611778863)
        ·
          refine ⟨7110202669290437417668295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740135112860291611778863 7110202669290437417668295)
          ·
            refine ⟨10665304003935656126502443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7110202669290437417668295 10665304003935656126502443)
            ·
              refine ⟨15997956005903484189753665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10665304003935656126502443 15997956005903484189753665)
              ·
                refine ⟨11998467004427613142315249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15997956005903484189753665 11998467004427613142315249)
                ·
                  refine ⟨8998850253320709856736437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11998467004427613142315249 8998850253320709856736437)
                  ·
                    refine ⟨843642211248816549069041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8998850253320709856736437 843642211248816549069041)
                    ·
                      rfl

theorem cell23_4928962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4928962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928962 prefixEnd_4928962 := by exact prefixLift 4928962
  have htrace : WordTrace (prefixWord ++ tailWord_4928962) baseStart_4928962 baseEnd_4928962 := by
    simpa [prefixWord, tailWord_4928962, baseEnd_4928962] using wordTrace_append hprefix tailTrace_4928962
  have hstable : (prefixWord ++ tailWord_4928962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928962).length < 2 ^ (prefixWord ++ tailWord_4928962).sum := by decide
  have hdescent : baseEnd_4928962 < baseStart_4928962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928977 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_4928977 : Nat := 118140960795 + 4928977 * 2 ^ 59
def prefixEnd_4928977 : Nat := 4983230072969 + 3 ^ 40 * 4928977 * 2
def baseEnd_4928977 : Nat := 2530934335956267088519553

theorem tailTrace_4928977 : CollatzResearch.WordTrace tailWord_4928977 prefixEnd_4928977 2530934335956267088519553 := by
  unfold tailWord_4928977
  simp only [CollatzResearch.WordTrace]
  refine ⟨179774560264165606097409185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119849706842777070731606123 179774560264165606097409185)
  ·
    refine ⟨134830920198124204573056889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179774560264165606097409185 134830920198124204573056889)
    ·
      refine ⟨101123190148593153429792667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134830920198124204573056889 101123190148593153429792667)
      ·
        refine ⟨151684785222889730144689001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101123190148593153429792667 151684785222889730144689001)
        ·
          refine ⟨113763588917167297608516751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151684785222889730144689001 113763588917167297608516751)
          ·
            refine ⟨170645383375750946412775127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113763588917167297608516751 170645383375750946412775127)
            ·
              refine ⟨255968075063626419619162691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170645383375750946412775127 255968075063626419619162691)
              ·
                refine ⟨383952112595439629428744037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255968075063626419619162691 383952112595439629428744037)
                ·
                  refine ⟨71991021111644930517889507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383952112595439629428744037 71991021111644930517889507)
                  ·
                    refine ⟨107986531667467395776834261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71991021111644930517889507 107986531667467395776834261)
                    ·
                      refine ⟨2530934335956267088519553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107986531667467395776834261 2530934335956267088519553)
                      ·
                        rfl

theorem cell23_4928977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_4928977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928977 prefixEnd_4928977 := by exact prefixLift 4928977
  have htrace : WordTrace (prefixWord ++ tailWord_4928977) baseStart_4928977 baseEnd_4928977 := by
    simpa [prefixWord, tailWord_4928977, baseEnd_4928977] using wordTrace_append hprefix tailTrace_4928977
  have hstable : (prefixWord ++ tailWord_4928977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928977).length < 2 ^ (prefixWord ++ tailWord_4928977).sum := by decide
  have hdescent : baseEnd_4928977 < baseStart_4928977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4928991 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 4, 3, 2]
def baseStart_4928991 : Nat := 118140960795 + 4928991 * 2 ^ 59
def prefixEnd_4928991 : Nat := 4983230072969 + 3 ^ 40 * 4928991 * 2
def baseEnd_4928991 : Nat := 2530941524685430033744489

theorem tailTrace_4928991 : CollatzResearch.WordTrace tailWord_4928991 prefixEnd_4928991 2530941524685430033744489 := by
  unfold tailWord_4928991
  simp only [CollatzResearch.WordTrace]
  refine ⟨179775070886114886488418827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119850047257409924325612551 179775070886114886488418827)
  ·
    refine ⟨269662606329172329732628241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179775070886114886488418827 269662606329172329732628241)
    ·
      refine ⟨202246954746879247299471181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269662606329172329732628241 202246954746879247299471181)
      ·
        refine ⟨75842608030079717737301693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202246954746879247299471181 75842608030079717737301693)
        ·
          refine ⟨28440978011279894151488135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75842608030079717737301693 28440978011279894151488135)
          ·
            refine ⟨42661467016919841227232203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28440978011279894151488135 42661467016919841227232203)
            ·
              refine ⟨63992200525379761840848305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42661467016919841227232203 63992200525379761840848305)
              ·
                refine ⟨47994150394034821380636229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63992200525379761840848305 47994150394034821380636229)
                ·
                  refine ⟨8998903198881529008869293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47994150394034821380636229 8998903198881529008869293)
                  ·
                    refine ⟨3374588699580573378325985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8998903198881529008869293 3374588699580573378325985)
                    ·
                      refine ⟨2530941524685430033744489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374588699580573378325985 2530941524685430033744489)
                      ·
                        rfl

theorem cell23_4928991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_4928991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4928991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4928991 prefixEnd_4928991 := by exact prefixLift 4928991
  have htrace : WordTrace (prefixWord ++ tailWord_4928991) baseStart_4928991 baseEnd_4928991 := by
    simpa [prefixWord, tailWord_4928991, baseEnd_4928991] using wordTrace_append hprefix tailTrace_4928991
  have hstable : (prefixWord ++ tailWord_4928991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4928991).length < 2 ^ (prefixWord ++ tailWord_4928991).sum := by decide
  have hdescent : baseEnd_4928991 < baseStart_4928991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4928991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929008 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 2, 3, 2]
def baseStart_4929008 : Nat := 118140960795 + 4929008 * 2 ^ 59
def prefixEnd_4929008 : Nat := 4983230072969 + 3 ^ 40 * 4929008 * 2
def baseEnd_4929008 : Nat := 2530950253856556467231911

theorem tailTrace_4929008 : CollatzResearch.WordTrace tailWord_4929008 prefixEnd_4929008 2530950253856556467231911 := by
  unfold tailWord_4929008
  simp only [CollatzResearch.WordTrace]
  refine ⟨89887845463526649195893839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119850460618035532261191785 89887845463526649195893839)
  ·
    refine ⟨134831768195289973793840759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89887845463526649195893839 134831768195289973793840759)
    ·
      refine ⟨202247652292934960690761139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134831768195289973793840759 202247652292934960690761139)
      ·
        refine ⟨303371478439402441036141709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202247652292934960690761139 303371478439402441036141709)
        ·
          refine ⟨113764304414775915388553141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303371478439402441036141709 113764304414775915388553141)
          ·
            refine ⟨10665403538885242067676857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113764304414775915388553141 10665403538885242067676857)
            ·
              refine ⟨7999052654163931550757643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10665403538885242067676857 7999052654163931550757643)
              ·
                refine ⟨11998578981245897326136465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7999052654163931550757643 11998578981245897326136465)
                ·
                  refine ⟨8998934235934422994602349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11998578981245897326136465 8998934235934422994602349)
                  ·
                    refine ⟨3374600338475408622975881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8998934235934422994602349 3374600338475408622975881)
                    ·
                      refine ⟨2530950253856556467231911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374600338475408622975881 2530950253856556467231911)
                      ·
                        rfl

theorem cell23_4929008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 3, 2].length) (baseStart_4929008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929008 prefixEnd_4929008 := by exact prefixLift 4929008
  have htrace : WordTrace (prefixWord ++ tailWord_4929008) baseStart_4929008 baseEnd_4929008 := by
    simpa [prefixWord, tailWord_4929008, baseEnd_4929008] using wordTrace_append hprefix tailTrace_4929008
  have hstable : (prefixWord ++ tailWord_4929008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929008).length < 2 ^ (prefixWord ++ tailWord_4929008).sum := by decide
  have hdescent : baseEnd_4929008 < baseStart_4929008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929075 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 1, 2, 3]
def baseStart_4929075 : Nat := 118140960795 + 4929075 * 2 ^ 59
def prefixEnd_4929075 : Nat := 4983230072969 + 3 ^ 40 * 4929075 * 2
def baseEnd_4929075 : Nat := 2530984657060407705094103

theorem tailTrace_4929075 : CollatzResearch.WordTrace tailWord_4929075 prefixEnd_4929075 2530984657060407705094103 := by
  unfold tailWord_4929075
  simp only [CollatzResearch.WordTrace]
  refine ⟨179778134617810568834476679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119852089745207045889651119 179778134617810568834476679)
  ·
    refine ⟨269667201926715853251715019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179778134617810568834476679 269667201926715853251715019)
    ·
      refine ⟨404500802890073779877572529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269667201926715853251715019 404500802890073779877572529)
      ·
        refine ⟨303375602167555334908179397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404500802890073779877572529 303375602167555334908179397)
        ·
          refine ⟨56882925406416625295283637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303375602167555334908179397 56882925406416625295283637)
          ·
            refine ⟨5332774256851558621432841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56882925406416625295283637 5332774256851558621432841)
            ·
              refine ⟨3999580692638668966074631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5332774256851558621432841 3999580692638668966074631)
              ·
                refine ⟨5999371038958003449111947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999580692638668966074631 5999371038958003449111947)
                ·
                  refine ⟨8999056558437005173667921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999371038958003449111947 8999056558437005173667921)
                  ·
                    refine ⟨6749292418827753880250941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8999056558437005173667921 6749292418827753880250941)
                    ·
                      refine ⟨2530984657060407705094103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6749292418827753880250941 2530984657060407705094103)
                      ·
                        rfl

theorem cell23_4929075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 2, 3].length) (baseStart_4929075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929075 prefixEnd_4929075 := by exact prefixLift 4929075
  have htrace : WordTrace (prefixWord ++ tailWord_4929075) baseStart_4929075 baseEnd_4929075 := by
    simpa [prefixWord, tailWord_4929075, baseEnd_4929075] using wordTrace_append hprefix tailTrace_4929075
  have hstable : (prefixWord ++ tailWord_4929075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929075).length < 2 ^ (prefixWord ++ tailWord_4929075).sum := by decide
  have hdescent : baseEnd_4929075 < baseStart_4929075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929104 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 2, 6]
def baseStart_4929104 : Nat := 118140960795 + 4929104 * 2 ^ 59
def prefixEnd_4929104 : Nat := 4983230072969 + 3 ^ 40 * 4929104 * 2
def baseEnd_4929104 : Nat := 843666515999796030543823

theorem tailTrace_4929104 : CollatzResearch.WordTrace tailWord_4929104 prefixEnd_4929104 843666515999796030543823 := by
  unfold tailWord_4929104
  simp only [CollatzResearch.WordTrace]
  refine ⟨89889596167352753393641183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119852794889803671191521577 89889596167352753393641183)
  ·
    refine ⟨134834394251029130090461775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89889596167352753393641183 134834394251029130090461775)
    ·
      refine ⟨202251591376543695135692663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134834394251029130090461775 202251591376543695135692663)
      ·
        refine ⟨303377387064815542703538995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202251591376543695135692663 303377387064815542703538995)
        ·
          refine ⟨455066080597223314055308493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303377387064815542703538995 455066080597223314055308493)
          ·
            refine ⟨170649780223958742770740685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455066080597223314055308493 170649780223958742770740685)
            ·
              refine ⟨63993667583984528539027757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170649780223958742770740685 63993667583984528539027757)
              ·
                refine ⟨23997625343994198202135409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63993667583984528539027757 23997625343994198202135409)
                ·
                  refine ⟨17998219007995648651601557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23997625343994198202135409 17998219007995648651601557)
                  ·
                    refine ⟨843666515999796030543823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17998219007995648651601557 843666515999796030543823)
                    ·
                      rfl

theorem cell23_4929104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_4929104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929104 prefixEnd_4929104 := by exact prefixLift 4929104
  have htrace : WordTrace (prefixWord ++ tailWord_4929104) baseStart_4929104 baseEnd_4929104 := by
    simpa [prefixWord, tailWord_4929104, baseEnd_4929104] using wordTrace_append hprefix tailTrace_4929104
  have hstable : (prefixWord ++ tailWord_4929104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929104).length < 2 ^ (prefixWord ++ tailWord_4929104).sum := by decide
  have hdescent : baseEnd_4929104 < baseStart_4929104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
