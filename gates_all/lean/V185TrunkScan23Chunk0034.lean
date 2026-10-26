import V185TrunkScan23Chunk0033

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_201633 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_201633 : Nat := 118140960795 + 201633 * 2 ^ 59
def prefixEnd_201633 : Nat := 4983230072969 + 3 ^ 40 * 201633 * 2
def baseEnd_201633 : Nat := 103534644808114843660213

theorem tailTrace_201633 : CollatzResearch.WordTrace tailWord_201633 prefixEnd_201633 103534644808114843660213 := by
  unfold tailWord_201633
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354159678525552019905553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4902773119017034679937035 7354159678525552019905553)
  ·
    refine ⟨5515619758894164014929165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7354159678525552019905553 5515619758894164014929165)
    ·
      refine ⟨2068357409585311505598437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5515619758894164014929165 2068357409585311505598437)
      ·
        refine ⟨387817014297245907299707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2068357409585311505598437 387817014297245907299707)
        ·
          refine ⟨581725521445868860949561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387817014297245907299707 581725521445868860949561)
          ·
            refine ⟨436294141084401645712171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581725521445868860949561 436294141084401645712171)
            ·
              refine ⟨654441211626602468568257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436294141084401645712171 654441211626602468568257)
              ·
                refine ⟨490830908719951851426193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654441211626602468568257 490830908719951851426193)
                ·
                  refine ⟨368123181539963888569645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490830908719951851426193 368123181539963888569645)
                  ·
                    refine ⟨138046193077486458213617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368123181539963888569645 138046193077486458213617)
                    ·
                      refine ⟨103534644808114843660213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138046193077486458213617 103534644808114843660213)
                      ·
                        rfl

theorem cell23_201633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_201633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201633 prefixEnd_201633 := by exact prefixLift 201633
  have htrace : WordTrace (prefixWord ++ tailWord_201633) baseStart_201633 baseEnd_201633 := by
    simpa [prefixWord, tailWord_201633, baseEnd_201633] using wordTrace_append hprefix tailTrace_201633
  have hstable : (prefixWord ++ tailWord_201633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201633).length < 2 ^ (prefixWord ++ tailWord_201633).sum := by decide
  have hdescent : baseEnd_201633 < baseStart_201633 := by decide
  rcases family_descends (prefixWord ++ tailWord_201633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201656 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 2, 4]
def baseStart_201656 : Nat := 118140960795 + 201656 * 2 ^ 59
def prefixEnd_201656 : Nat := 4983230072969 + 3 ^ 40 * 201656 * 2
def baseEnd_201656 : Nat := 34515484954389417890869

theorem tailTrace_201656 : CollatzResearch.WordTrace tailWord_201656 prefixEnd_201656 34515484954389417890869 := by
  unfold tailWord_201656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677499278721113473996411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4903332371628151298661881 3677499278721113473996411)
  ·
    refine ⟨5516248918081670210994617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3677499278721113473996411 5516248918081670210994617)
    ·
      refine ⟨4137186688561252658245963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5516248918081670210994617 4137186688561252658245963)
      ·
        refine ⟨6205780032841878987368945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137186688561252658245963 6205780032841878987368945)
        ·
          refine ⟨4654335024631409240526709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6205780032841878987368945 4654335024631409240526709)
          ·
            refine ⟨436343908559194616299379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4654335024631409240526709 436343908559194616299379)
            ·
              refine ⟨654515862838791924449069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436343908559194616299379 654515862838791924449069)
              ·
                refine ⟨245443448564546971668401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 654515862838791924449069 245443448564546971668401)
                ·
                  refine ⟨184082586423410228751301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245443448564546971668401 184082586423410228751301)
                  ·
                    refine ⟨34515484954389417890869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184082586423410228751301 34515484954389417890869)
                    ·
                      rfl

theorem cell23_201656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_201656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201656 prefixEnd_201656 := by exact prefixLift 201656
  have htrace : WordTrace (prefixWord ++ tailWord_201656) baseStart_201656 baseEnd_201656 := by
    simpa [prefixWord, tailWord_201656, baseEnd_201656] using wordTrace_append hprefix tailTrace_201656
  have hstable : (prefixWord ++ tailWord_201656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201656).length < 2 ^ (prefixWord ++ tailWord_201656).sum := by decide
  have hdescent : baseEnd_201656 < baseStart_201656 := by decide
  rcases family_descends (prefixWord ++ tailWord_201656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201679 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 3]
def baseStart_201679 : Nat := 118140960795 + 201679 * 2 ^ 59
def prefixEnd_201679 : Nat := 4983230072969 + 3 ^ 40 * 201679 * 2
def baseEnd_201679 : Nat := 103558264918221663685001

theorem tailTrace_201679 : CollatzResearch.WordTrace tailWord_201679 prefixEnd_201679 103558264918221663685001 := by
  unfold tailWord_201679
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355837436358901876080091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4903891624239267917386727 7355837436358901876080091)
  ·
    refine ⟨11033756154538352814120137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7355837436358901876080091 11033756154538352814120137)
    ·
      refine ⟨8275317115903764610590103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11033756154538352814120137 8275317115903764610590103)
      ·
        refine ⟨12412975673855646915885155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8275317115903764610590103 12412975673855646915885155)
        ·
          refine ⟨18619463510783470373827733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12412975673855646915885155 18619463510783470373827733)
          ·
            refine ⟨872787352067975173773175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18619463510783470373827733 872787352067975173773175)
            ·
              refine ⟨1309181028101962760659763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872787352067975173773175 1309181028101962760659763)
              ·
                refine ⟨1963771542152944140989645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309181028101962760659763 1963771542152944140989645)
                ·
                  refine ⟨736414328307354052871117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1963771542152944140989645 736414328307354052871117)
                  ·
                    refine ⟨276155373115257769826669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736414328307354052871117 276155373115257769826669)
                    ·
                      refine ⟨103558264918221663685001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 276155373115257769826669 103558264918221663685001)
                      ·
                        rfl

theorem cell23_201679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_201679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201679 prefixEnd_201679 := by exact prefixLift 201679
  have htrace : WordTrace (prefixWord ++ tailWord_201679) baseStart_201679 baseEnd_201679 := by
    simpa [prefixWord, tailWord_201679, baseEnd_201679] using wordTrace_append hprefix tailTrace_201679
  have hstable : (prefixWord ++ tailWord_201679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201679).length < 2 ^ (prefixWord ++ tailWord_201679).sum := by decide
  have hdescent : baseEnd_201679 < baseStart_201679 := by decide
  rcases family_descends (prefixWord ++ tailWord_201679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201713 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_201713 : Nat := 118140960795 + 201713 * 2 ^ 59
def prefixEnd_201713 : Nat := 4983230072969 + 3 ^ 40 * 201713 * 2
def baseEnd_201713 : Nat := 103575723260474530659845

theorem tailTrace_201713 : CollatzResearch.WordTrace tailWord_201713 prefixEnd_201713 103575723260474530659845 := by
  unfold tailWord_201713
  simp only [CollatzResearch.WordTrace]
  refine ⟨7357077518235725682817793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4904718345490483788545195 7357077518235725682817793)
  ·
    refine ⟨5517808138676794262113345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7357077518235725682817793 5517808138676794262113345)
    ·
      refine ⟨4138356104007595696585009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5517808138676794262113345 4138356104007595696585009)
      ·
        refine ⟨3103767078005696772438757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4138356104007595696585009 3103767078005696772438757)
        ·
          refine ⟨581956327126068144832267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3103767078005696772438757 581956327126068144832267)
          ·
            refine ⟨872934490689102217248401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581956327126068144832267 872934490689102217248401)
            ·
              refine ⟨654700868016826662936301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872934490689102217248401 654700868016826662936301)
              ·
                refine ⟨245512825506309998601113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 654700868016826662936301 245512825506309998601113)
                ·
                  refine ⟨184134619129732498950835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245512825506309998601113 184134619129732498950835)
                  ·
                    refine ⟨276201928694598748426253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 184134619129732498950835 276201928694598748426253)
                    ·
                      refine ⟨103575723260474530659845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 276201928694598748426253 103575723260474530659845)
                      ·
                        rfl

theorem cell23_201713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_201713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201713 prefixEnd_201713 := by exact prefixLift 201713
  have htrace : WordTrace (prefixWord ++ tailWord_201713) baseStart_201713 baseEnd_201713 := by
    simpa [prefixWord, tailWord_201713, baseEnd_201713] using wordTrace_append hprefix tailTrace_201713
  have hstable : (prefixWord ++ tailWord_201713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201713).length < 2 ^ (prefixWord ++ tailWord_201713).sum := by decide
  have hdescent : baseEnd_201713 < baseStart_201713 := by decide
  rcases family_descends (prefixWord ++ tailWord_201713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201740 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 1, 3, 2]
def baseStart_201740 : Nat := 118140960795 + 201740 * 2 ^ 59
def prefixEnd_201740 : Nat := 4983230072969 + 3 ^ 40 * 201740 * 2
def baseEnd_201740 : Nat := 103589587238145925022221

theorem tailTrace_201740 : CollatzResearch.WordTrace tailWord_201740 prefixEnd_201740 103589587238145925022221 := by
  unfold tailWord_201740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679031144568954647025337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4905374859425272862700449 3679031144568954647025337)
  ·
    refine ⟨2759273358426715985269003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3679031144568954647025337 2759273358426715985269003)
    ·
      refine ⟨4138910037640073977903505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759273358426715985269003 4138910037640073977903505)
      ·
        refine ⟨3104182528230055483427629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4138910037640073977903505 3104182528230055483427629)
        ·
          refine ⟨1164068448086270806285361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3104182528230055483427629 1164068448086270806285361)
          ·
            refine ⟨873051336064703104714021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164068448086270806285361 873051336064703104714021)
            ·
              refine ⟨163697125512131832133879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 873051336064703104714021 163697125512131832133879)
              ·
                refine ⟨245545688268197748200819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163697125512131832133879 245545688268197748200819)
                ·
                  refine ⟨368318532402296622301229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245545688268197748200819 368318532402296622301229)
                  ·
                    refine ⟨138119449650861233362961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368318532402296622301229 138119449650861233362961)
                    ·
                      refine ⟨103589587238145925022221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138119449650861233362961 103589587238145925022221)
                      ·
                        rfl

theorem cell23_201740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_201740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201740 prefixEnd_201740 := by exact prefixLift 201740
  have htrace : WordTrace (prefixWord ++ tailWord_201740) baseStart_201740 baseEnd_201740 := by
    simpa [prefixWord, tailWord_201740, baseEnd_201740] using wordTrace_append hprefix tailTrace_201740
  have hstable : (prefixWord ++ tailWord_201740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201740).length < 2 ^ (prefixWord ++ tailWord_201740).sum := by decide
  have hdescent : baseEnd_201740 < baseStart_201740 := by decide
  rcases family_descends (prefixWord ++ tailWord_201740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201759 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 7]
def baseStart_201759 : Nat := 118140960795 + 201759 * 2 ^ 59
def prefixEnd_201759 : Nat := 4983230072969 + 3 ^ 40 * 201759 * 2
def baseEnd_201759 : Nat := 11511038152286816742737

theorem tailTrace_201759 : CollatzResearch.WordTrace tailWord_201759 prefixEnd_201759 11511038152286816742737 := by
  unfold tailWord_201759
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358755276069075538992331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4905836850712717025994887 7358755276069075538992331)
  ·
    refine ⟨11038132914103613308488497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7358755276069075538992331 11038132914103613308488497)
    ·
      refine ⟨8278599685577709981366373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11038132914103613308488497 8278599685577709981366373)
      ·
        refine ⟨1552237441045820621506195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8278599685577709981366373 1552237441045820621506195)
        ·
          refine ⟨2328356161568730932259293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552237441045820621506195 2328356161568730932259293)
          ·
            refine ⟨873133560588274099597235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2328356161568730932259293 873133560588274099597235)
            ·
              refine ⟨1309700340882411149395853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873133560588274099597235 1309700340882411149395853)
              ·
                refine ⟨491137627830904181023445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1309700340882411149395853 491137627830904181023445)
                ·
                  refine ⟨11511038152286816742737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 491137627830904181023445 11511038152286816742737)
                  ·
                    rfl

theorem cell23_201759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 7].length) (baseStart_201759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201759 prefixEnd_201759 := by exact prefixLift 201759
  have htrace : WordTrace (prefixWord ++ tailWord_201759) baseStart_201759 baseEnd_201759 := by
    simpa [prefixWord, tailWord_201759, baseEnd_201759] using wordTrace_append hprefix tailTrace_201759
  have hstable : (prefixWord ++ tailWord_201759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201759).length < 2 ^ (prefixWord ++ tailWord_201759).sum := by decide
  have hdescent : baseEnd_201759 < baseStart_201759 := by decide
  rcases family_descends (prefixWord ++ tailWord_201759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201806 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_201806 : Nat := 118140960795 + 201806 * 2 ^ 59
def prefixEnd_201806 : Nat := 4983230072969 + 3 ^ 40 * 201806 * 2
def baseEnd_201806 : Nat := 34541158987114222265639

theorem tailTrace_201806 : CollatzResearch.WordTrace tailWord_201806 prefixEnd_201806 34541158987114222265639 := by
  unfold tailWord_201806
  simp only [CollatzResearch.WordTrace]
  refine ⟨920058688362350320744159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4906979671265868377302181 920058688362350320744159)
  ·
    refine ⟨1380088032543525481116239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 920058688362350320744159 1380088032543525481116239)
    ·
      refine ⟨2070132048815288221674359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380088032543525481116239 2070132048815288221674359)
      ·
        refine ⟨3105198073222932332511539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070132048815288221674359 3105198073222932332511539)
        ·
          refine ⟨4657797109834398498767309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105198073222932332511539 4657797109834398498767309)
          ·
            refine ⟨1746673916187899437037741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4657797109834398498767309 1746673916187899437037741)
            ·
              refine ⟨655002718570462288889153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1746673916187899437037741 655002718570462288889153)
              ·
                refine ⟨491252038927846716666865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655002718570462288889153 491252038927846716666865)
                ·
                  refine ⟨368439029195885037500149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491252038927846716666865 368439029195885037500149)
                  ·
                    refine ⟨34541158987114222265639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 368439029195885037500149 34541158987114222265639)
                    ·
                      rfl

theorem cell23_201806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_201806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201806 prefixEnd_201806 := by exact prefixLift 201806
  have htrace : WordTrace (prefixWord ++ tailWord_201806) baseStart_201806 baseEnd_201806 := by
    simpa [prefixWord, tailWord_201806, baseEnd_201806] using wordTrace_append hprefix tailTrace_201806
  have hstable : (prefixWord ++ tailWord_201806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201806).length < 2 ^ (prefixWord ++ tailWord_201806).sum := by decide
  have hdescent : baseEnd_201806 < baseStart_201806 := by decide
  rcases family_descends (prefixWord ++ tailWord_201806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201810 : List Nat := [3, 2, 2, 1, 3, 2, 3, 2, 5]
def baseStart_201810 : Nat := 118140960795 + 201810 * 2 ^ 59
def prefixEnd_201810 : Nat := 4983230072969 + 3 ^ 40 * 201810 * 2
def baseEnd_201810 : Nat := 11513947875995627905211

theorem tailTrace_201810 : CollatzResearch.WordTrace tailWord_201810 prefixEnd_201810 11513947875995627905211 := by
  unfold tailWord_201810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1840153849721077812274721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4907076932589540832732589 1840153849721077812274721)
  ·
    refine ⟨1380115387290808359206041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1840153849721077812274721 1380115387290808359206041)
    ·
      refine ⟨1035086540468106269404531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380115387290808359206041 1035086540468106269404531)
      ·
        refine ⟨1552629810702159404106797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035086540468106269404531 1552629810702159404106797)
        ·
          refine ⟨582236179013309776540049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1552629810702159404106797 582236179013309776540049)
          ·
            refine ⟨436677134259982332405037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582236179013309776540049 436677134259982332405037)
            ·
              refine ⟨163753925347493374651889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436677134259982332405037 163753925347493374651889)
              ·
                refine ⟨122815444010620030988917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163753925347493374651889 122815444010620030988917)
                ·
                  refine ⟨11513947875995627905211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122815444010620030988917 11513947875995627905211)
                  ·
                    rfl

theorem cell23_201810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_201810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201810 prefixEnd_201810 := by exact prefixLift 201810
  have htrace : WordTrace (prefixWord ++ tailWord_201810) baseStart_201810 baseEnd_201810 := by
    simpa [prefixWord, tailWord_201810, baseEnd_201810] using wordTrace_append hprefix tailTrace_201810
  have hstable : (prefixWord ++ tailWord_201810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201810).length < 2 ^ (prefixWord ++ tailWord_201810).sum := by decide
  have hdescent : baseEnd_201810 < baseStart_201810 := by decide
  rcases family_descends (prefixWord ++ tailWord_201810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201821 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_201821 : Nat := 118140960795 + 201821 * 2 ^ 59
def prefixEnd_201821 : Nat := 4983230072969 + 3 ^ 40 * 201821 * 2
def baseEnd_201821 : Nat := 103631179171160108109349

theorem tailTrace_201821 : CollatzResearch.WordTrace tailWord_201821 prefixEnd_201821 103631179171160108109349 := by
  unfold tailWord_201821
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361016601844460127749317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4907344401229640085166211 7361016601844460127749317)
  ·
    refine ⟨1380190612845836273952997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7361016601844460127749317 1380190612845836273952997)
    ·
      refine ⟨258785739908594301366187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1380190612845836273952997 258785739908594301366187)
      ·
        refine ⟨388178609862891452049281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258785739908594301366187 388178609862891452049281)
        ·
          refine ⟨291133957397168589036961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388178609862891452049281 291133957397168589036961)
          ·
            refine ⟨218350468047876441777721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291133957397168589036961 218350468047876441777721)
            ·
              refine ⟨163762851035907331333291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218350468047876441777721 163762851035907331333291)
              ·
                refine ⟨245644276553860996999937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163762851035907331333291 245644276553860996999937)
                ·
                  refine ⟨184233207415395747749953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245644276553860996999937 184233207415395747749953)
                  ·
                    refine ⟨138174905561546810812465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184233207415395747749953 138174905561546810812465)
                    ·
                      refine ⟨103631179171160108109349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138174905561546810812465 103631179171160108109349)
                      ·
                        rfl

theorem cell23_201821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_201821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201821 prefixEnd_201821 := by exact prefixLift 201821
  have htrace : WordTrace (prefixWord ++ tailWord_201821) baseStart_201821 baseEnd_201821 := by
    simpa [prefixWord, tailWord_201821, baseEnd_201821] using wordTrace_append hprefix tailTrace_201821
  have hstable : (prefixWord ++ tailWord_201821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201821).length < 2 ^ (prefixWord ++ tailWord_201821).sum := by decide
  have hdescent : baseEnd_201821 < baseStart_201821 := by decide
  rcases family_descends (prefixWord ++ tailWord_201821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201836 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_201836 : Nat := 118140960795 + 201836 * 2 ^ 59
def prefixEnd_201836 : Nat := 4983230072969 + 3 ^ 40 * 201836 * 2
def baseEnd_201836 : Nat := 34546293793659183140593

theorem tailTrace_201836 : CollatzResearch.WordTrace tailWord_201836 prefixEnd_201836 34546293793659183140593 := by
  unfold tailWord_201836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680781848395058844772681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4907709131193411793030241 3680781848395058844772681)
  ·
    refine ⟨2760586386296294133579511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3680781848395058844772681 2760586386296294133579511)
    ·
      refine ⟨4140879579444441200369267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760586386296294133579511 4140879579444441200369267)
      ·
        refine ⟨6211319369166661800553901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140879579444441200369267 6211319369166661800553901)
        ·
          refine ⟨2329244763437498175207713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6211319369166661800553901 2329244763437498175207713)
          ·
            refine ⟨1746933572578123631405785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2329244763437498175207713 1746933572578123631405785)
            ·
              refine ⟨1310200179433592723554339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746933572578123631405785 1310200179433592723554339)
              ·
                refine ⟨1965300269150389085331509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310200179433592723554339 1965300269150389085331509)
                ·
                  refine ⟨184246900232848976749829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1965300269150389085331509 184246900232848976749829)
                  ·
                    refine ⟨34546293793659183140593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184246900232848976749829 34546293793659183140593)
                    ·
                      rfl

theorem cell23_201836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_201836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201836 prefixEnd_201836 := by exact prefixLift 201836
  have htrace : WordTrace (prefixWord ++ tailWord_201836) baseStart_201836 baseEnd_201836 := by
    simpa [prefixWord, tailWord_201836, baseEnd_201836] using wordTrace_append hprefix tailTrace_201836
  have hstable : (prefixWord ++ tailWord_201836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201836).length < 2 ^ (prefixWord ++ tailWord_201836).sum := by decide
  have hdescent : baseEnd_201836 < baseStart_201836 := by decide
  rcases family_descends (prefixWord ++ tailWord_201836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201893 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_201893 : Nat := 118140960795 + 201893 * 2 ^ 59
def prefixEnd_201893 : Nat := 4983230072969 + 3 ^ 40 * 201893 * 2
def baseEnd_201893 : Nat := 103668149778283826409017

theorem tailTrace_201893 : CollatzResearch.WordTrace tailWord_201893 prefixEnd_201893 103668149778283826409017 := by
  unfold tailWord_201893
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363642657583616424370333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4909095105055744282913555 7363642657583616424370333)
  ·
    refine ⟨2761365996593856159138875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7363642657583616424370333 2761365996593856159138875)
    ·
      refine ⟨4142048994890784238708313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761365996593856159138875 4142048994890784238708313)
      ·
        refine ⟨3106536746168088179031235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4142048994890784238708313 3106536746168088179031235)
        ·
          refine ⟨4659805119252132268546853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106536746168088179031235 4659805119252132268546853)
          ·
            refine ⟨873713459859774800352535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4659805119252132268546853 873713459859774800352535)
            ·
              refine ⟨1310570189789662200528803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873713459859774800352535 1310570189789662200528803)
              ·
                refine ⟨1965855284684493300793205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310570189789662200528803 1965855284684493300793205)
                ·
                  refine ⟨184298932939171246949363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1965855284684493300793205 184298932939171246949363)
                  ·
                    refine ⟨276448399408756870424045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 184298932939171246949363 276448399408756870424045)
                    ·
                      refine ⟨103668149778283826409017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 276448399408756870424045 103668149778283826409017)
                      ·
                        rfl

theorem cell23_201893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_201893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201893 prefixEnd_201893 := by exact prefixLift 201893
  have htrace : WordTrace (prefixWord ++ tailWord_201893) baseStart_201893 baseEnd_201893 := by
    simpa [prefixWord, tailWord_201893, baseEnd_201893] using wordTrace_append hprefix tailTrace_201893
  have hstable : (prefixWord ++ tailWord_201893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201893).length < 2 ^ (prefixWord ++ tailWord_201893).sum := by decide
  have hdescent : baseEnd_201893 < baseStart_201893 := by decide
  rcases family_descends (prefixWord ++ tailWord_201893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201913 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 1, 5]
def baseStart_201913 : Nat := 118140960795 + 201913 * 2 ^ 59
def prefixEnd_201913 : Nat := 4983230072969 + 3 ^ 40 * 201913 * 2
def baseEnd_201913 : Nat := 34559473130457916052975

theorem tailTrace_201913 : CollatzResearch.WordTrace tailWord_201913 prefixEnd_201913 34559473130457916052975 := by
  unfold tailWord_201913
  simp only [CollatzResearch.WordTrace]
  refine ⟨7364372117511159840098393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4909581411674106560065595 7364372117511159840098393)
  ·
    refine ⟨5523279088133369880073795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7364372117511159840098393 5523279088133369880073795)
    ·
      refine ⟨8284918632200054820110693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5523279088133369880073795 8284918632200054820110693)
      ·
        refine ⟨1553422243537510278770755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8284918632200054820110693 1553422243537510278770755)
        ·
          refine ⟨2330133365306265418156133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553422243537510278770755 2330133365306265418156133)
          ·
            refine ⟨436900005994924765904275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2330133365306265418156133 436900005994924765904275)
            ·
              refine ⟨655350008992387148856413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436900005994924765904275 655350008992387148856413)
              ·
                refine ⟨245756253372145180821155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 655350008992387148856413 245756253372145180821155)
                ·
                  refine ⟨368634380058217771231733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245756253372145180821155 368634380058217771231733)
                  ·
                    refine ⟨34559473130457916052975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 368634380058217771231733 34559473130457916052975)
                    ·
                      rfl

theorem cell23_201913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_201913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201913 prefixEnd_201913 := by exact prefixLift 201913
  have htrace : WordTrace (prefixWord ++ tailWord_201913) baseStart_201913 baseEnd_201913 := by
    simpa [prefixWord, tailWord_201913, baseEnd_201913] using wordTrace_append hprefix tailTrace_201913
  have hstable : (prefixWord ++ tailWord_201913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201913).length < 2 ^ (prefixWord ++ tailWord_201913).sum := by decide
  have hdescent : baseEnd_201913 < baseStart_201913 := by decide
  rcases family_descends (prefixWord ++ tailWord_201913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201943 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 2, 4]
def baseStart_201943 : Nat := 118140960795 + 201943 * 2 ^ 59
def prefixEnd_201943 : Nat := 4983230072969 + 3 ^ 40 * 201943 * 2
def baseEnd_201943 : Nat := 34564607937002876927929

theorem tailTrace_201943 : CollatzResearch.WordTrace tailWord_201943 prefixEnd_201943 34564607937002876927929 := by
  unfold tailWord_201943
  simp only [CollatzResearch.WordTrace]
  refine ⟨7365466307402474963690483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4910310871601649975793655 7365466307402474963690483)
  ·
    refine ⟨11048199461103712445535725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7365466307402474963690483 11048199461103712445535725)
    ·
      refine ⟨4143074797913892167075897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11048199461103712445535725 4143074797913892167075897)
      ·
        refine ⟨3107306098435419125306923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4143074797913892167075897 3107306098435419125306923)
        ·
          refine ⟨4660959147653128687960385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107306098435419125306923 4660959147653128687960385)
          ·
            refine ⟨3495719360739846515970289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660959147653128687960385 3495719360739846515970289)
            ·
              refine ⟨2621789520554884886977717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3495719360739846515970289 2621789520554884886977717)
              ·
                refine ⟨245792767552020458154161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2621789520554884886977717 245792767552020458154161)
                ·
                  refine ⟨184344575664015343615621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245792767552020458154161 184344575664015343615621)
                  ·
                    refine ⟨34564607937002876927929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184344575664015343615621 34564607937002876927929)
                    ·
                      rfl

theorem cell23_201943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_201943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201943 prefixEnd_201943 := by exact prefixLift 201943
  have htrace : WordTrace (prefixWord ++ tailWord_201943) baseStart_201943 baseEnd_201943 := by
    simpa [prefixWord, tailWord_201943, baseEnd_201943] using wordTrace_append hprefix tailTrace_201943
  have hstable : (prefixWord ++ tailWord_201943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201943).length < 2 ^ (prefixWord ++ tailWord_201943).sum := by decide
  have hdescent : baseEnd_201943 < baseStart_201943 := by decide
  rcases family_descends (prefixWord ++ tailWord_201943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201970 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_201970 : Nat := 118140960795 + 201970 * 2 ^ 59
def prefixEnd_201970 : Nat := 4983230072969 + 3 ^ 40 * 201970 * 2
def baseEnd_201970 : Nat := 103707687788680025146163

theorem tailTrace_201970 : CollatzResearch.WordTrace tailWord_201970 prefixEnd_201970 103707687788680025146163 := by
  unfold tailWord_201970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841612769576164643730841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4910967385536439049948909 1841612769576164643730841)
  ·
    refine ⟨1381209577182123482798131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1841612769576164643730841 1381209577182123482798131)
    ·
      refine ⟨2071814365773185224197197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381209577182123482798131 2071814365773185224197197)
      ·
        refine ⟨776930387164944459073949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2071814365773185224197197 776930387164944459073949)
        ·
          refine ⟨291348895186854172152731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 776930387164944459073949 291348895186854172152731)
          ·
            refine ⟨437023342780281258229097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291348895186854172152731 437023342780281258229097)
            ·
              refine ⟨327767507085210943671823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437023342780281258229097 327767507085210943671823)
              ·
                refine ⟨491651260627816415507735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327767507085210943671823 491651260627816415507735)
                ·
                  refine ⟨737476890941724623261603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491651260627816415507735 737476890941724623261603)
                  ·
                    refine ⟨1106215336412586934892405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 737476890941724623261603 1106215336412586934892405)
                    ·
                      refine ⟨103707687788680025146163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1106215336412586934892405 103707687788680025146163)
                      ·
                        rfl

theorem cell23_201970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_201970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201970 prefixEnd_201970 := by exact prefixLift 201970
  have htrace : WordTrace (prefixWord ++ tailWord_201970) baseStart_201970 baseEnd_201970 := by
    simpa [prefixWord, tailWord_201970, baseEnd_201970] using wordTrace_append hprefix tailTrace_201970
  have hstable : (prefixWord ++ tailWord_201970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201970).length < 2 ^ (prefixWord ++ tailWord_201970).sum := by decide
  have hdescent : baseEnd_201970 < baseStart_201970 := by decide
  rcases family_descends (prefixWord ++ tailWord_201970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202057 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 2, 2, 2]
def baseStart_202057 : Nat := 118140960795 + 202057 * 2 ^ 59
def prefixEnd_202057 : Nat := 4983230072969 + 3 ^ 40 * 202057 * 2
def baseEnd_202057 : Nat := 103752360605621184758263

theorem tailTrace_202057 : CollatzResearch.WordTrace tailWord_202057 prefixEnd_202057 103752360605621184758263 := by
  unfold tailWord_202057
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369624228989472433340425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4913082819326314955560283 7369624228989472433340425)
  ·
    refine ⟨5527218171742104325005319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7369624228989472433340425 5527218171742104325005319)
    ·
      refine ⟨8290827257613156487507979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527218171742104325005319 8290827257613156487507979)
      ·
        refine ⟨12436240886419734731261969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290827257613156487507979 12436240886419734731261969)
        ·
          refine ⟨9327180664814801048446477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12436240886419734731261969 9327180664814801048446477)
          ·
            refine ⟨3497692749305550393167429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9327180664814801048446477 3497692749305550393167429)
            ·
              refine ⟨655817390494790698718893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3497692749305550393167429 655817390494790698718893)
              ·
                refine ⟨245931521435546512019585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 655817390494790698718893 245931521435546512019585)
                ·
                  refine ⟨184448641076659884014689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245931521435546512019585 184448641076659884014689)
                  ·
                    refine ⟨138336480807494913011017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184448641076659884014689 138336480807494913011017)
                    ·
                      refine ⟨103752360605621184758263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138336480807494913011017 103752360605621184758263)
                      ·
                        rfl

theorem cell23_202057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 2, 2].length) (baseStart_202057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202057 prefixEnd_202057 := by exact prefixLift 202057
  have htrace : WordTrace (prefixWord ++ tailWord_202057) baseStart_202057 baseEnd_202057 := by
    simpa [prefixWord, tailWord_202057, baseEnd_202057] using wordTrace_append hprefix tailTrace_202057
  have hstable : (prefixWord ++ tailWord_202057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202057).length < 2 ^ (prefixWord ++ tailWord_202057).sum := by decide
  have hdescent : baseEnd_202057 < baseStart_202057 := by decide
  rcases family_descends (prefixWord ++ tailWord_202057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202080 : List Nat := [2, 1, 1, 3, 4, 1, 1, 5, 5]
def baseStart_202080 : Nat := 118140960795 + 202080 * 2 ^ 59
def prefixEnd_202080 : Nat := 4983230072969 + 3 ^ 40 * 202080 * 2
def baseEnd_202080 : Nat := 11529352295630510530073

theorem tailTrace_202080 : CollatzResearch.WordTrace tailWord_202080 prefixEnd_202080 11529352295630510530073 := by
  unfold tailWord_202080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685231553953073680713847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4913642071937431574285129 3685231553953073680713847)
  ·
    refine ⟨5527847330929610521070771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685231553953073680713847 5527847330929610521070771)
    ·
      refine ⟨8291770996394415781606157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527847330929610521070771 8291770996394415781606157)
      ·
        refine ⟨3109414123647905918102309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8291770996394415781606157 3109414123647905918102309)
        ·
          refine ⟨583015148183982359644183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3109414123647905918102309 583015148183982359644183)
          ·
            refine ⟨874522722275973539466275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583015148183982359644183 874522722275973539466275)
            ·
              refine ⟨1311784083413960309199413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874522722275973539466275 1311784083413960309199413)
              ·
                refine ⟨122979757820058778987445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1311784083413960309199413 122979757820058778987445)
                ·
                  refine ⟨11529352295630510530073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122979757820058778987445 11529352295630510530073)
                  ·
                    rfl

theorem cell23_202080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 5].length) (baseStart_202080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202080 prefixEnd_202080 := by exact prefixLift 202080
  have htrace : WordTrace (prefixWord ++ tailWord_202080) baseStart_202080 baseEnd_202080 := by
    simpa [prefixWord, tailWord_202080, baseEnd_202080] using wordTrace_append hprefix tailTrace_202080
  have hstable : (prefixWord ++ tailWord_202080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202080).length < 2 ^ (prefixWord ++ tailWord_202080).sum := by decide
  have hdescent : baseEnd_202080 < baseStart_202080 := by decide
  rcases family_descends (prefixWord ++ tailWord_202080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202178 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_202178 : Nat := 118140960795 + 202178 * 2 ^ 59
def prefixEnd_202178 : Nat := 4983230072969 + 3 ^ 40 * 202178 * 2
def baseEnd_202178 : Nat := 34604830588271737115069

theorem tailTrace_202178 : CollatzResearch.WordTrace tailWord_202178 prefixEnd_202178 34604830588271737115069 := by
  unfold tailWord_202178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843509365387777524623797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4916024974367406732330125 1843509365387777524623797)
  ·
    refine ⟨172829003005104142933481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1843509365387777524623797 172829003005104142933481)
    ·
      refine ⟨129621752253828107200111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172829003005104142933481 129621752253828107200111)
      ·
        refine ⟨194432628380742160800167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129621752253828107200111 194432628380742160800167)
        ·
          refine ⟨291648942571113241200251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194432628380742160800167 291648942571113241200251)
          ·
            refine ⟨437473413856669861800377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291648942571113241200251 437473413856669861800377)
            ·
              refine ⟨328105060392502396350283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437473413856669861800377 328105060392502396350283)
              ·
                refine ⟨492157590588753594525425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328105060392502396350283 492157590588753594525425)
                ·
                  refine ⟨369118192941565195894069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492157590588753594525425 369118192941565195894069)
                  ·
                    refine ⟨34604830588271737115069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 369118192941565195894069 34604830588271737115069)
                    ·
                      rfl

theorem cell23_202178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_202178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202178 prefixEnd_202178 := by exact prefixLift 202178
  have htrace : WordTrace (prefixWord ++ tailWord_202178) baseStart_202178 baseEnd_202178 := by
    simpa [prefixWord, tailWord_202178, baseEnd_202178] using wordTrace_append hprefix tailTrace_202178
  have hstable : (prefixWord ++ tailWord_202178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202178).length < 2 ^ (prefixWord ++ tailWord_202178).sum := by decide
  have hdescent : baseEnd_202178 < baseStart_202178 := by decide
  rcases family_descends (prefixWord ++ tailWord_202178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202200 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 1, 5]
def baseStart_202200 : Nat := 118140960795 + 202200 * 2 ^ 59
def prefixEnd_202200 : Nat := 4983230072969 + 3 ^ 40 * 202200 * 2
def baseEnd_202200 : Nat := 34608596113071375090035

theorem tailTrace_202200 : CollatzResearch.WordTrace tailWord_202200 prefixEnd_202200 34608596113071375090035 := by
  unfold tailWord_202200
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687419933735703927898027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4916559911647605237197369 3687419933735703927898027)
  ·
    refine ⟨5531129900603555891847041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3687419933735703927898027 5531129900603555891847041)
    ·
      refine ⟨4148347425452666918885281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5531129900603555891847041 4148347425452666918885281)
      ·
        refine ⟨3111260569089500189163961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4148347425452666918885281 3111260569089500189163961)
        ·
          refine ⟨2333445426817125141872971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111260569089500189163961 2333445426817125141872971)
          ·
            refine ⟨3500168140225687712809457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333445426817125141872971 3500168140225687712809457)
            ·
              refine ⟨2625126105169265784607093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500168140225687712809457 2625126105169265784607093)
              ·
                refine ⟨246105572359618667306915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2625126105169265784607093 246105572359618667306915)
                ·
                  refine ⟨369158358539428000960373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246105572359618667306915 369158358539428000960373)
                  ·
                    refine ⟨34608596113071375090035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 369158358539428000960373 34608596113071375090035)
                    ·
                      rfl

theorem cell23_202200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_202200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202200 prefixEnd_202200 := by exact prefixLift 202200
  have htrace : WordTrace (prefixWord ++ tailWord_202200) baseStart_202200 baseEnd_202200 := by
    simpa [prefixWord, tailWord_202200, baseEnd_202200] using wordTrace_append hprefix tailTrace_202200
  have hstable : (prefixWord ++ tailWord_202200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202200).length < 2 ^ (prefixWord ++ tailWord_202200).sum := by decide
  have hdescent : baseEnd_202200 < baseStart_202200 := by decide
  rcases family_descends (prefixWord ++ tailWord_202200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202207 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 2, 3, 2]
def baseStart_202207 : Nat := 118140960795 + 202207 * 2 ^ 59
def prefixEnd_202207 : Nat := 4983230072969 + 3 ^ 40 * 202207 * 2
def baseEnd_202207 : Nat := 103829382703795597882573

theorem tailTrace_202207 : CollatzResearch.WordTrace tailWord_202207 prefixEnd_202207 103829382703795597882573 := by
  unfold tailWord_202207
  simp only [CollatzResearch.WordTrace]
  refine ⟨7375095178446048051300875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4916730118964032034200583 7375095178446048051300875)
  ·
    refine ⟨11062642767669072076951313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7375095178446048051300875 11062642767669072076951313)
    ·
      refine ⟨8296982075751804057713485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11062642767669072076951313 8296982075751804057713485)
      ·
        refine ⟨3111368278406926521642557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8296982075751804057713485 3111368278406926521642557)
        ·
          refine ⟨1166763104402597445615959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3111368278406926521642557 1166763104402597445615959)
          ·
            refine ⟨1750144656603896168423939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166763104402597445615959 1750144656603896168423939)
            ·
              refine ⟨2625216984905844252635909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750144656603896168423939 2625216984905844252635909)
              ·
                refine ⟨492228184669845797369233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2625216984905844252635909 492228184669845797369233)
                ·
                  refine ⟨369171138502384348026925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492228184669845797369233 369171138502384348026925)
                  ·
                    refine ⟨138439176938394130510097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369171138502384348026925 138439176938394130510097)
                    ·
                      refine ⟨103829382703795597882573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138439176938394130510097 103829382703795597882573)
                      ·
                        rfl

theorem cell23_202207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_202207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202207 prefixEnd_202207 := by exact prefixLift 202207
  have htrace : WordTrace (prefixWord ++ tailWord_202207) baseStart_202207 baseEnd_202207 := by
    simpa [prefixWord, tailWord_202207, baseEnd_202207] using wordTrace_append hprefix tailTrace_202207
  have hstable : (prefixWord ++ tailWord_202207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202207).length < 2 ^ (prefixWord ++ tailWord_202207).sum := by decide
  have hdescent : baseEnd_202207 < baseStart_202207 := by decide
  rcases family_descends (prefixWord ++ tailWord_202207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202241 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_202241 : Nat := 118140960795 + 202241 * 2 ^ 59
def prefixEnd_202241 : Nat := 4983230072969 + 3 ^ 40 * 202241 * 2
def baseEnd_202241 : Nat := 103846841046048464857417

theorem tailTrace_202241 : CollatzResearch.WordTrace tailWord_202241 prefixEnd_202241 103846841046048464857417 := by
  unfold tailWord_202241
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376335260322871858038577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4917556840215247905359051 7376335260322871858038577)
  ·
    refine ⟨5532251445242153893528933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7376335260322871858038577 5532251445242153893528933)
    ·
      refine ⟨1037297145982903855036675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5532251445242153893528933 1037297145982903855036675)
      ·
        refine ⟨1555945718974355782555013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037297145982903855036675 1555945718974355782555013)
        ·
          refine ⟨291739822307691709229065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1555945718974355782555013 291739822307691709229065)
          ·
            refine ⟨218804866730768781921799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291739822307691709229065 218804866730768781921799)
            ·
              refine ⟨328207300096153172882699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218804866730768781921799 328207300096153172882699)
              ·
                refine ⟨492310950144229759324049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328207300096153172882699 492310950144229759324049)
                ·
                  refine ⟨369233212608172319493037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492310950144229759324049 369233212608172319493037)
                  ·
                    refine ⟨138462454728064619809889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369233212608172319493037 138462454728064619809889)
                    ·
                      refine ⟨103846841046048464857417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138462454728064619809889 103846841046048464857417)
                      ·
                        rfl

theorem cell23_202241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_202241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202241 prefixEnd_202241 := by exact prefixLift 202241
  have htrace : WordTrace (prefixWord ++ tailWord_202241) baseStart_202241 baseEnd_202241 := by
    simpa [prefixWord, tailWord_202241, baseEnd_202241] using wordTrace_append hprefix tailTrace_202241
  have hstable : (prefixWord ++ tailWord_202241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202241).length < 2 ^ (prefixWord ++ tailWord_202241).sum := by decide
  have hdescent : baseEnd_202241 < baseStart_202241 := by decide
  rcases family_descends (prefixWord ++ tailWord_202241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202251 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 1, 5]
def baseStart_202251 : Nat := 118140960795 + 202251 * 2 ^ 59
def prefixEnd_202251 : Nat := 4983230072969 + 3 ^ 40 * 202251 * 2
def baseEnd_202251 : Nat := 34617325284197808577457

theorem tailTrace_202251 : CollatzResearch.WordTrace tailWord_202251 prefixEnd_202251 34617325284197808577457 := by
  unfold tailWord_202251
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376699990286643565902607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4917799993524429043935071 7376699990286643565902607)
  ·
    refine ⟨11065049985429965348853911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7376699990286643565902607 11065049985429965348853911)
    ·
      refine ⟨16597574978144948023280867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11065049985429965348853911 16597574978144948023280867)
      ·
        refine ⟨24896362467217422034921301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16597574978144948023280867 24896362467217422034921301)
        ·
          refine ⟨145877123831352082235867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 24896362467217422034921301 145877123831352082235867)
          ·
            refine ⟨218815685747028123353801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145877123831352082235867 218815685747028123353801)
            ·
              refine ⟨164111764310271092515351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218815685747028123353801 164111764310271092515351)
              ·
                refine ⟨246167646465406638773027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164111764310271092515351 246167646465406638773027)
                ·
                  refine ⟨369251469698109958159541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246167646465406638773027 369251469698109958159541)
                  ·
                    refine ⟨34617325284197808577457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 369251469698109958159541 34617325284197808577457)
                    ·
                      rfl

theorem cell23_202251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 5].length) (baseStart_202251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202251 prefixEnd_202251 := by exact prefixLift 202251
  have htrace : WordTrace (prefixWord ++ tailWord_202251) baseStart_202251 baseEnd_202251 := by
    simpa [prefixWord, tailWord_202251, baseEnd_202251] using wordTrace_append hprefix tailTrace_202251
  have hstable : (prefixWord ++ tailWord_202251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202251).length < 2 ^ (prefixWord ++ tailWord_202251).sum := by decide
  have hdescent : baseEnd_202251 < baseStart_202251 := by decide
  rcases family_descends (prefixWord ++ tailWord_202251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202254 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_202254 : Nat := 118140960795 + 202254 * 2 ^ 59
def prefixEnd_202254 : Nat := 4983230072969 + 3 ^ 40 * 202254 * 2
def baseEnd_202254 : Nat := 103853516294556913994857

theorem tailTrace_202254 : CollatzResearch.WordTrace tailWord_202254 prefixEnd_202254 103853516294556913994857 := by
  unfold tailWord_202254
  simp only [CollatzResearch.WordTrace]
  refine ⟨922101176159471884782727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4917872939517183385507877 922101176159471884782727)
  ·
    refine ⟨1383151764239207827174091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 922101176159471884782727 1383151764239207827174091)
    ·
      refine ⟨2074727646358811740761137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1383151764239207827174091 2074727646358811740761137)
      ·
        refine ⟨1556045734769108805570853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2074727646358811740761137 1556045734769108805570853)
        ·
          refine ⟨291758575269207901044535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1556045734769108805570853 291758575269207901044535)
          ·
            refine ⟨437637862903811851566803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291758575269207901044535 437637862903811851566803)
            ·
              refine ⟨656456794355717777350205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437637862903811851566803 656456794355717777350205)
              ·
                refine ⟨246171297883394166506327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656456794355717777350205 246171297883394166506327)
                ·
                  refine ⟨369256946825091249759491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246171297883394166506327 369256946825091249759491)
                  ·
                    refine ⟨553885420237636874639237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 369256946825091249759491 553885420237636874639237)
                    ·
                      refine ⟨103853516294556913994857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 553885420237636874639237 103853516294556913994857)
                      ·
                        rfl

theorem cell23_202254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_202254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202254 prefixEnd_202254 := by exact prefixLift 202254
  have htrace : WordTrace (prefixWord ++ tailWord_202254) baseStart_202254 baseEnd_202254 := by
    simpa [prefixWord, tailWord_202254, baseEnd_202254] using wordTrace_append hprefix tailTrace_202254
  have hstable : (prefixWord ++ tailWord_202254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202254).length < 2 ^ (prefixWord ++ tailWord_202254).sum := by decide
  have hdescent : baseEnd_202254 < baseStart_202254 := by decide
  rcases family_descends (prefixWord ++ tailWord_202254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202257 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_202257 : Nat := 118140960795 + 202257 * 2 ^ 59
def prefixEnd_202257 : Nat := 4983230072969 + 3 ^ 40 * 202257 * 2
def baseEnd_202257 : Nat := 103855056736520402257343

theorem tailTrace_202257 : CollatzResearch.WordTrace tailWord_202257 prefixEnd_202257 103855056736520402257343 := by
  unfold tailWord_202257
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376918828264906590621025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4917945885509937727080683 7376918828264906590621025)
  ·
    refine ⟨5532689121198679942965769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7376918828264906590621025 5532689121198679942965769)
    ·
      refine ⟨4149516840899009957224327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5532689121198679942965769 4149516840899009957224327)
      ·
        refine ⟨6224275261348514935836491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149516840899009957224327 6224275261348514935836491)
        ·
          refine ⟨9336412892022772403754737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224275261348514935836491 9336412892022772403754737)
          ·
            refine ⟨7002309669017079302816053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9336412892022772403754737 7002309669017079302816053)
            ·
              refine ⟨656466531470351184639005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7002309669017079302816053 656466531470351184639005)
              ·
                refine ⟨246174949301381694239627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656466531470351184639005 246174949301381694239627)
                ·
                  refine ⟨369262423952072541359441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246174949301381694239627 369262423952072541359441)
                  ·
                    refine ⟨276946817964054406019581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 369262423952072541359441 276946817964054406019581)
                    ·
                      refine ⟨103855056736520402257343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 276946817964054406019581 103855056736520402257343)
                      ·
                        rfl

theorem cell23_202257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_202257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202257 prefixEnd_202257 := by exact prefixLift 202257
  have htrace : WordTrace (prefixWord ++ tailWord_202257) baseStart_202257 baseEnd_202257 := by
    simpa [prefixWord, tailWord_202257, baseEnd_202257] using wordTrace_append hprefix tailTrace_202257
  have hstable : (prefixWord ++ tailWord_202257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202257).length < 2 ^ (prefixWord ++ tailWord_202257).sum := by decide
  have hdescent : baseEnd_202257 < baseStart_202257 := by decide
  rcases family_descends (prefixWord ++ tailWord_202257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202271 : List Nat := [1, 1, 2, 4, 1, 1, 4, 4, 1, 2, 2]
def baseStart_202271 : Nat := 118140960795 + 202271 * 2 ^ 59
def prefixEnd_202271 : Nat := 4983230072969 + 3 ^ 40 * 202271 * 2
def baseEnd_202271 : Nat := 103862245465683347482279

theorem tailTrace_202271 : CollatzResearch.WordTrace tailWord_202271 prefixEnd_202271 103862245465683347482279 := by
  unfold tailWord_202271
  simp only [CollatzResearch.WordTrace]
  refine ⟨7377429450214186981630667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4918286300142791321087111 7377429450214186981630667)
  ·
    refine ⟨11066144175321280472446001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7377429450214186981630667 11066144175321280472446001)
    ·
      refine ⟨8299608131490960354334501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11066144175321280472446001 8299608131490960354334501)
      ·
        refine ⟨1556176524654555066437719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8299608131490960354334501 1556176524654555066437719)
        ·
          refine ⟨2334264786981832599656579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556176524654555066437719 2334264786981832599656579)
          ·
            refine ⟨3501397180472748899484869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334264786981832599656579 3501397180472748899484869)
            ·
              refine ⟨656511971338640418653413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3501397180472748899484869 656511971338640418653413)
              ·
                refine ⟨123095994625995078497515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656511971338640418653413 123095994625995078497515)
                ·
                  refine ⟨184643991938992617746273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123095994625995078497515 184643991938992617746273)
                  ·
                    refine ⟨138482993954244463309705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184643991938992617746273 138482993954244463309705)
                    ·
                      refine ⟨103862245465683347482279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138482993954244463309705 103862245465683347482279)
                      ·
                        rfl

theorem cell23_202271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_202271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202271 prefixEnd_202271 := by exact prefixLift 202271
  have htrace : WordTrace (prefixWord ++ tailWord_202271) baseStart_202271 baseEnd_202271 := by
    simpa [prefixWord, tailWord_202271, baseEnd_202271] using wordTrace_append hprefix tailTrace_202271
  have hstable : (prefixWord ++ tailWord_202271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202271).length < 2 ^ (prefixWord ++ tailWord_202271).sum := by decide
  have hdescent : baseEnd_202271 < baseStart_202271 := by decide
  rcases family_descends (prefixWord ++ tailWord_202271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202314 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_202314 : Nat := 118140960795 + 202314 * 2 ^ 59
def prefixEnd_202314 : Nat := 4983230072969 + 3 ^ 40 * 202314 * 2
def baseEnd_202314 : Nat := 103884325133826679244581

theorem tailTrace_202314 : CollatzResearch.WordTrace tailWord_202314 prefixEnd_202314 103884325133826679244581 := by
  unfold tailWord_202314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844749447264601331361499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4919331859372270216963997 1844749447264601331361499)
  ·
    refine ⟨2767124170896901997042249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844749447264601331361499 2767124170896901997042249)
    ·
      refine ⟨2075343128172676497781687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2767124170896901997042249 2075343128172676497781687)
      ·
        refine ⟨3113014692259014746672531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075343128172676497781687 3113014692259014746672531)
        ·
          refine ⟨4669522038388522120008797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113014692259014746672531 4669522038388522120008797)
          ·
            refine ⟨1751070764395695795003299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4669522038388522120008797 1751070764395695795003299)
            ·
              refine ⟨2626606146593543692504949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751070764395695795003299 2626606146593543692504949)
              ·
                refine ⟨246244326243144721172339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2626606146593543692504949 246244326243144721172339)
                ·
                  refine ⟨369366489364717081758509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246244326243144721172339 369366489364717081758509)
                  ·
                    refine ⟨138512433511768905659441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369366489364717081758509 138512433511768905659441)
                    ·
                      refine ⟨103884325133826679244581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138512433511768905659441 103884325133826679244581)
                      ·
                        rfl

theorem cell23_202314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_202314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202314 prefixEnd_202314 := by exact prefixLift 202314
  have htrace : WordTrace (prefixWord ++ tailWord_202314) baseStart_202314 baseEnd_202314 := by
    simpa [prefixWord, tailWord_202314, baseEnd_202314] using wordTrace_append hprefix tailTrace_202314
  have hstable : (prefixWord ++ tailWord_202314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202314).length < 2 ^ (prefixWord ++ tailWord_202314).sum := by decide
  have hdescent : baseEnd_202314 < baseStart_202314 := by decide
  rcases family_descends (prefixWord ++ tailWord_202314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202378 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_202378 : Nat := 118140960795 + 202378 * 2 ^ 59
def prefixEnd_202378 : Nat := 4983230072969 + 3 ^ 40 * 202378 * 2
def baseEnd_202378 : Nat := 103917187895714428844287

theorem tailTrace_202378 : CollatzResearch.WordTrace tailWord_202378 prefixEnd_202378 103917187895714428844287 := by
  unfold tailWord_202378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1845333015206636063943947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4920888040551029503850525 1845333015206636063943947)
  ·
    refine ⟨2767999522809954095915921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1845333015206636063943947 2767999522809954095915921)
    ·
      refine ⟨2075999642107465571936941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2767999522809954095915921 2075999642107465571936941)
      ·
        refine ⟨778499865790299589476353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2075999642107465571936941 778499865790299589476353)
        ·
          refine ⟨583874899342724692107265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778499865790299589476353 583874899342724692107265)
          ·
            refine ⟨437906174507043519080449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583874899342724692107265 437906174507043519080449)
            ·
              refine ⟨328429630880282639310337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437906174507043519080449 328429630880282639310337)
              ·
                refine ⟨246322223160211979482753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328429630880282639310337 246322223160211979482753)
                ·
                  refine ⟨184741667370158984612065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246322223160211979482753 184741667370158984612065)
                  ·
                    refine ⟨138556250527619238459049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184741667370158984612065 138556250527619238459049)
                    ·
                      refine ⟨103917187895714428844287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138556250527619238459049 103917187895714428844287)
                      ·
                        rfl

theorem cell23_202378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_202378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202378 prefixEnd_202378 := by exact prefixLift 202378
  have htrace : WordTrace (prefixWord ++ tailWord_202378) baseStart_202378 baseEnd_202378 := by
    simpa [prefixWord, tailWord_202378, baseEnd_202378] using wordTrace_append hprefix tailTrace_202378
  have hstable : (prefixWord ++ tailWord_202378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202378).length < 2 ^ (prefixWord ++ tailWord_202378).sum := by decide
  have hdescent : baseEnd_202378 < baseStart_202378 := by decide
  rcases family_descends (prefixWord ++ tailWord_202378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202524 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_202524 : Nat := 118140960795 + 202524 * 2 ^ 59
def prefixEnd_202524 : Nat := 4983230072969 + 3 ^ 40 * 202524 * 2
def baseEnd_202524 : Nat := 103992156071270857618615

theorem tailTrace_202524 : CollatzResearch.WordTrace tailWord_202524 prefixEnd_202524 103992156071270857618615 := by
  unfold tailWord_202524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693328559148805595295313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4924438078865074127060417 3693328559148805595295313)
  ·
    refine ⟨2769996419361604196471485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3693328559148805595295313 2769996419361604196471485)
    ·
      refine ⟨1038748657260601573676807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2769996419361604196471485 1038748657260601573676807)
      ·
        refine ⟨1558122985890902360515211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038748657260601573676807 1558122985890902360515211)
        ·
          refine ⟨2337184478836353540772817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558122985890902360515211 2337184478836353540772817)
          ·
            refine ⟨1752888359127265155579613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337184478836353540772817 1752888359127265155579613)
            ·
              refine ⟨657333134672724433342355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1752888359127265155579613 657333134672724433342355)
              ·
                refine ⟨985999702009086650013533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657333134672724433342355 985999702009086650013533)
                ·
                  refine ⟨369749888253407493755075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985999702009086650013533 369749888253407493755075)
                  ·
                    refine ⟨554624832380111240632613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 369749888253407493755075 554624832380111240632613)
                    ·
                      refine ⟨103992156071270857618615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 554624832380111240632613 103992156071270857618615)
                      ·
                        rfl

theorem cell23_202524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_202524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202524 prefixEnd_202524 := by exact prefixLift 202524
  have htrace : WordTrace (prefixWord ++ tailWord_202524) baseStart_202524 baseEnd_202524 := by
    simpa [prefixWord, tailWord_202524, baseEnd_202524] using wordTrace_append hprefix tailTrace_202524
  have hstable : (prefixWord ++ tailWord_202524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202524).length < 2 ^ (prefixWord ++ tailWord_202524).sum := by decide
  have hdescent : baseEnd_202524 < baseStart_202524 := by decide
  rcases family_descends (prefixWord ++ tailWord_202524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202547 : List Nat := [1, 1, 1, 2, 7, 11]
def baseStart_202547 : Nat := 118140960795 + 202547 * 2 ^ 59
def prefixEnd_202547 : Nat := 4983230072969 + 3 ^ 40 * 202547 * 2
def baseEnd_202547 : Nat := 427999860602157479963

theorem tailTrace_202547 : CollatzResearch.WordTrace tailWord_202547 prefixEnd_202547 427999860602157479963 := by
  unfold tailWord_202547
  simp only [CollatzResearch.WordTrace]
  refine ⟨7387495997214286118677895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4924997331476190745785263 7387495997214286118677895)
  ·
    refine ⟨11081243995821429178016843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7387495997214286118677895 11081243995821429178016843)
    ·
      refine ⟨16621865993732143767025265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11081243995821429178016843 16621865993732143767025265)
      ·
        refine ⟨12466399495299107825268949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16621865993732143767025265 12466399495299107825268949)
        ·
          refine ⟨292181238171072839654741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 12466399495299107825268949 292181238171072839654741)
          ·
            refine ⟨427999860602157479963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 292181238171072839654741 427999860602157479963)
            ·
              rfl

theorem cell23_202547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 11].length) (baseStart_202547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202547 prefixEnd_202547 := by exact prefixLift 202547
  have htrace : WordTrace (prefixWord ++ tailWord_202547) baseStart_202547 baseEnd_202547 := by
    simpa [prefixWord, tailWord_202547, baseEnd_202547] using wordTrace_append hprefix tailTrace_202547
  have hstable : (prefixWord ++ tailWord_202547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202547).length < 2 ^ (prefixWord ++ tailWord_202547).sum := by decide
  have hdescent : baseEnd_202547 < baseStart_202547 := by decide
  rcases family_descends (prefixWord ++ tailWord_202547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202567 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_202567 : Nat := 118140960795 + 202567 * 2 ^ 59
def prefixEnd_202567 : Nat := 4983230072969 + 3 ^ 40 * 202567 * 2
def baseEnd_202567 : Nat := 104014235739414189380917

theorem tailTrace_202567 : CollatzResearch.WordTrace tailWord_202567 prefixEnd_202567 104014235739414189380917 := by
  unfold tailWord_202567
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388225457141829534405955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4925483638094553022937303 7388225457141829534405955)
  ·
    refine ⟨11082338185712744301608933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7388225457141829534405955 11082338185712744301608933)
    ·
      refine ⟨2077938409821139556551675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11082338185712744301608933 2077938409821139556551675)
      ·
        refine ⟨3116907614731709334827513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077938409821139556551675 3116907614731709334827513)
        ·
          refine ⟨2337680711048782001120635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3116907614731709334827513 2337680711048782001120635)
          ·
            refine ⟨3506521066573173001680953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337680711048782001120635 3506521066573173001680953)
            ·
              refine ⟨2629890799929879751260715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3506521066573173001680953 2629890799929879751260715)
              ·
                refine ⟨3944836199894819626891073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629890799929879751260715 3944836199894819626891073)
                ·
                  refine ⟨2958627149921114720168305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3944836199894819626891073 2958627149921114720168305)
                  ·
                    refine ⟨2218970362440836040126229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2958627149921114720168305 2218970362440836040126229)
                    ·
                      refine ⟨104014235739414189380917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2218970362440836040126229 104014235739414189380917)
                      ·
                        rfl

theorem cell23_202567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_202567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202567 prefixEnd_202567 := by exact prefixLift 202567
  have htrace : WordTrace (prefixWord ++ tailWord_202567) baseStart_202567 baseEnd_202567 := by
    simpa [prefixWord, tailWord_202567, baseEnd_202567] using wordTrace_append hprefix tailTrace_202567
  have hstable : (prefixWord ++ tailWord_202567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202567).length < 2 ^ (prefixWord ++ tailWord_202567).sum := by decide
  have hdescent : baseEnd_202567 < baseStart_202567 := by decide
  rcases family_descends (prefixWord ++ tailWord_202567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202595 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 1, 2, 3]
def baseStart_202595 : Nat := 118140960795 + 202595 * 2 ^ 59
def prefixEnd_202595 : Nat := 4983230072969 + 3 ^ 40 * 202595 * 2
def baseEnd_202595 : Nat := 104028613197740079830789

theorem tailTrace_202595 : CollatzResearch.WordTrace tailWord_202595 prefixEnd_202595 104028613197740079830789 := by
  unfold tailWord_202595
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389246701040390316425239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4926164467360260210950159 7389246701040390316425239)
  ·
    refine ⟨11083870051560585474637859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7389246701040390316425239 11083870051560585474637859)
    ·
      refine ⟨16625805077340878211956789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11083870051560585474637859 16625805077340878211956789)
      ·
        refine ⟨1558669226000707332370949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16625805077340878211956789 1558669226000707332370949)
        ·
          refine ⟨292250479875132624819553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1558669226000707332370949 292250479875132624819553)
          ·
            refine ⟨219187859906349468614665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292250479875132624819553 219187859906349468614665)
            ·
              refine ⟨164390894929762101460999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219187859906349468614665 164390894929762101460999)
              ·
                refine ⟨246586342394643152191499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164390894929762101460999 246586342394643152191499)
                ·
                  refine ⟨369879513591964728287249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246586342394643152191499 369879513591964728287249)
                  ·
                    refine ⟨277409635193973546215437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 369879513591964728287249 277409635193973546215437)
                    ·
                      refine ⟨104028613197740079830789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 277409635193973546215437 104028613197740079830789)
                      ·
                        rfl

theorem cell23_202595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_202595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202595 prefixEnd_202595 := by exact prefixLift 202595
  have htrace : WordTrace (prefixWord ++ tailWord_202595) baseStart_202595 baseEnd_202595 := by
    simpa [prefixWord, tailWord_202595, baseEnd_202595] using wordTrace_append hprefix tailTrace_202595
  have hstable : (prefixWord ++ tailWord_202595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202595).length < 2 ^ (prefixWord ++ tailWord_202595).sum := by decide
  have hdescent : baseEnd_202595 < baseStart_202595 := by decide
  rcases family_descends (prefixWord ++ tailWord_202595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202602 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_202602 : Nat := 118140960795 + 202602 * 2 ^ 59
def prefixEnd_202602 : Nat := 4983230072969 + 3 ^ 40 * 202602 * 2
def baseEnd_202602 : Nat := 34677402520773850814419

theorem tailTrace_202602 : CollatzResearch.WordTrace tailWord_202602 prefixEnd_202602 34677402520773850814419 := by
  unfold tailWord_202602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847375503003757627982515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4926334674676687007953373 1847375503003757627982515)
  ·
    refine ⟨2771063254505636441973773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1847375503003757627982515 2771063254505636441973773)
    ·
      refine ⟨1039148720439613665740165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2771063254505636441973773 1039148720439613665740165)
      ·
        refine ⟨194840385082427562326281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1039148720439613665740165 194840385082427562326281)
        ·
          refine ⟨146130288811820671744711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194840385082427562326281 146130288811820671744711)
          ·
            refine ⟨219195433217731007617067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146130288811820671744711 219195433217731007617067)
            ·
              refine ⟨328793149826596511425601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219195433217731007617067 328793149826596511425601)
              ·
                refine ⟨246594862369947383569201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328793149826596511425601 246594862369947383569201)
                ·
                  refine ⟨184946146777460537676901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246594862369947383569201 184946146777460537676901)
                  ·
                    refine ⟨34677402520773850814419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184946146777460537676901 34677402520773850814419)
                    ·
                      rfl

theorem cell23_202602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_202602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202602 prefixEnd_202602 := by exact prefixLift 202602
  have htrace : WordTrace (prefixWord ++ tailWord_202602) baseStart_202602 baseEnd_202602 := by
    simpa [prefixWord, tailWord_202602, baseEnd_202602] using wordTrace_append hprefix tailTrace_202602
  have hstable : (prefixWord ++ tailWord_202602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202602).length < 2 ^ (prefixWord ++ tailWord_202602).sum := by decide
  have hdescent : baseEnd_202602 < baseStart_202602 := by decide
  rcases family_descends (prefixWord ++ tailWord_202602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202625 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_202625 : Nat := 118140960795 + 202625 * 2 ^ 59
def prefixEnd_202625 : Nat := 4983230072969 + 3 ^ 40 * 202625 * 2
def baseEnd_202625 : Nat := 104044017617374962455651

theorem tailTrace_202625 : CollatzResearch.WordTrace tailWord_202625 prefixEnd_202625 104044017617374962455651 := by
  unfold tailWord_202625
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390340890931705440017329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4926893927287803626678219 7390340890931705440017329)
  ·
    refine ⟨5542755668198779080012997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7390340890931705440017329 5542755668198779080012997)
    ·
      refine ⟨1039266687787271077502437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5542755668198779080012997 1039266687787271077502437)
      ·
        refine ⟨194862503960113327031707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1039266687787271077502437 194862503960113327031707)
        ·
          refine ⟨292293755940169990547561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194862503960113327031707 292293755940169990547561)
          ·
            refine ⟨219220316955127492910671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292293755940169990547561 219220316955127492910671)
            ·
              refine ⟨328830475432691239366007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219220316955127492910671 328830475432691239366007)
              ·
                refine ⟨493245713149036859049011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328830475432691239366007 493245713149036859049011)
                ·
                  refine ⟨739868569723555288573517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493245713149036859049011 739868569723555288573517)
                  ·
                    refine ⟨277450713646333233215069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 739868569723555288573517 277450713646333233215069)
                    ·
                      refine ⟨104044017617374962455651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 277450713646333233215069 104044017617374962455651)
                      ·
                        rfl

theorem cell23_202625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_202625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202625 prefixEnd_202625 := by exact prefixLift 202625
  have htrace : WordTrace (prefixWord ++ tailWord_202625) baseStart_202625 baseEnd_202625 := by
    simpa [prefixWord, tailWord_202625, baseEnd_202625] using wordTrace_append hprefix tailTrace_202625
  have hstable : (prefixWord ++ tailWord_202625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202625).length < 2 ^ (prefixWord ++ tailWord_202625).sum := by decide
  have hdescent : baseEnd_202625 < baseStart_202625 := by decide
  rcases family_descends (prefixWord ++ tailWord_202625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202676 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_202676 : Nat := 118140960795 + 202676 * 2 ^ 59
def prefixEnd_202676 : Nat := 4983230072969 + 3 ^ 40 * 202676 * 2
def baseEnd_202676 : Nat := 104070205130754262917917

theorem tailTrace_202676 : CollatzResearch.WordTrace tailWord_202676 prefixEnd_202676 104070205130754262917917 := by
  unfold tailWord_202676
  simp only [CollatzResearch.WordTrace]
  refine ⟨3696100506873470575061941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4928134009164627433415921 3696100506873470575061941)
  ·
    refine ⟨346509422519387866412057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3696100506873470575061941 346509422519387866412057)
    ·
      refine ⟨259882066889540899809043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346509422519387866412057 259882066889540899809043)
      ·
        refine ⟨389823100334311349713565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259882066889540899809043 389823100334311349713565)
        ·
          refine ⟨146183662625366756142587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389823100334311349713565 146183662625366756142587)
          ·
            refine ⟨219275493938050134213881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146183662625366756142587 219275493938050134213881)
            ·
              refine ⟨164456620453537600660411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219275493938050134213881 164456620453537600660411)
              ·
                refine ⟨246684930680306400990617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164456620453537600660411 246684930680306400990617)
                ·
                  refine ⟨185013698010229800742963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246684930680306400990617 185013698010229800742963)
                  ·
                    refine ⟨277520547015344701114445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 185013698010229800742963 277520547015344701114445)
                    ·
                      refine ⟨104070205130754262917917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 277520547015344701114445 104070205130754262917917)
                      ·
                        rfl

theorem cell23_202676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_202676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202676 prefixEnd_202676 := by exact prefixLift 202676
  have htrace : WordTrace (prefixWord ++ tailWord_202676) baseStart_202676 baseEnd_202676 := by
    simpa [prefixWord, tailWord_202676, baseEnd_202676] using wordTrace_append hprefix tailTrace_202676
  have hstable : (prefixWord ++ tailWord_202676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202676).length < 2 ^ (prefixWord ++ tailWord_202676).sum := by decide
  have hdescent : baseEnd_202676 < baseStart_202676 := by decide
  rcases family_descends (prefixWord ++ tailWord_202676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202704 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_202704 : Nat := 118140960795 + 202704 * 2 ^ 59
def prefixEnd_202704 : Nat := 4983230072969 + 3 ^ 40 * 202704 * 2
def baseEnd_202704 : Nat := 104084582589080153367787

theorem tailTrace_202704 : CollatzResearch.WordTrace tailWord_202704 prefixEnd_202704 104084582589080153367787 := by
  unfold tailWord_202704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3696611128822750966071583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4928814838430334621428777 3696611128822750966071583)
  ·
    refine ⟨5544916693234126449107375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3696611128822750966071583 5544916693234126449107375)
    ·
      refine ⟨8317375039851189673661063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5544916693234126449107375 8317375039851189673661063)
      ·
        refine ⟨12476062559776784510491595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8317375039851189673661063 12476062559776784510491595)
        ·
          refine ⟨18714093839665176765737393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476062559776784510491595 18714093839665176765737393)
          ·
            refine ⟨14035570379748882574303045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18714093839665176765737393 14035570379748882574303045)
            ·
              refine ⟨2631669446202915482681821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14035570379748882574303045 2631669446202915482681821)
              ·
                refine ⟨986876042326093306005683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631669446202915482681821 986876042326093306005683)
                ·
                  refine ⟨1480314063489139959008525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986876042326093306005683 1480314063489139959008525)
                  ·
                    refine ⟨555117773808427484628197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480314063489139959008525 555117773808427484628197)
                    ·
                      refine ⟨104084582589080153367787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 555117773808427484628197 104084582589080153367787)
                      ·
                        rfl

theorem cell23_202704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_202704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202704 prefixEnd_202704 := by exact prefixLift 202704
  have htrace : WordTrace (prefixWord ++ tailWord_202704) baseStart_202704 baseEnd_202704 := by
    simpa [prefixWord, tailWord_202704, baseEnd_202704] using wordTrace_append hprefix tailTrace_202704
  have hstable : (prefixWord ++ tailWord_202704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202704).length < 2 ^ (prefixWord ++ tailWord_202704).sum := by decide
  have hdescent : baseEnd_202704 < baseStart_202704 := by decide
  rcases family_descends (prefixWord ++ tailWord_202704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202716 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_202716 : Nat := 118140960795 + 202716 * 2 ^ 59
def prefixEnd_202716 : Nat := 4983230072969 + 3 ^ 40 * 202716 * 2
def baseEnd_202716 : Nat := 104090744356934106417733

theorem tailTrace_202716 : CollatzResearch.WordTrace tailWord_202716 prefixEnd_202716 104090744356934106417733 := by
  unfold tailWord_202716
  simp only [CollatzResearch.WordTrace]
  refine ⟨3696829966801013990790001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4929106622401351987720001 3696829966801013990790001)
  ·
    refine ⟨2772622475100760493092501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3696829966801013990790001 2772622475100760493092501)
    ·
      refine ⟨129966678520348148113711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2772622475100760493092501 129966678520348148113711)
      ·
        refine ⟨194950017780522222170567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129966678520348148113711 194950017780522222170567)
        ·
          refine ⟨292425026670783333255851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194950017780522222170567 292425026670783333255851)
          ·
            refine ⟨438637540006174999883777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292425026670783333255851 438637540006174999883777)
            ·
              refine ⟨328978155004631249912833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438637540006174999883777 328978155004631249912833)
              ·
                refine ⟨246733616253473437434625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328978155004631249912833 246733616253473437434625)
                ·
                  refine ⟨185050212190105078075969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246733616253473437434625 185050212190105078075969)
                  ·
                    refine ⟨138787659142578808556977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185050212190105078075969 138787659142578808556977)
                    ·
                      refine ⟨104090744356934106417733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138787659142578808556977 104090744356934106417733)
                      ·
                        rfl

theorem cell23_202716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_202716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202716 prefixEnd_202716 := by exact prefixLift 202716
  have htrace : WordTrace (prefixWord ++ tailWord_202716) baseStart_202716 baseEnd_202716 := by
    simpa [prefixWord, tailWord_202716, baseEnd_202716] using wordTrace_append hprefix tailTrace_202716
  have hstable : (prefixWord ++ tailWord_202716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202716).length < 2 ^ (prefixWord ++ tailWord_202716).sum := by decide
  have hdescent : baseEnd_202716 < baseStart_202716 := by decide
  rcases family_descends (prefixWord ++ tailWord_202716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202721 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_202721 : Nat := 118140960795 + 202721 * 2 ^ 59
def prefixEnd_202721 : Nat := 4983230072969 + 3 ^ 40 * 202721 * 2
def baseEnd_202721 : Nat := 104093311760206586855209

theorem tailTrace_202721 : CollatzResearch.WordTrace tailWord_202721 prefixEnd_202721 104093311760206586855209 := by
  unfold tailWord_202721
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393842298583913835512017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4929228199055942557008011 7393842298583913835512017)
  ·
    refine ⟨5545381723937935376634013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7393842298583913835512017 5545381723937935376634013)
    ·
      refine ⟨2079518146476725766237755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5545381723937935376634013 2079518146476725766237755)
      ·
        refine ⟨3119277219715088649356633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079518146476725766237755 3119277219715088649356633)
        ·
          refine ⟨2339457914786316487017475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119277219715088649356633 2339457914786316487017475)
          ·
            refine ⟨3509186872179474730526213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339457914786316487017475 3509186872179474730526213)
            ·
              refine ⟨657972538533651511973665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3509186872179474730526213 657972538533651511973665)
              ·
                refine ⟨493479403900238633980249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657972538533651511973665 493479403900238633980249)
                ·
                  refine ⟨370109552925178975485187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493479403900238633980249 370109552925178975485187)
                  ·
                    refine ⟨555164329387768463227781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370109552925178975485187 555164329387768463227781)
                    ·
                      refine ⟨104093311760206586855209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 555164329387768463227781 104093311760206586855209)
                      ·
                        rfl

theorem cell23_202721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_202721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202721 prefixEnd_202721 := by exact prefixLift 202721
  have htrace : WordTrace (prefixWord ++ tailWord_202721) baseStart_202721 baseEnd_202721 := by
    simpa [prefixWord, tailWord_202721, baseEnd_202721] using wordTrace_append hprefix tailTrace_202721
  have hstable : (prefixWord ++ tailWord_202721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202721).length < 2 ^ (prefixWord ++ tailWord_202721).sum := by decide
  have hdescent : baseEnd_202721 < baseStart_202721 := by decide
  rcases family_descends (prefixWord ++ tailWord_202721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202724 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_202724 : Nat := 118140960795 + 202724 * 2 ^ 59
def prefixEnd_202724 : Nat := 4983230072969 + 3 ^ 40 * 202724 * 2
def baseEnd_202724 : Nat := 104094852202170075117695

theorem tailTrace_202724 : CollatzResearch.WordTrace tailWord_202724 prefixEnd_202724 104094852202170075117695 := by
  unfold tailWord_202724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3696975858786522673935613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4929301145048696898580817 3696975858786522673935613)
  ·
    refine ⟨1386365947044946002725855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3696975858786522673935613 1386365947044946002725855)
    ·
      refine ⟨2079548920567419004088783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386365947044946002725855 2079548920567419004088783)
      ·
        refine ⟨3119323380851128506133175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079548920567419004088783 3119323380851128506133175)
        ·
          refine ⟨4678985071276692759199763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119323380851128506133175 4678985071276692759199763)
          ·
            refine ⟨7018477606915039138799645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4678985071276692759199763 7018477606915039138799645)
            ·
              refine ⟨2631929102593139677049867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7018477606915039138799645 2631929102593139677049867)
              ·
                refine ⟨3947893653889709515574801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631929102593139677049867 3947893653889709515574801)
                ·
                  refine ⟨2960920240417282136681101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947893653889709515574801 2960920240417282136681101)
                  ·
                    refine ⟨1110345090156480801255413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960920240417282136681101 1110345090156480801255413)
                    ·
                      refine ⟨104094852202170075117695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1110345090156480801255413 104094852202170075117695)
                      ·
                        rfl

theorem cell23_202724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_202724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202724 prefixEnd_202724 := by exact prefixLift 202724
  have htrace : WordTrace (prefixWord ++ tailWord_202724) baseStart_202724 baseEnd_202724 := by
    simpa [prefixWord, tailWord_202724, baseEnd_202724] using wordTrace_append hprefix tailTrace_202724
  have hstable : (prefixWord ++ tailWord_202724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202724).length < 2 ^ (prefixWord ++ tailWord_202724).sum := by decide
  have hdescent : baseEnd_202724 < baseStart_202724 := by decide
  rcases family_descends (prefixWord ++ tailWord_202724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202778 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 6]
def baseStart_202778 : Nat := 118140960795 + 202778 * 2 ^ 59
def prefixEnd_202778 : Nat := 4983230072969 + 3 ^ 40 * 202778 * 2
def baseEnd_202778 : Nat := 11569175573056984871383

theorem tailTrace_202778 : CollatzResearch.WordTrace tailWord_202778 prefixEnd_202778 11569175573056984871383 := by
  unfold tailWord_202778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848980314844353142584247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4930614172918275046891325 1848980314844353142584247)
  ·
    refine ⟨2773470472266529713876371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1848980314844353142584247 2773470472266529713876371)
    ·
      refine ⟨4160205708399794570814557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2773470472266529713876371 4160205708399794570814557)
      ·
        refine ⟨1560077140649922964055459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4160205708399794570814557 1560077140649922964055459)
        ·
          refine ⟨2340115710974884446083189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560077140649922964055459 2340115710974884446083189)
          ·
            refine ⟨219385847903895416820299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2340115710974884446083189 219385847903895416820299)
            ·
              refine ⟨329078771855843125230449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219385847903895416820299 329078771855843125230449)
              ·
                refine ⟨246809078891882343922837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329078771855843125230449 246809078891882343922837)
                ·
                  refine ⟨11569175573056984871383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246809078891882343922837 11569175573056984871383)
                  ·
                    rfl

theorem cell23_202778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_202778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202778 prefixEnd_202778 := by exact prefixLift 202778
  have htrace : WordTrace (prefixWord ++ tailWord_202778) baseStart_202778 baseEnd_202778 := by
    simpa [prefixWord, tailWord_202778, baseEnd_202778] using wordTrace_append hprefix tailTrace_202778
  have hstable : (prefixWord ++ tailWord_202778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202778).length < 2 ^ (prefixWord ++ tailWord_202778).sum := by decide
  have hdescent : baseEnd_202778 < baseStart_202778 := by decide
  rcases family_descends (prefixWord ++ tailWord_202778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202781 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_202781 : Nat := 118140960795 + 202781 * 2 ^ 59
def prefixEnd_202781 : Nat := 4983230072969 + 3 ^ 40 * 202781 * 2
def baseEnd_202781 : Nat := 104124120599476352104933

theorem tailTrace_202781 : CollatzResearch.WordTrace tailWord_202781 prefixEnd_202781 104124120599476352104933 := by
  unfold tailWord_202781
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396030678366544082696197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4930687118911029388464131 7396030678366544082696197)
  ·
    refine ⟨1386755752193727015505537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7396030678366544082696197 1386755752193727015505537)
    ·
      refine ⟨1040066814145295261629153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1386755752193727015505537 1040066814145295261629153)
      ·
        refine ⟨780050110608971446221865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040066814145295261629153 780050110608971446221865)
        ·
          refine ⟨585037582956728584666399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780050110608971446221865 585037582956728584666399)
          ·
            refine ⟨877556374435092876999599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585037582956728584666399 877556374435092876999599)
            ·
              refine ⟨1316334561652639315499399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877556374435092876999599 1316334561652639315499399)
              ·
                refine ⟨1974501842478958973249099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316334561652639315499399 1974501842478958973249099)
                ·
                  refine ⟨2961752763718438459873649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974501842478958973249099 2961752763718438459873649)
                  ·
                    refine ⟨2221314572788828844905237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2961752763718438459873649 2221314572788828844905237)
                    ·
                      refine ⟨104124120599476352104933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2221314572788828844905237 104124120599476352104933)
                      ·
                        rfl

theorem cell23_202781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_202781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202781 prefixEnd_202781 := by exact prefixLift 202781
  have htrace : WordTrace (prefixWord ++ tailWord_202781) baseStart_202781 baseEnd_202781 := by
    simpa [prefixWord, tailWord_202781, baseEnd_202781] using wordTrace_append hprefix tailTrace_202781
  have hstable : (prefixWord ++ tailWord_202781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202781).length < 2 ^ (prefixWord ++ tailWord_202781).sum := by decide
  have hdescent : baseEnd_202781 < baseStart_202781 := by decide
  rcases family_descends (prefixWord ++ tailWord_202781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202828 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_202828 : Nat := 118140960795 + 202828 * 2 ^ 59
def prefixEnd_202828 : Nat := 4983230072969 + 3 ^ 40 * 202828 * 2
def baseEnd_202828 : Nat := 104148254190237668217217

theorem tailTrace_202828 : CollatzResearch.WordTrace tailWord_202828 prefixEnd_202828 104148254190237668217217 := by
  unfold tailWord_202828
  simp only [CollatzResearch.WordTrace]
  refine ⟨3698872454598135554828569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4931829939464180739771425 3698872454598135554828569)
  ·
    refine ⟨2774154340948601666121427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3698872454598135554828569 2774154340948601666121427)
    ·
      refine ⟨4161231511422902499182141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774154340948601666121427 4161231511422902499182141)
      ·
        refine ⟨1560461816783588437193303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4161231511422902499182141 1560461816783588437193303)
        ·
          refine ⟨2340692725175382655789955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560461816783588437193303 2340692725175382655789955)
          ·
            refine ⟨3511039087763073983684933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340692725175382655789955 3511039087763073983684933)
            ·
              refine ⟨658319828955576371940925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3511039087763073983684933 658319828955576371940925)
              ·
                refine ⟨246869935858341139477847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 658319828955576371940925 246869935858341139477847)
                ·
                  refine ⟨370304903787511709216771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246869935858341139477847 370304903787511709216771)
                  ·
                    refine ⟨555457355681267563825157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370304903787511709216771 555457355681267563825157)
                    ·
                      refine ⟨104148254190237668217217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 555457355681267563825157 104148254190237668217217)
                      ·
                        rfl

theorem cell23_202828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_202828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202828 prefixEnd_202828 := by exact prefixLift 202828
  have htrace : WordTrace (prefixWord ++ tailWord_202828) baseStart_202828 baseEnd_202828 := by
    simpa [prefixWord, tailWord_202828, baseEnd_202828] using wordTrace_append hprefix tailTrace_202828
  have hstable : (prefixWord ++ tailWord_202828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202828).length < 2 ^ (prefixWord ++ tailWord_202828).sum := by decide
  have hdescent : baseEnd_202828 < baseStart_202828 := by decide
  rcases family_descends (prefixWord ++ tailWord_202828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202846 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_202846 : Nat := 118140960795 + 202846 * 2 ^ 59
def prefixEnd_202846 : Nat := 4983230072969 + 3 ^ 40 * 202846 * 2
def baseEnd_202846 : Nat := 11573055204668733088015

theorem tailTrace_202846 : CollatzResearch.WordTrace tailWord_202846 prefixEnd_202846 11573055204668733088015 := by
  unfold tailWord_202846
  simp only [CollatzResearch.WordTrace]
  refine ⟨924800177891382522976549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4932267615420706789208261 924800177891382522976549)
  ·
    refine ⟨173400033354634223058103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 924800177891382522976549 173400033354634223058103)
    ·
      refine ⟨260100050031951334587155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173400033354634223058103 260100050031951334587155)
      ·
        refine ⟨390150075047927001880733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260100050031951334587155 390150075047927001880733)
        ·
          refine ⟨146306278142972625705275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390150075047927001880733 146306278142972625705275)
          ·
            refine ⟨219459417214458938557913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146306278142972625705275 219459417214458938557913)
            ·
              refine ⟨164594562910844203918435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219459417214458938557913 164594562910844203918435)
              ·
                refine ⟨246891844366266305877653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164594562910844203918435 246891844366266305877653)
                ·
                  refine ⟨11573055204668733088015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246891844366266305877653 11573055204668733088015)
                  ·
                    rfl

theorem cell23_202846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_202846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202846 prefixEnd_202846 := by exact prefixLift 202846
  have htrace : WordTrace (prefixWord ++ tailWord_202846) baseStart_202846 baseEnd_202846 := by
    simpa [prefixWord, tailWord_202846, baseEnd_202846] using wordTrace_append hprefix tailTrace_202846
  have hstable : (prefixWord ++ tailWord_202846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202846).length < 2 ^ (prefixWord ++ tailWord_202846).sum := by decide
  have hdescent : baseEnd_202846 < baseStart_202846 := by decide
  rcases family_descends (prefixWord ++ tailWord_202846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202901 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_202901 : Nat := 118140960795 + 202901 * 2 ^ 59
def prefixEnd_202901 : Nat := 4983230072969 + 3 ^ 40 * 202901 * 2
def baseEnd_202901 : Nat := 104185738278015882604381

theorem tailTrace_202901 : CollatzResearch.WordTrace tailWord_202901 prefixEnd_202901 104185738278015882604381 := by
  unfold tailWord_202901
  simp only [CollatzResearch.WordTrace]
  refine ⟨7400407437931804577064557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4933604958621203051376371 7400407437931804577064557)
  ·
    refine ⟨2775152789224426716399209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7400407437931804577064557 2775152789224426716399209)
    ·
      refine ⟨2081364591918320037299407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2775152789224426716399209 2081364591918320037299407)
      ·
        refine ⟨3122046887877480055949111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081364591918320037299407 3122046887877480055949111)
        ·
          refine ⟨4683070331816220083923667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122046887877480055949111 4683070331816220083923667)
          ·
            refine ⟨7024605497724330125885501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683070331816220083923667 7024605497724330125885501)
            ·
              refine ⟨2634227061646623797207063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7024605497724330125885501 2634227061646623797207063)
              ·
                refine ⟨3951340592469935695810595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634227061646623797207063 3951340592469935695810595)
                ·
                  refine ⟨5927010888704903543715893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951340592469935695810595 5927010888704903543715893)
                  ·
                    refine ⟨555657270816084707223365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5927010888704903543715893 555657270816084707223365)
                    ·
                      refine ⟨104185738278015882604381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 555657270816084707223365 104185738278015882604381)
                      ·
                        rfl

theorem cell23_202901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_202901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202901 prefixEnd_202901 := by exact prefixLift 202901
  have htrace : WordTrace (prefixWord ++ tailWord_202901) baseStart_202901 baseEnd_202901 := by
    simpa [prefixWord, tailWord_202901, baseEnd_202901] using wordTrace_append hprefix tailTrace_202901
  have hstable : (prefixWord ++ tailWord_202901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202901).length < 2 ^ (prefixWord ++ tailWord_202901).sum := by decide
  have hdescent : baseEnd_202901 < baseStart_202901 := by decide
  rcases family_descends (prefixWord ++ tailWord_202901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202931 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4]
def baseStart_202931 : Nat := 118140960795 + 202931 * 2 ^ 59
def prefixEnd_202931 : Nat := 4983230072969 + 3 ^ 40 * 202931 * 2
def baseEnd_202931 : Nat := 104201142697650765229243

theorem tailTrace_202931 : CollatzResearch.WordTrace tailWord_202931 prefixEnd_202931 104201142697650765229243 := by
  unfold tailWord_202931
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401501627823119700656647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4934334418548746467104431 7401501627823119700656647)
  ·
    refine ⟨11102252441734679550984971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7401501627823119700656647 11102252441734679550984971)
    ·
      refine ⟨16653378662602019326477457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11102252441734679550984971 16653378662602019326477457)
      ·
        refine ⟨12490033996951514494858093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16653378662602019326477457 12490033996951514494858093)
        ·
          refine ⟨4683762748856817935571785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12490033996951514494858093 4683762748856817935571785)
          ·
            refine ⟨3512822061642613451678839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683762748856817935571785 3512822061642613451678839)
            ·
              refine ⟨5269233092463920177518259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512822061642613451678839 5269233092463920177518259)
              ·
                refine ⟨7903849638695880266277389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269233092463920177518259 7903849638695880266277389)
                ·
                  refine ⟨2963943614510955099854021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7903849638695880266277389 2963943614510955099854021)
                  ·
                    refine ⟨555739427720804081222629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2963943614510955099854021 555739427720804081222629)
                    ·
                      refine ⟨104201142697650765229243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 555739427720804081222629 104201142697650765229243)
                      ·
                        rfl

theorem cell23_202931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_202931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202931 prefixEnd_202931 := by exact prefixLift 202931
  have htrace : WordTrace (prefixWord ++ tailWord_202931) baseStart_202931 baseEnd_202931 := by
    simpa [prefixWord, tailWord_202931, baseEnd_202931] using wordTrace_append hprefix tailTrace_202931
  have hstable : (prefixWord ++ tailWord_202931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202931).length < 2 ^ (prefixWord ++ tailWord_202931).sum := by decide
  have hdescent : baseEnd_202931 < baseStart_202931 := by decide
  rcases family_descends (prefixWord ++ tailWord_202931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202935 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 1, 4, 2]
def baseStart_202935 : Nat := 118140960795 + 202935 * 2 ^ 59
def prefixEnd_202935 : Nat := 4983230072969 + 3 ^ 40 * 202935 * 2
def baseEnd_202935 : Nat := 104203196620268749579225

theorem tailTrace_202935 : CollatzResearch.WordTrace tailWord_202935 prefixEnd_202935 104203196620268749579225 := by
  unfold tailWord_202935
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401647519808628383802259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4934431679872418922534839 7401647519808628383802259)
  ·
    refine ⟨11102471279712942575703389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7401647519808628383802259 11102471279712942575703389)
    ·
      refine ⟨4163426729892353465888771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11102471279712942575703389 4163426729892353465888771)
      ·
        refine ⟨6245140094838530198833157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163426729892353465888771 6245140094838530198833157)
        ·
          refine ⟨1170963767782224412281217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6245140094838530198833157 1170963767782224412281217)
          ·
            refine ⟨878222825836668309210913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170963767782224412281217 878222825836668309210913)
            ·
              refine ⟨658667119377501231908185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878222825836668309210913 658667119377501231908185)
              ·
                refine ⟨494000339533125923931139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658667119377501231908185 494000339533125923931139)
                ·
                  refine ⟨741000509299688885896709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494000339533125923931139 741000509299688885896709)
                  ·
                    refine ⟨138937595493691666105633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 741000509299688885896709 138937595493691666105633)
                    ·
                      refine ⟨104203196620268749579225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138937595493691666105633 104203196620268749579225)
                      ·
                        rfl

theorem cell23_202935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_202935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202935 prefixEnd_202935 := by exact prefixLift 202935
  have htrace : WordTrace (prefixWord ++ tailWord_202935) baseStart_202935 baseEnd_202935 := by
    simpa [prefixWord, tailWord_202935, baseEnd_202935] using wordTrace_append hprefix tailTrace_202935
  have hstable : (prefixWord ++ tailWord_202935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202935).length < 2 ^ (prefixWord ++ tailWord_202935).sum := by decide
  have hdescent : baseEnd_202935 < baseStart_202935 := by decide
  rcases family_descends (prefixWord ++ tailWord_202935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202941 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 11]
def baseStart_202941 : Nat := 118140960795 + 202941 * 2 ^ 59
def prefixEnd_202941 : Nat := 4983230072969 + 3 ^ 40 * 202941 * 2
def baseEnd_202941 : Nat := 11578475278243969567133

theorem tailTrace_202941 : CollatzResearch.WordTrace tailWord_202941 prefixEnd_202941 11578475278243969567133 := by
  unfold tailWord_202941
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401866357786891408520677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4934577571857927605680451 7401866357786891408520677)
  ·
    refine ⟨1387849942085042139097627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7401866357786891408520677 1387849942085042139097627)
    ·
      refine ⟨2081774913127563208646441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387849942085042139097627 2081774913127563208646441)
      ·
        refine ⟨1561331184845672406484831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2081774913127563208646441 1561331184845672406484831)
        ·
          refine ⟨2341996777268508609727247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561331184845672406484831 2341996777268508609727247)
          ·
            refine ⟨3512995165902762914590871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341996777268508609727247 3512995165902762914590871)
            ·
              refine ⟨5269492748854144371886307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512995165902762914590871 5269492748854144371886307)
              ·
                refine ⟨7904239123281216557829461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269492748854144371886307 7904239123281216557829461)
                ·
                  refine ⟨11578475278243969567133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 7904239123281216557829461 11578475278243969567133)
                  ·
                    rfl

theorem cell23_202941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_202941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202941 prefixEnd_202941 := by exact prefixLift 202941
  have htrace : WordTrace (prefixWord ++ tailWord_202941) baseStart_202941 baseEnd_202941 := by
    simpa [prefixWord, tailWord_202941, baseEnd_202941] using wordTrace_append hprefix tailTrace_202941
  have hstable : (prefixWord ++ tailWord_202941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202941).length < 2 ^ (prefixWord ++ tailWord_202941).sum := by decide
  have hdescent : baseEnd_202941 < baseStart_202941 := by decide
  rcases family_descends (prefixWord ++ tailWord_202941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202946 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_202946 : Nat := 118140960795 + 202946 * 2 ^ 59
def prefixEnd_202946 : Nat := 4983230072969 + 3 ^ 40 * 202946 * 2
def baseEnd_202946 : Nat := 104208844907468206541675

theorem tailTrace_202946 : CollatzResearch.WordTrace tailWord_202946 prefixEnd_202946 104208844907468206541675 := by
  unfold tailWord_202946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850512180692194315613173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4934699148512518174968461 1850512180692194315613173)
  ·
    refine ⟨173485516939893217088735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1850512180692194315613173 173485516939893217088735)
    ·
      refine ⟨260228275409839825633103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173485516939893217088735 260228275409839825633103)
      ·
        refine ⟨390342413114759738449655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260228275409839825633103 390342413114759738449655)
        ·
          refine ⟨585513619672139607674483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390342413114759738449655 585513619672139607674483)
          ·
            refine ⟨878270429508209411511725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585513619672139607674483 878270429508209411511725)
            ·
              refine ⟨329351411065578529316897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 878270429508209411511725 329351411065578529316897)
              ·
                refine ⟨247013558299183896987673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329351411065578529316897 247013558299183896987673)
                ·
                  refine ⟨185260168724387922740755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247013558299183896987673 185260168724387922740755)
                  ·
                    refine ⟨277890253086581884111133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 185260168724387922740755 277890253086581884111133)
                    ·
                      refine ⟨104208844907468206541675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 277890253086581884111133 104208844907468206541675)
                      ·
                        rfl

theorem cell23_202946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_202946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202946 prefixEnd_202946 := by exact prefixLift 202946
  have htrace : WordTrace (prefixWord ++ tailWord_202946) baseStart_202946 baseEnd_202946 := by
    simpa [prefixWord, tailWord_202946, baseEnd_202946] using wordTrace_append hprefix tailTrace_202946
  have hstable : (prefixWord ++ tailWord_202946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202946).length < 2 ^ (prefixWord ++ tailWord_202946).sum := by decide
  have hdescent : baseEnd_202946 < baseStart_202946 := by decide
  rcases family_descends (prefixWord ++ tailWord_202946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202958 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_202958 : Nat := 118140960795 + 202958 * 2 ^ 59
def prefixEnd_202958 : Nat := 4983230072969 + 3 ^ 40 * 202958 * 2
def baseEnd_202958 : Nat := 11579445186146906621291

theorem tailTrace_202958 : CollatzResearch.WordTrace tailWord_202958 prefixEnd_202958 11579445186146906621291 := by
  unfold tailWord_202958
  simp only [CollatzResearch.WordTrace]
  refine ⟨925310799840662913986191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4934990932483535541259685 925310799840662913986191)
  ·
    refine ⟨1387966199760994370979287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 925310799840662913986191 1387966199760994370979287)
    ·
      refine ⟨2081949299641491556468931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387966199760994370979287 2081949299641491556468931)
      ·
        refine ⟨3122923949462237334703397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081949299641491556468931 3122923949462237334703397)
        ·
          refine ⟨585548240524169500256887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3122923949462237334703397 585548240524169500256887)
          ·
            refine ⟨878322360786254250385331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585548240524169500256887 878322360786254250385331)
            ·
              refine ⟨1317483541179381375577997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878322360786254250385331 1317483541179381375577997)
              ·
                refine ⟨494056327942268015841749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1317483541179381375577997 494056327942268015841749)
                ·
                  refine ⟨11579445186146906621291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 494056327942268015841749 11579445186146906621291)
                  ·
                    rfl

theorem cell23_202958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_202958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202958 prefixEnd_202958 := by exact prefixLift 202958
  have htrace : WordTrace (prefixWord ++ tailWord_202958) baseStart_202958 baseEnd_202958 := by
    simpa [prefixWord, tailWord_202958, baseEnd_202958] using wordTrace_append hprefix tailTrace_202958
  have hstable : (prefixWord ++ tailWord_202958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202958).length < 2 ^ (prefixWord ++ tailWord_202958).sum := by decide
  have hdescent : baseEnd_202958 < baseStart_202958 := by decide
  rcases family_descends (prefixWord ++ tailWord_202958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202971 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 1, 7]
def baseStart_202971 : Nat := 118140960795 + 202971 * 2 ^ 59
def prefixEnd_202971 : Nat := 4983230072969 + 3 ^ 40 * 202971 * 2
def baseEnd_202971 : Nat := 34740560641276869576353

theorem tailTrace_202971 : CollatzResearch.WordTrace tailWord_202971 prefixEnd_202971 34740560641276869576353 := by
  unfold tailWord_202971
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402960547678206532112767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4935307031785471021408511 7402960547678206532112767)
  ·
    refine ⟨11104440821517309798169151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7402960547678206532112767 11104440821517309798169151)
    ·
      refine ⟨16656661232275964697253727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11104440821517309798169151 16656661232275964697253727)
      ·
        refine ⟨24984991848413947045880591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16656661232275964697253727 24984991848413947045880591)
        ·
          refine ⟨37477487772620920568820887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24984991848413947045880591 37477487772620920568820887)
          ·
            refine ⟨56216231658931380853231331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37477487772620920568820887 56216231658931380853231331)
            ·
              refine ⟨84324347488397071279846997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56216231658931380853231331 84324347488397071279846997)
              ·
                refine ⟨988175947129653179060707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 84324347488397071279846997 988175947129653179060707)
                ·
                  refine ⟨1482263920694479768591061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988175947129653179060707 1482263920694479768591061)
                  ·
                    refine ⟨34740560641276869576353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1482263920694479768591061 34740560641276869576353)
                    ·
                      rfl

theorem cell23_202971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 7].length) (baseStart_202971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202971 prefixEnd_202971 := by exact prefixLift 202971
  have htrace : WordTrace (prefixWord ++ tailWord_202971) baseStart_202971 baseEnd_202971 := by
    simpa [prefixWord, tailWord_202971, baseEnd_202971] using wordTrace_append hprefix tailTrace_202971
  have hstable : (prefixWord ++ tailWord_202971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202971).length < 2 ^ (prefixWord ++ tailWord_202971).sum := by decide
  have hdescent : baseEnd_202971 < baseStart_202971 := by decide
  rcases family_descends (prefixWord ++ tailWord_202971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202988 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_202988 : Nat := 118140960795 + 202988 * 2 ^ 59
def prefixEnd_202988 : Nat := 4983230072969 + 3 ^ 40 * 202988 * 2
def baseEnd_202988 : Nat := 34743470364985680738827

theorem tailTrace_202988 : CollatzResearch.WordTrace tailWord_202988 prefixEnd_202988 34743470364985680738827 := by
  unfold tailWord_202988
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701790294308309217740809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4935720392411078956987745 3701790294308309217740809)
  ·
    refine ⟨2776342720731231913305607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3701790294308309217740809 2776342720731231913305607)
    ·
      refine ⟨4164514081096847869958411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776342720731231913305607 4164514081096847869958411)
      ·
        refine ⟨6246771121645271804937617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164514081096847869958411 6246771121645271804937617)
        ·
          refine ⟨4685078341233953853703213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6246771121645271804937617 4685078341233953853703213)
          ·
            refine ⟨1756904377962732695138705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4685078341233953853703213 1756904377962732695138705)
            ·
              refine ⟨1317678283472049521354029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756904377962732695138705 1317678283472049521354029)
              ·
                refine ⟨494129356302018570507761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1317678283472049521354029 494129356302018570507761)
                ·
                  refine ⟨370597017226513927880821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494129356302018570507761 370597017226513927880821)
                  ·
                    refine ⟨34743470364985680738827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 370597017226513927880821 34743470364985680738827)
                    ·
                      rfl

theorem cell23_202988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_202988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202988 prefixEnd_202988 := by exact prefixLift 202988
  have htrace : WordTrace (prefixWord ++ tailWord_202988) baseStart_202988 baseEnd_202988 := by
    simpa [prefixWord, tailWord_202988, baseEnd_202988] using wordTrace_append hprefix tailTrace_202988
  have hstable : (prefixWord ++ tailWord_202988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202988).length < 2 ^ (prefixWord ++ tailWord_202988).sum := by decide
  have hdescent : baseEnd_202988 < baseStart_202988 := by decide
  rcases family_descends (prefixWord ++ tailWord_202988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203008 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_203008 : Nat := 118140960795 + 203008 * 2 ^ 59
def prefixEnd_203008 : Nat := 4983230072969 + 3 ^ 40 * 203008 * 2
def baseEnd_203008 : Nat := 104240680708046963966389

theorem tailTrace_203008 : CollatzResearch.WordTrace tailWord_203008 prefixEnd_203008 104240680708046963966389 := by
  unfold tailWord_203008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3702155024272080925604839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4936206699029441234139785 3702155024272080925604839)
  ·
    refine ⟨5553232536408121388407259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3702155024272080925604839 5553232536408121388407259)
    ·
      refine ⟨8329848804612182082610889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5553232536408121388407259 8329848804612182082610889)
      ·
        refine ⟨6247386603459136561958167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8329848804612182082610889 6247386603459136561958167)
        ·
          refine ⟨9371079905188704842937251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247386603459136561958167 9371079905188704842937251)
          ·
            refine ⟨14056619857783057264405877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371079905188704842937251 14056619857783057264405877)
            ·
              refine ⟨1317808111667161618538051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14056619857783057264405877 1317808111667161618538051)
              ·
                refine ⟨1976712167500742427807077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317808111667161618538051 1976712167500742427807077)
                ·
                  refine ⟨370633531406389205213827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976712167500742427807077 370633531406389205213827)
                  ·
                    refine ⟨555950297109583807820741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370633531406389205213827 555950297109583807820741)
                    ·
                      refine ⟨104240680708046963966389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 555950297109583807820741 104240680708046963966389)
                      ·
                        rfl

theorem cell23_203008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_203008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203008 prefixEnd_203008 := by exact prefixLift 203008
  have htrace : WordTrace (prefixWord ++ tailWord_203008) baseStart_203008 baseEnd_203008 := by
    simpa [prefixWord, tailWord_203008, baseEnd_203008] using wordTrace_append hprefix tailTrace_203008
  have hstable : (prefixWord ++ tailWord_203008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203008).length < 2 ^ (prefixWord ++ tailWord_203008).sum := by decide
  have hdescent : baseEnd_203008 < baseStart_203008 := by decide
  rcases family_descends (prefixWord ++ tailWord_203008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203042 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_203042 : Nat := 118140960795 + 203042 * 2 ^ 59
def prefixEnd_203042 : Nat := 4983230072969 + 3 ^ 40 * 203042 * 2
def baseEnd_203042 : Nat := 104258139050299830941233

theorem tailTrace_203042 : CollatzResearch.WordTrace tailWord_203042 prefixEnd_203042 104258139050299830941233 := by
  unfold tailWord_203042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851387532605246414486845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4937033420280657105298253 1851387532605246414486845)
  ·
    refine ⟨694270324726967405432567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1851387532605246414486845 694270324726967405432567)
    ·
      refine ⟨1041405487090451108148851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694270324726967405432567 1041405487090451108148851)
      ·
        refine ⟨1562108230635676662223277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041405487090451108148851 1562108230635676662223277)
        ·
          refine ⟨585790586488378748333729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1562108230635676662223277 585790586488378748333729)
          ·
            refine ⟨439342939866284061250297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585790586488378748333729 439342939866284061250297)
            ·
              refine ⟨329507204899713045937723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439342939866284061250297 329507204899713045937723)
              ·
                refine ⟨494260807349569568906585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329507204899713045937723 494260807349569568906585)
                ·
                  refine ⟨370695605512177176679939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494260807349569568906585 370695605512177176679939)
                  ·
                    refine ⟨556043408268265765019909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370695605512177176679939 556043408268265765019909)
                    ·
                      refine ⟨104258139050299830941233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 556043408268265765019909 104258139050299830941233)
                      ·
                        rfl

theorem cell23_203042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_203042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203042 prefixEnd_203042 := by exact prefixLift 203042
  have htrace : WordTrace (prefixWord ++ tailWord_203042) baseStart_203042 baseEnd_203042 := by
    simpa [prefixWord, tailWord_203042, baseEnd_203042] using wordTrace_append hprefix tailTrace_203042
  have hstable : (prefixWord ++ tailWord_203042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203042).length < 2 ^ (prefixWord ++ tailWord_203042).sum := by decide
  have hdescent : baseEnd_203042 < baseStart_203042 := by decide
  rcases family_descends (prefixWord ++ tailWord_203042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203065 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 6]
def baseStart_203065 : Nat := 118140960795 + 203065 * 2 ^ 59
def prefixEnd_203065 : Nat := 4983230072969 + 3 ^ 40 * 203065 * 2
def baseEnd_203065 : Nat := 11585549900594804550403

theorem tailTrace_203065 : CollatzResearch.WordTrace tailWord_203065 prefixEnd_203065 11585549900594804550403 := by
  unfold tailWord_203065
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406389009337660586034649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4937592672891773724023099 7406389009337660586034649)
  ·
    refine ⟨5554791757003245439525987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7406389009337660586034649 5554791757003245439525987)
    ·
      refine ⟨8332187635504868159288981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554791757003245439525987 8332187635504868159288981)
      ·
        refine ⟨390571295414290694966671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8332187635504868159288981 390571295414290694966671)
        ·
          refine ⟨585856943121436042450007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390571295414290694966671 585856943121436042450007)
          ·
            refine ⟨878785414682154063675011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585856943121436042450007 878785414682154063675011)
            ·
              refine ⟨1318178122023231095512517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878785414682154063675011 1318178122023231095512517)
              ·
                refine ⟨247158397879355830408597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1318178122023231095512517 247158397879355830408597)
                ·
                  refine ⟨11585549900594804550403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247158397879355830408597 11585549900594804550403)
                  ·
                    rfl

theorem cell23_203065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 6].length) (baseStart_203065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203065 prefixEnd_203065 := by exact prefixLift 203065
  have htrace : WordTrace (prefixWord ++ tailWord_203065) baseStart_203065 baseEnd_203065 := by
    simpa [prefixWord, tailWord_203065, baseEnd_203065] using wordTrace_append hprefix tailTrace_203065
  have hstable : (prefixWord ++ tailWord_203065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203065).length < 2 ^ (prefixWord ++ tailWord_203065).sum := by decide
  have hdescent : baseEnd_203065 < baseStart_203065 := by decide
  rcases family_descends (prefixWord ++ tailWord_203065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203068 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_203068 : Nat := 118140960795 + 203068 * 2 ^ 59
def prefixEnd_203068 : Nat := 4983230072969 + 3 ^ 40 * 203068 * 2
def baseEnd_203068 : Nat := 104271489547316729216113

theorem tailTrace_203068 : CollatzResearch.WordTrace tailWord_203068 prefixEnd_203068 104271489547316729216113 := by
  unfold tailWord_203068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703249214163396049196929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4937665618884528065595905 3703249214163396049196929)
  ·
    refine ⟨2777436910622547036897697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3703249214163396049196929 2777436910622547036897697)
    ·
      refine ⟨2083077682966910277673273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2777436910622547036897697 2083077682966910277673273)
      ·
        refine ⟨1562308262225182708254955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2083077682966910277673273 1562308262225182708254955)
        ·
          refine ⟨2343462393337774062382433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562308262225182708254955 2343462393337774062382433)
          ·
            refine ⟨1757596795003330546786825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343462393337774062382433 1757596795003330546786825)
            ·
              refine ⟨1318197596252497910090119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757596795003330546786825 1318197596252497910090119)
              ·
                refine ⟨1977296394378746865135179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318197596252497910090119 1977296394378746865135179)
                ·
                  refine ⟨2965944591568120297702769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977296394378746865135179 2965944591568120297702769)
                  ·
                    refine ⟨2224458443676090223277077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965944591568120297702769 2224458443676090223277077)
                    ·
                      refine ⟨104271489547316729216113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2224458443676090223277077 104271489547316729216113)
                      ·
                        rfl

theorem cell23_203068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_203068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203068 prefixEnd_203068 := by exact prefixLift 203068
  have htrace : WordTrace (prefixWord ++ tailWord_203068) baseStart_203068 baseEnd_203068 := by
    simpa [prefixWord, tailWord_203068, baseEnd_203068] using wordTrace_append hprefix tailTrace_203068
  have hstable : (prefixWord ++ tailWord_203068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203068).length < 2 ^ (prefixWord ++ tailWord_203068).sum := by decide
  have hdescent : baseEnd_203068 < baseStart_203068 := by decide
  rcases family_descends (prefixWord ++ tailWord_203068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203092 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_203092 : Nat := 118140960795 + 203092 * 2 ^ 59
def prefixEnd_203092 : Nat := 4983230072969 + 3 ^ 40 * 203092 * 2
def baseEnd_203092 : Nat := 104283813083024635316003

theorem tailTrace_203092 : CollatzResearch.WordTrace tailWord_203092 prefixEnd_203092 104283813083024635316003 := by
  unfold tailWord_203092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703686890119922098633765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4938249186826562798178353 3703686890119922098633765)
  ·
    refine ⟨694441291897485393493831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3703686890119922098633765 694441291897485393493831)
    ·
      refine ⟨1041661937846228090240747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694441291897485393493831 1041661937846228090240747)
      ·
        refine ⟨1562492906769342135361121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041661937846228090240747 1562492906769342135361121)
        ·
          refine ⟨1171869680077006601520841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562492906769342135361121 1171869680077006601520841)
          ·
            refine ⟨878902260057754951140631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171869680077006601520841 878902260057754951140631)
            ·
              refine ⟨1318353390086632426710947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878902260057754951140631 1318353390086632426710947)
              ·
                refine ⟨1977530085129948640066421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318353390086632426710947 1977530085129948640066421)
                ·
                  refine ⟨185393445480932685006227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1977530085129948640066421 185393445480932685006227)
                  ·
                    refine ⟨278090168221399027509341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 185393445480932685006227 278090168221399027509341)
                    ·
                      refine ⟨104283813083024635316003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 278090168221399027509341 104283813083024635316003)
                      ·
                        rfl

theorem cell23_203092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_203092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203092 prefixEnd_203092 := by exact prefixLift 203092
  have htrace : WordTrace (prefixWord ++ tailWord_203092) baseStart_203092 baseEnd_203092 := by
    simpa [prefixWord, tailWord_203092, baseEnd_203092] using wordTrace_append hprefix tailTrace_203092
  have hstable : (prefixWord ++ tailWord_203092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203092).length < 2 ^ (prefixWord ++ tailWord_203092).sum := by decide
  have hdescent : baseEnd_203092 < baseStart_203092 := by decide
  rcases family_descends (prefixWord ++ tailWord_203092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203095 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 1, 5]
def baseStart_203095 : Nat := 118140960795 + 203095 * 2 ^ 59
def prefixEnd_203095 : Nat := 4983230072969 + 3 ^ 40 * 203095 * 2
def baseEnd_203095 : Nat := 34761784508329374526163

theorem tailTrace_203095 : CollatzResearch.WordTrace tailWord_203095 prefixEnd_203095 34761784508329374526163 := by
  unfold tailWord_203095
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407483199228975709626739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4938322132819317139751159 7407483199228975709626739)
  ·
    refine ⟨11111224798843463564440109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7407483199228975709626739 11111224798843463564440109)
    ·
      refine ⟨4166709299566298836665041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11111224798843463564440109 4166709299566298836665041)
      ·
        refine ⟨3125031974674724127498781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4166709299566298836665041 3125031974674724127498781)
        ·
          refine ⟨1171886990503021547812043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3125031974674724127498781 1171886990503021547812043)
          ·
            refine ⟨1757830485754532321718065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171886990503021547812043 1757830485754532321718065)
            ·
              refine ⟨1318372864315899241288549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757830485754532321718065 1318372864315899241288549)
              ·
                refine ⟨247194912059231107741603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1318372864315899241288549 247194912059231107741603)
                ·
                  refine ⟨370792368088846661612405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247194912059231107741603 370792368088846661612405)
                  ·
                    refine ⟨34761784508329374526163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 370792368088846661612405 34761784508329374526163)
                    ·
                      rfl

theorem cell23_203095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_203095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203095 prefixEnd_203095 := by exact prefixLift 203095
  have htrace : WordTrace (prefixWord ++ tailWord_203095) baseStart_203095 baseEnd_203095 := by
    simpa [prefixWord, tailWord_203095, baseEnd_203095] using wordTrace_append hprefix tailTrace_203095
  have hstable : (prefixWord ++ tailWord_203095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203095).length < 2 ^ (prefixWord ++ tailWord_203095).sum := by decide
  have hdescent : baseEnd_203095 < baseStart_203095 := by decide
  rcases family_descends (prefixWord ++ tailWord_203095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203109 : List Nat := [1, 3, 1, 3, 1, 3, 1, 5, 1, 1, 3]
def baseStart_203109 : Nat := 118140960795 + 203109 * 2 ^ 59
def prefixEnd_203109 : Nat := 4983230072969 + 3 ^ 40 * 203109 * 2
def baseEnd_203109 : Nat := 104292542254151068803425

theorem tailTrace_203109 : CollatzResearch.WordTrace tailWord_203109 prefixEnd_203109 104292542254151068803425 := by
  unfold tailWord_203109
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407993821178256100636381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4938662547452170733757587 7407993821178256100636381)
  ·
    refine ⟨2777997682941846037738643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7407993821178256100636381 2777997682941846037738643)
    ·
      refine ⟨4166996524412769056607965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2777997682941846037738643 4166996524412769056607965)
      ·
        refine ⟨1562623696654788396227987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4166996524412769056607965 1562623696654788396227987)
        ·
          refine ⟨2343935544982182594341981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562623696654788396227987 2343935544982182594341981)
          ·
            refine ⟨878975829368318472878243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2343935544982182594341981 878975829368318472878243)
            ·
              refine ⟨1318463744052477709317365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878975829368318472878243 1318463744052477709317365)
              ·
                refine ⟨123605976004919785248503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1318463744052477709317365 123605976004919785248503)
                ·
                  refine ⟨185408964007379677872755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123605976004919785248503 185408964007379677872755)
                  ·
                    refine ⟨278113446011069516809133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 185408964007379677872755 278113446011069516809133)
                    ·
                      refine ⟨104292542254151068803425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 278113446011069516809133 104292542254151068803425)
                      ·
                        rfl

theorem cell23_203109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_203109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203109 prefixEnd_203109 := by exact prefixLift 203109
  have htrace : WordTrace (prefixWord ++ tailWord_203109) baseStart_203109 baseEnd_203109 := by
    simpa [prefixWord, tailWord_203109, baseEnd_203109] using wordTrace_append hprefix tailTrace_203109
  have hstable : (prefixWord ++ tailWord_203109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203109).length < 2 ^ (prefixWord ++ tailWord_203109).sum := by decide
  have hdescent : baseEnd_203109 < baseStart_203109 := by decide
  rcases family_descends (prefixWord ++ tailWord_203109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203112 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 1, 5]
def baseStart_203112 : Nat := 118140960795 + 203112 * 2 ^ 59
def prefixEnd_203112 : Nat := 4983230072969 + 3 ^ 40 * 203112 * 2
def baseEnd_203112 : Nat := 34764694232038185688637

theorem tailTrace_203112 : CollatzResearch.WordTrace tailWord_203112 prefixEnd_203112 34764694232038185688637 := by
  unfold tailWord_203112
  simp only [CollatzResearch.WordTrace]
  refine ⟨3704051620083693806497795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4938735493444925075330393 3704051620083693806497795)
  ·
    refine ⟨5556077430125540709746693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3704051620083693806497795 5556077430125540709746693)
    ·
      refine ⟨1041764518148538883077505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5556077430125540709746693 1041764518148538883077505)
      ·
        refine ⟨781323388611404162308129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1041764518148538883077505 781323388611404162308129)
        ·
          refine ⟨585992541458553121731097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781323388611404162308129 585992541458553121731097)
          ·
            refine ⟨439494406093914841298323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585992541458553121731097 439494406093914841298323)
            ·
              refine ⟨659241609140872261947485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439494406093914841298323 659241609140872261947485)
              ·
                refine ⟨247215603427827098230307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 659241609140872261947485 247215603427827098230307)
                ·
                  refine ⟨370823405141740647345461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247215603427827098230307 370823405141740647345461)
                  ·
                    refine ⟨34764694232038185688637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 370823405141740647345461 34764694232038185688637)
                    ·
                      rfl

theorem cell23_203112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_203112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203112 prefixEnd_203112 := by exact prefixLift 203112
  have htrace : WordTrace (prefixWord ++ tailWord_203112) baseStart_203112 baseEnd_203112 := by
    simpa [prefixWord, tailWord_203112, baseEnd_203112] using wordTrace_append hprefix tailTrace_203112
  have hstable : (prefixWord ++ tailWord_203112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203112).length < 2 ^ (prefixWord ++ tailWord_203112).sum := by decide
  have hdescent : baseEnd_203112 < baseStart_203112 := by decide
  rcases family_descends (prefixWord ++ tailWord_203112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203115 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 4]
def baseStart_203115 : Nat := 118140960795 + 203115 * 2 ^ 59
def prefixEnd_203115 : Nat := 4983230072969 + 3 ^ 40 * 203115 * 2
def baseEnd_203115 : Nat := 104295623138078045328397

theorem tailTrace_203115 : CollatzResearch.WordTrace tailWord_203115 prefixEnd_203115 104295623138078045328397 := by
  unfold tailWord_203115
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408212659156519125354799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4938808439437679416903199 7408212659156519125354799)
  ·
    refine ⟨11112318988734778688032199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7408212659156519125354799 11112318988734778688032199)
    ·
      refine ⟨16668478483102168032048299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11112318988734778688032199 16668478483102168032048299)
      ·
        refine ⟨25002717724653252048072449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16668478483102168032048299 25002717724653252048072449)
        ·
          refine ⟨18752038293489939036054337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25002717724653252048072449 18752038293489939036054337)
          ·
            refine ⟨14064028720117454277040753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18752038293489939036054337 14064028720117454277040753)
            ·
              refine ⟨10548021540088090707780565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14064028720117454277040753 10548021540088090707780565)
              ·
                refine ⟨247219254845814625963607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10548021540088090707780565 247219254845814625963607)
                ·
                  refine ⟨370828882268721938945411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247219254845814625963607 370828882268721938945411)
                  ·
                    refine ⟨556243323403082908418117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370828882268721938945411 556243323403082908418117)
                    ·
                      refine ⟨104295623138078045328397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 556243323403082908418117 104295623138078045328397)
                      ·
                        rfl

theorem cell23_203115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 4].length) (baseStart_203115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203115 prefixEnd_203115 := by exact prefixLift 203115
  have htrace : WordTrace (prefixWord ++ tailWord_203115) baseStart_203115 baseEnd_203115 := by
    simpa [prefixWord, tailWord_203115, baseEnd_203115] using wordTrace_append hprefix tailTrace_203115
  have hstable : (prefixWord ++ tailWord_203115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203115).length < 2 ^ (prefixWord ++ tailWord_203115).sum := by decide
  have hdescent : baseEnd_203115 < baseStart_203115 := by decide
  rcases family_descends (prefixWord ++ tailWord_203115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203128 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_203128 : Nat := 118140960795 + 203128 * 2 ^ 59
def prefixEnd_203128 : Nat := 4983230072969 + 3 ^ 40 * 203128 * 2
def baseEnd_203128 : Nat := 104302298386586494465837

theorem tailTrace_203128 : CollatzResearch.WordTrace tailWord_203128 prefixEnd_203128 104302298386586494465837 := by
  unfold tailWord_203128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3704343404054711172789019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4939124538739614897052025 3704343404054711172789019)
  ·
    refine ⟨5556515106082066759183529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3704343404054711172789019 5556515106082066759183529)
    ·
      refine ⟨4167386329561550069387647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5556515106082066759183529 4167386329561550069387647)
      ·
        refine ⟨6251079494342325104081471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4167386329561550069387647 6251079494342325104081471)
        ·
          refine ⟨9376619241513487656122207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6251079494342325104081471 9376619241513487656122207)
          ·
            refine ⟨14064928862270231484183311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9376619241513487656122207 14064928862270231484183311)
            ·
              refine ⟨21097393293405347226274967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14064928862270231484183311 21097393293405347226274967)
              ·
                refine ⟨31646089940108020839412451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21097393293405347226274967 31646089940108020839412451)
                ·
                  refine ⟨47469134910162031259118677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31646089940108020839412451 47469134910162031259118677)
                  ·
                    refine ⟨556278924728461303817797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47469134910162031259118677 556278924728461303817797)
                    ·
                      refine ⟨104302298386586494465837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 556278924728461303817797 104302298386586494465837)
                      ·
                        rfl

theorem cell23_203128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_203128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203128 prefixEnd_203128 := by exact prefixLift 203128
  have htrace : WordTrace (prefixWord ++ tailWord_203128) baseStart_203128 baseEnd_203128 := by
    simpa [prefixWord, tailWord_203128, baseEnd_203128] using wordTrace_append hprefix tailTrace_203128
  have hstable : (prefixWord ++ tailWord_203128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203128).length < 2 ^ (prefixWord ++ tailWord_203128).sum := by decide
  have hdescent : baseEnd_203128 < baseStart_203128 := by decide
  rcases family_descends (prefixWord ++ tailWord_203128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203145 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_203145 : Nat := 118140960795 + 203145 * 2 ^ 59
def prefixEnd_203145 : Nat := 4983230072969 + 3 ^ 40 * 203145 * 2
def baseEnd_203145 : Nat := 104311027557712927953259

theorem tailTrace_203145 : CollatzResearch.WordTrace tailWord_203145 prefixEnd_203145 104311027557712927953259 := by
  unfold tailWord_203145
  simp only [CollatzResearch.WordTrace]
  refine ⟨7409306849047834248946889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4939537899365222832631259 7409306849047834248946889)
  ·
    refine ⟨5556980136785875686710167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7409306849047834248946889 5556980136785875686710167)
    ·
      refine ⟨8335470205178813530065251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5556980136785875686710167 8335470205178813530065251)
      ·
        refine ⟨12503205307768220295097877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8335470205178813530065251 12503205307768220295097877)
        ·
          refine ⟨586087748801635326332713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12503205307768220295097877 586087748801635326332713)
          ·
            refine ⟨439565811601226494749535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586087748801635326332713 439565811601226494749535)
            ·
              refine ⟨659348717401839742124303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439565811601226494749535 659348717401839742124303)
              ·
                refine ⟨989023076102759613186455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659348717401839742124303 989023076102759613186455)
                ·
                  refine ⟨1483534614154139419779683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989023076102759613186455 1483534614154139419779683)
                  ·
                    refine ⟨2225301921231209129669525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1483534614154139419779683 2225301921231209129669525)
                    ·
                      refine ⟨104311027557712927953259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2225301921231209129669525 104311027557712927953259)
                      ·
                        rfl

theorem cell23_203145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_203145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203145 prefixEnd_203145 := by exact prefixLift 203145
  have htrace : WordTrace (prefixWord ++ tailWord_203145) baseStart_203145 baseEnd_203145 := by
    simpa [prefixWord, tailWord_203145, baseEnd_203145] using wordTrace_append hprefix tailTrace_203145
  have hstable : (prefixWord ++ tailWord_203145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203145).length < 2 ^ (prefixWord ++ tailWord_203145).sum := by decide
  have hdescent : baseEnd_203145 < baseStart_203145 := by decide
  rcases family_descends (prefixWord ++ tailWord_203145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203169 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_203169 : Nat := 118140960795 + 203169 * 2 ^ 59
def prefixEnd_203169 : Nat := 4983230072969 + 3 ^ 40 * 203169 * 2
def baseEnd_203169 : Nat := 104323351093420834053149

theorem tailTrace_203169 : CollatzResearch.WordTrace tailWord_203169 prefixEnd_203169 104323351093420834053149 := by
  unfold tailWord_203169
  simp only [CollatzResearch.WordTrace]
  refine ⟨7410182200960886347820561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4940121467307257565213707 7410182200960886347820561)
  ·
    refine ⟨5557636650720664760865421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7410182200960886347820561 5557636650720664760865421)
    ·
      refine ⟨2084113744020249285324533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5557636650720664760865421 2084113744020249285324533)
      ·
        refine ⟨195385663501898370499175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2084113744020249285324533 195385663501898370499175)
        ·
          refine ⟨293078495252847555748763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195385663501898370499175 293078495252847555748763)
          ·
            refine ⟨439617742879271333623145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293078495252847555748763 439617742879271333623145)
            ·
              refine ⟨329713307159453500217359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439617742879271333623145 329713307159453500217359)
              ·
                refine ⟨494569960739180250326039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329713307159453500217359 494569960739180250326039)
                ·
                  refine ⟨741854941108770375489059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494569960739180250326039 741854941108770375489059)
                  ·
                    refine ⟨1112782411663155563233589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741854941108770375489059 1112782411663155563233589)
                    ·
                      refine ⟨104323351093420834053149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1112782411663155563233589 104323351093420834053149)
                      ·
                        rfl

theorem cell23_203169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_203169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203169 prefixEnd_203169 := by exact prefixLift 203169
  have htrace : WordTrace (prefixWord ++ tailWord_203169) baseStart_203169 baseEnd_203169 := by
    simpa [prefixWord, tailWord_203169, baseEnd_203169] using wordTrace_append hprefix tailTrace_203169
  have hstable : (prefixWord ++ tailWord_203169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203169).length < 2 ^ (prefixWord ++ tailWord_203169).sum := by decide
  have hdescent : baseEnd_203169 < baseStart_203169 := by decide
  rcases family_descends (prefixWord ++ tailWord_203169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203192 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 3, 3, 2]
def baseStart_203192 : Nat := 118140960795 + 203192 * 2 ^ 59
def prefixEnd_203192 : Nat := 4983230072969 + 3 ^ 40 * 203192 * 2
def baseEnd_203192 : Nat := 104335161148474244065543

theorem tailTrace_203192 : CollatzResearch.WordTrace tailWord_203192 prefixEnd_203192 104335161148474244065543 := by
  unfold tailWord_203192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705510539938780637953915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4940680719918374183938553 3705510539938780637953915)
  ·
    refine ⟨5558265809908170956930873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3705510539938780637953915 5558265809908170956930873)
    ·
      refine ⟨4168699357431128217698155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5558265809908170956930873 4168699357431128217698155)
      ·
        refine ⟨6253049036146692326547233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168699357431128217698155 6253049036146692326547233)
        ·
          refine ⟨4689786777110019244910425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6253049036146692326547233 4689786777110019244910425)
          ·
            refine ⟨3517340082832514433682819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689786777110019244910425 3517340082832514433682819)
            ·
              refine ⟨5276010124248771650524229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517340082832514433682819 5276010124248771650524229)
              ·
                refine ⟨989251898296644684473293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5276010124248771650524229 989251898296644684473293)
                ·
                  refine ⟨370969461861241756677485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989251898296644684473293 370969461861241756677485)
                  ·
                    refine ⟨139113548197965658754057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370969461861241756677485 139113548197965658754057)
                    ·
                      refine ⟨104335161148474244065543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139113548197965658754057 104335161148474244065543)
                      ·
                        rfl

theorem cell23_203192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_203192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203192 prefixEnd_203192 := by exact prefixLift 203192
  have htrace : WordTrace (prefixWord ++ tailWord_203192) baseStart_203192 baseEnd_203192 := by
    simpa [prefixWord, tailWord_203192, baseEnd_203192] using wordTrace_append hprefix tailTrace_203192
  have hstable : (prefixWord ++ tailWord_203192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203192).length < 2 ^ (prefixWord ++ tailWord_203192).sum := by decide
  have hdescent : baseEnd_203192 < baseStart_203192 := by decide
  rcases family_descends (prefixWord ++ tailWord_203192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203209 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 1, 3, 2]
def baseStart_203209 : Nat := 118140960795 + 203209 * 2 ^ 59
def prefixEnd_203209 : Nat := 4983230072969 + 3 ^ 40 * 203209 * 2
def baseEnd_203209 : Nat := 104343890319600677552965

theorem tailTrace_203209 : CollatzResearch.WordTrace tailWord_203209 prefixEnd_203209 104343890319600677552965 := by
  unfold tailWord_203209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7411641120815973179276681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4941094080543982119517787 7411641120815973179276681)
  ·
    refine ⟨5558730840611979884457511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7411641120815973179276681 5558730840611979884457511)
    ·
      refine ⟨8338096260917969826686267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558730840611979884457511 8338096260917969826686267)
      ·
        refine ⟨12507144391376954740029401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8338096260917969826686267 12507144391376954740029401)
        ·
          refine ⟨9380358293532716055022051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12507144391376954740029401 9380358293532716055022051)
          ·
            refine ⟨14070537440299074082533077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380358293532716055022051 14070537440299074082533077)
            ·
              refine ⟨329778221257009548809369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14070537440299074082533077 329778221257009548809369)
              ·
                refine ⟨247333665942757161607027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329778221257009548809369 247333665942757161607027)
                ·
                  refine ⟨371000498914135742410541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247333665942757161607027 371000498914135742410541)
                  ·
                    refine ⟨139125187092800903403953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371000498914135742410541 139125187092800903403953)
                    ·
                      refine ⟨104343890319600677552965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139125187092800903403953 104343890319600677552965)
                      ·
                        rfl

theorem cell23_203209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 3, 2].length) (baseStart_203209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203209 prefixEnd_203209 := by exact prefixLift 203209
  have htrace : WordTrace (prefixWord ++ tailWord_203209) baseStart_203209 baseEnd_203209 := by
    simpa [prefixWord, tailWord_203209, baseEnd_203209] using wordTrace_append hprefix tailTrace_203209
  have hstable : (prefixWord ++ tailWord_203209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203209).length < 2 ^ (prefixWord ++ tailWord_203209).sum := by decide
  have hdescent : baseEnd_203209 < baseStart_203209 := by decide
  rcases family_descends (prefixWord ++ tailWord_203209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203225 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_203225 : Nat := 118140960795 + 203225 * 2 ^ 59
def prefixEnd_203225 : Nat := 4983230072969 + 3 ^ 40 * 203225 * 2
def baseEnd_203225 : Nat := 104352106010072614952891

theorem tailTrace_203225 : CollatzResearch.WordTrace tailWord_203225 prefixEnd_203225 104352106010072614952891 := by
  unfold tailWord_203225
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412224688758007911859129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4941483125838671941239419 7412224688758007911859129)
  ·
    refine ⟨5559168516568505933894347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7412224688758007911859129 5559168516568505933894347)
    ·
      refine ⟨8338752774852758900841521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5559168516568505933894347 8338752774852758900841521)
      ·
        refine ⟨6254064581139569175631141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8338752774852758900841521 6254064581139569175631141)
        ·
          refine ⟨1172637108963669220430839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6254064581139569175631141 1172637108963669220430839)
          ·
            refine ⟨1758955663445503830646259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172637108963669220430839 1758955663445503830646259)
            ·
              refine ⟨2638433495168255745969389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758955663445503830646259 2638433495168255745969389)
              ·
                refine ⟨989412560688095904738521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2638433495168255745969389 989412560688095904738521)
                ·
                  refine ⟨742059420516071928553891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989412560688095904738521 742059420516071928553891)
                  ·
                    refine ⟨1113089130774107892830837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 742059420516071928553891 1113089130774107892830837)
                    ·
                      refine ⟨104352106010072614952891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1113089130774107892830837 104352106010072614952891)
                      ·
                        rfl

theorem cell23_203225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_203225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203225 prefixEnd_203225 := by exact prefixLift 203225
  have htrace : WordTrace (prefixWord ++ tailWord_203225) baseStart_203225 baseEnd_203225 := by
    simpa [prefixWord, tailWord_203225, baseEnd_203225] using wordTrace_append hprefix tailTrace_203225
  have hstable : (prefixWord ++ tailWord_203225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203225).length < 2 ^ (prefixWord ++ tailWord_203225).sum := by decide
  have hdescent : baseEnd_203225 < baseStart_203225 := by decide
  rcases family_descends (prefixWord ++ tailWord_203225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203226 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2]
def baseStart_203226 : Nat := 118140960795 + 203226 * 2 ^ 59
def prefixEnd_203226 : Nat := 4983230072969 + 3 ^ 40 * 203226 * 2
def baseEnd_203226 : Nat := 104352619490727111040387

theorem tailTrace_203226 : CollatzResearch.WordTrace tailWord_203226 prefixEnd_203226 104352619490727111040387 := by
  unfold tailWord_203226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853065290438596270661383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4941507441169590055097021 1853065290438596270661383)
  ·
    refine ⟨2779597935657894405992075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853065290438596270661383 2779597935657894405992075)
    ·
      refine ⟨4169396903486841608988113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779597935657894405992075 4169396903486841608988113)
      ·
        refine ⟨3127047677615131206741085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4169396903486841608988113 3127047677615131206741085)
        ·
          refine ⟨1172642879105674202527907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3127047677615131206741085 1172642879105674202527907)
          ·
            refine ⟨1758964318658511303791861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172642879105674202527907 1758964318658511303791861)
            ·
              refine ⟨164902904874235434730487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1758964318658511303791861 164902904874235434730487)
              ·
                refine ⟨247354357311353152095731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164902904874235434730487 247354357311353152095731)
                ·
                  refine ⟨371031535967029728143597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247354357311353152095731 371031535967029728143597)
                  ·
                    refine ⟨139136825987636148053849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371031535967029728143597 139136825987636148053849)
                    ·
                      refine ⟨104352619490727111040387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139136825987636148053849 104352619490727111040387)
                      ·
                        rfl

theorem cell23_203226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_203226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203226 prefixEnd_203226 := by exact prefixLift 203226
  have htrace : WordTrace (prefixWord ++ tailWord_203226) baseStart_203226 baseEnd_203226 := by
    simpa [prefixWord, tailWord_203226, baseEnd_203226] using wordTrace_append hprefix tailTrace_203226
  have hstable : (prefixWord ++ tailWord_203226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203226).length < 2 ^ (prefixWord ++ tailWord_203226).sum := by decide
  have hdescent : baseEnd_203226 < baseStart_203226 := by decide
  rcases family_descends (prefixWord ++ tailWord_203226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203234 : List Nat := [3, 3, 3, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_203234 : Nat := 118140960795 + 203234 * 2 ^ 59
def prefixEnd_203234 : Nat := 4983230072969 + 3 ^ 40 * 203234 * 2
def baseEnd_203234 : Nat := 104356727335963079740351

theorem tailTrace_203234 : CollatzResearch.WordTrace tailWord_203234 prefixEnd_203234 104356727335963079740351 := by
  unfold tailWord_203234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853138236431350612234189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4941701963816934965957837 1853138236431350612234189)
  ·
    refine ⟨694926838661756479587821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1853138236431350612234189 694926838661756479587821)
    ·
      refine ⟨260597564498158679845433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 694926838661756479587821 260597564498158679845433)
      ·
        refine ⟨195448173373619009884075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260597564498158679845433 195448173373619009884075)
        ·
          refine ⟨293172260060428514826113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195448173373619009884075 293172260060428514826113)
          ·
            refine ⟨219879195045321386119585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293172260060428514826113 219879195045321386119585)
            ·
              refine ⟨164909396283991039589689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219879195045321386119585 164909396283991039589689)
              ·
                refine ⟨123682047212993279692267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164909396283991039589689 123682047212993279692267)
                ·
                  refine ⟨185523070819489919538401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123682047212993279692267 185523070819489919538401)
                  ·
                    refine ⟨139142303114617439653801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185523070819489919538401 139142303114617439653801)
                    ·
                      refine ⟨104356727335963079740351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139142303114617439653801 104356727335963079740351)
                      ·
                        rfl

theorem cell23_203234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_203234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203234 prefixEnd_203234 := by exact prefixLift 203234
  have htrace : WordTrace (prefixWord ++ tailWord_203234) baseStart_203234 baseEnd_203234 := by
    simpa [prefixWord, tailWord_203234, baseEnd_203234] using wordTrace_append hprefix tailTrace_203234
  have hstable : (prefixWord ++ tailWord_203234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203234).length < 2 ^ (prefixWord ++ tailWord_203234).sum := by decide
  have hdescent : baseEnd_203234 < baseStart_203234 := by decide
  rcases family_descends (prefixWord ++ tailWord_203234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203242 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_203242 : Nat := 118140960795 + 203242 * 2 ^ 59
def prefixEnd_203242 : Nat := 4983230072969 + 3 ^ 40 * 203242 * 2
def baseEnd_203242 : Nat := 104360835181199048440313

theorem tailTrace_203242 : CollatzResearch.WordTrace tailWord_203242 prefixEnd_203242 104360835181199048440313 := by
  unfold tailWord_203242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853211182424104953806995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4941896486464279876818653 1853211182424104953806995)
  ·
    refine ⟨2779816773636157430710493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853211182424104953806995 2779816773636157430710493)
    ·
      refine ⟨1042431290113559036516435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2779816773636157430710493 1042431290113559036516435)
      ·
        refine ⟨1563646935170338554774653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042431290113559036516435 1563646935170338554774653)
        ·
          refine ⟨586367600688876958040495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1563646935170338554774653 586367600688876958040495)
          ·
            refine ⟨879551401033315437060743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586367600688876958040495 879551401033315437060743)
            ·
              refine ⟨1319327101549973155591115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879551401033315437060743 1319327101549973155591115)
              ·
                refine ⟨1978990652324959733386673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319327101549973155591115 1978990652324959733386673)
                ·
                  refine ⟨1484242989243719800040005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1978990652324959733386673 1484242989243719800040005)
                  ·
                    refine ⟨278295560483197462507501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1484242989243719800040005 278295560483197462507501)
                    ·
                      refine ⟨104360835181199048440313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 278295560483197462507501 104360835181199048440313)
                      ·
                        rfl

theorem cell23_203242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_203242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203242 prefixEnd_203242 := by exact prefixLift 203242
  have htrace : WordTrace (prefixWord ++ tailWord_203242) baseStart_203242 baseEnd_203242 := by
    simpa [prefixWord, tailWord_203242, baseEnd_203242] using wordTrace_append hprefix tailTrace_203242
  have hstable : (prefixWord ++ tailWord_203242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203242).length < 2 ^ (prefixWord ++ tailWord_203242).sum := by decide
  have hdescent : baseEnd_203242 < baseStart_203242 := by decide
  rcases family_descends (prefixWord ++ tailWord_203242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203277 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_203277 : Nat := 118140960795 + 203277 * 2 ^ 59
def prefixEnd_203277 : Nat := 4983230072969 + 3 ^ 40 * 203277 * 2
def baseEnd_203277 : Nat := 104378807004106411502653

theorem tailTrace_203277 : CollatzResearch.WordTrace tailWord_203277 prefixEnd_203277 104378807004106411502653 := by
  unfold tailWord_203277
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414121284569620792752085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4942747523046413861834723 7414121284569620792752085)
  ·
    refine ⟨173768467607100487330127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7414121284569620792752085 173768467607100487330127)
    ·
      refine ⟨260652701410650730995191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173768467607100487330127 260652701410650730995191)
      ·
        refine ⟨390979052115976096492787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260652701410650730995191 390979052115976096492787)
        ·
          refine ⟨586468578173964144739181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390979052115976096492787 586468578173964144739181)
          ·
            refine ⟨219925716815236554277193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 586468578173964144739181 219925716815236554277193)
            ·
              refine ⟨164944287611427415707895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219925716815236554277193 164944287611427415707895)
              ·
                refine ⟨247416431417141123561843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164944287611427415707895 247416431417141123561843)
                ·
                  refine ⟨371124647125711685342765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247416431417141123561843 371124647125711685342765)
                  ·
                    refine ⟨139171742672141882003537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371124647125711685342765 139171742672141882003537)
                    ·
                      refine ⟨104378807004106411502653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139171742672141882003537 104378807004106411502653)
                      ·
                        rfl

theorem cell23_203277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_203277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203277 prefixEnd_203277 := by exact prefixLift 203277
  have htrace : WordTrace (prefixWord ++ tailWord_203277) baseStart_203277 baseEnd_203277 := by
    simpa [prefixWord, tailWord_203277, baseEnd_203277] using wordTrace_append hprefix tailTrace_203277
  have hstable : (prefixWord ++ tailWord_203277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203277).length < 2 ^ (prefixWord ++ tailWord_203277).sum := by decide
  have hdescent : baseEnd_203277 < baseStart_203277 := by decide
  rcases family_descends (prefixWord ++ tailWord_203277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203406 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_203406 : Nat := 118140960795 + 203406 * 2 ^ 59
def prefixEnd_203406 : Nat := 4983230072969 + 3 ^ 40 * 203406 * 2
def baseEnd_203406 : Nat := 104445046008536406789559

theorem tailTrace_203406 : CollatzResearch.WordTrace tailWord_203406 prefixEnd_203406 104445046008536406789559 := by
  unfold tailWord_203406
  simp only [CollatzResearch.WordTrace]
  refine ⟨927353287637784478024759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4945884200734850549465381 927353287637784478024759)
  ·
    refine ⟨1391029931456676717037139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 927353287637784478024759 1391029931456676717037139)
    ·
      refine ⟨2086544897185015075555709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391029931456676717037139 2086544897185015075555709)
      ·
        refine ⟨782454336444380653333391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2086544897185015075555709 782454336444380653333391)
        ·
          refine ⟨1173681504666570980000087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782454336444380653333391 1173681504666570980000087)
          ·
            refine ⟨1760522256999856470000131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173681504666570980000087 1760522256999856470000131)
            ·
              refine ⟨2640783385499784705000197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760522256999856470000131 2640783385499784705000197)
              ·
                refine ⟨495146884781209632187537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2640783385499784705000197 495146884781209632187537)
                ·
                  refine ⟨371360163585907224140653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495146884781209632187537 371360163585907224140653)
                  ·
                    refine ⟨139260061344715209052745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371360163585907224140653 139260061344715209052745)
                    ·
                      refine ⟨104445046008536406789559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139260061344715209052745 104445046008536406789559)
                      ·
                        rfl

theorem cell23_203406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_203406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203406 prefixEnd_203406 := by exact prefixLift 203406
  have htrace : WordTrace (prefixWord ++ tailWord_203406) baseStart_203406 baseEnd_203406 := by
    simpa [prefixWord, tailWord_203406, baseEnd_203406] using wordTrace_append hprefix tailTrace_203406
  have hstable : (prefixWord ++ tailWord_203406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203406).length < 2 ^ (prefixWord ++ tailWord_203406).sum := by decide
  have hdescent : baseEnd_203406 < baseStart_203406 := by decide
  rcases family_descends (prefixWord ++ tailWord_203406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203439 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 3]
def baseStart_203439 : Nat := 118140960795 + 203439 * 2 ^ 59
def prefixEnd_203439 : Nat := 4983230072969 + 3 ^ 40 * 203439 * 2
def baseEnd_203439 : Nat := 104461990870134777676907

theorem tailTrace_203439 : CollatzResearch.WordTrace tailWord_203439 prefixEnd_203439 104461990870134777676907 := by
  unfold tailWord_203439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7420029909982722460149371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4946686606655148306766247 7420029909982722460149371)
  ·
    refine ⟨11130044864974083690224057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7420029909982722460149371 11130044864974083690224057)
    ·
      refine ⟨8347533648730562767668043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11130044864974083690224057 8347533648730562767668043)
      ·
        refine ⟨12521300473095844151502065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8347533648730562767668043 12521300473095844151502065)
        ·
          refine ⟨9390975354821883113626549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12521300473095844151502065 9390975354821883113626549)
          ·
            refine ⟨880403939514551541902489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9390975354821883113626549 880403939514551541902489)
            ·
              refine ⟨660302954635913656426867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880403939514551541902489 660302954635913656426867)
              ·
                refine ⟨990454431953870484640301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660302954635913656426867 990454431953870484640301)
                ·
                  refine ⟨371420411982701431740113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990454431953870484640301 371420411982701431740113)
                  ·
                    refine ⟨278565308987026073805085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 371420411982701431740113 278565308987026073805085)
                    ·
                      refine ⟨104461990870134777676907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 278565308987026073805085 104461990870134777676907)
                      ·
                        rfl

theorem cell23_203439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_203439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203439 prefixEnd_203439 := by exact prefixLift 203439
  have htrace : WordTrace (prefixWord ++ tailWord_203439) baseStart_203439 baseEnd_203439 := by
    simpa [prefixWord, tailWord_203439, baseEnd_203439] using wordTrace_append hprefix tailTrace_203439
  have hstable : (prefixWord ++ tailWord_203439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203439).length < 2 ^ (prefixWord ++ tailWord_203439).sum := by decide
  have hdescent : baseEnd_203439 < baseStart_203439 := by decide
  rcases family_descends (prefixWord ++ tailWord_203439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203453 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_203453 : Nat := 118140960795 + 203453 * 2 ^ 59
def prefixEnd_203453 : Nat := 4983230072969 + 3 ^ 40 * 203453 * 2
def baseEnd_203453 : Nat := 104469179599297722901843

theorem tailTrace_203453 : CollatzResearch.WordTrace tailWord_203453 prefixEnd_203453 104469179599297722901843 := by
  unfold tailWord_203453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7420540531932002851159013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4947027021288001900772675 7420540531932002851159013)
  ·
    refine ⟨1391351349737250534592315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7420540531932002851159013 1391351349737250534592315)
    ·
      refine ⟨2087027024605875801888473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391351349737250534592315 2087027024605875801888473)
      ·
        refine ⟨1565270268454406851416355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2087027024605875801888473 1565270268454406851416355)
        ·
          refine ⟨2347905402681610277124533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565270268454406851416355 2347905402681610277124533)
          ·
            refine ⟨220116131501400963480425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2347905402681610277124533 220116131501400963480425)
            ·
              refine ⟨165087098626050722610319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220116131501400963480425 165087098626050722610319)
              ·
                refine ⟨247630647939076083915479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165087098626050722610319 247630647939076083915479)
                ·
                  refine ⟨371445971908614125873219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247630647939076083915479 371445971908614125873219)
                  ·
                    refine ⟨557168957862921188809829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371445971908614125873219 557168957862921188809829)
                    ·
                      refine ⟨104469179599297722901843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 557168957862921188809829 104469179599297722901843)
                      ·
                        rfl

theorem cell23_203453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_203453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203453 prefixEnd_203453 := by exact prefixLift 203453
  have htrace : WordTrace (prefixWord ++ tailWord_203453) baseStart_203453 baseEnd_203453 := by
    simpa [prefixWord, tailWord_203453, baseEnd_203453] using wordTrace_append hprefix tailTrace_203453
  have hstable : (prefixWord ++ tailWord_203453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203453).length < 2 ^ (prefixWord ++ tailWord_203453).sum := by decide
  have hdescent : baseEnd_203453 < baseStart_203453 := by decide
  rcases family_descends (prefixWord ++ tailWord_203453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203456 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3]
def baseStart_203456 : Nat := 118140960795 + 203456 * 2 ^ 59
def prefixEnd_203456 : Nat := 4983230072969 + 3 ^ 40 * 203456 * 2
def baseEnd_203456 : Nat := 104470720041261211164329

theorem tailTrace_203456 : CollatzResearch.WordTrace tailWord_203456 prefixEnd_203456 104470720041261211164329 := by
  unfold tailWord_203456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710324975460567181759111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4947099967280756242345481 3710324975460567181759111)
  ·
    refine ⟨5565487463190850772638667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3710324975460567181759111 5565487463190850772638667)
    ·
      refine ⟨8348231194786276158958001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5565487463190850772638667 8348231194786276158958001)
      ·
        refine ⟨6261173396089707119218501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8348231194786276158958001 6261173396089707119218501)
        ·
          refine ⟨1173970011766820084853469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6261173396089707119218501 1173970011766820084853469)
          ·
            refine ⟨440238754412557531820051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1173970011766820084853469 440238754412557531820051)
            ·
              refine ⟨660358131618836297730077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440238754412557531820051 660358131618836297730077)
              ·
                refine ⟨247634299357063611648779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660358131618836297730077 247634299357063611648779)
                ·
                  refine ⟨371451449035595417473169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247634299357063611648779 371451449035595417473169)
                  ·
                    refine ⟨278588586776696563104877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 371451449035595417473169 278588586776696563104877)
                    ·
                      refine ⟨104470720041261211164329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 278588586776696563104877 104470720041261211164329)
                      ·
                        rfl

theorem cell23_203456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_203456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203456 prefixEnd_203456 := by exact prefixLift 203456
  have htrace : WordTrace (prefixWord ++ tailWord_203456) baseStart_203456 baseEnd_203456 := by
    simpa [prefixWord, tailWord_203456, baseEnd_203456] using wordTrace_append hprefix tailTrace_203456
  have hstable : (prefixWord ++ tailWord_203456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203456).length < 2 ^ (prefixWord ++ tailWord_203456).sum := by decide
  have hdescent : baseEnd_203456 < baseStart_203456 := by decide
  rcases family_descends (prefixWord ++ tailWord_203456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203470 : List Nat := [4, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_203470 : Nat := 118140960795 + 203470 * 2 ^ 59
def prefixEnd_203470 : Nat := 4983230072969 + 3 ^ 40 * 203470 * 2
def baseEnd_203470 : Nat := 104477908770424156389265

theorem tailTrace_203470 : CollatzResearch.WordTrace tailWord_203470 prefixEnd_203470 104477908770424156389265 := by
  unfold tailWord_203470
  simp only [CollatzResearch.WordTrace]
  refine ⟨927645071608801844315983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4947440381913609836351909 927645071608801844315983)
  ·
    refine ⟨1391467607413202766473975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 927645071608801844315983 1391467607413202766473975)
    ·
      refine ⟨2087201411119804149710963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391467607413202766473975 2087201411119804149710963)
      ·
        refine ⟨3130802116679706224566445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087201411119804149710963 3130802116679706224566445)
        ·
          refine ⟨1174050793754889834212417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3130802116679706224566445 1174050793754889834212417)
          ·
            refine ⟨880538095316167375659313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174050793754889834212417 880538095316167375659313)
            ·
              refine ⟨660403571487125531744485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880538095316167375659313 660403571487125531744485)
              ·
                refine ⟨123825669653836037202091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660403571487125531744485 123825669653836037202091)
                ·
                  refine ⟨185738504480754055803137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123825669653836037202091 185738504480754055803137)
                  ·
                    refine ⟨139303878360565541852353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185738504480754055803137 139303878360565541852353)
                    ·
                      refine ⟨104477908770424156389265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139303878360565541852353 104477908770424156389265)
                      ·
                        rfl

theorem cell23_203470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_203470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203470 prefixEnd_203470 := by exact prefixLift 203470
  have htrace : WordTrace (prefixWord ++ tailWord_203470) baseStart_203470 baseEnd_203470 := by
    simpa [prefixWord, tailWord_203470, baseEnd_203470] using wordTrace_append hprefix tailTrace_203470
  have hstable : (prefixWord ++ tailWord_203470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203470).length < 2 ^ (prefixWord ++ tailWord_203470).sum := by decide
  have hdescent : baseEnd_203470 < baseStart_203470 := by decide
  rcases family_descends (prefixWord ++ tailWord_203470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203583 : List Nat := [1, 1, 2, 2, 5, 1, 4, 2, 5]
def baseStart_203583 : Nat := 118140960795 + 203583 * 2 ^ 59
def prefixEnd_203583 : Nat := 4983230072969 + 3 ^ 40 * 203583 * 2
def baseEnd_203583 : Nat := 11615103564931357141805

theorem tailTrace_203583 : CollatzResearch.WordTrace tailWord_203583 prefixEnd_203583 11615103564931357141805 := by
  unfold tailWord_203583
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425282021461035053391403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4950188014307356702260935 7425282021461035053391403)
  ·
    refine ⟨11137923032191552580087105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7425282021461035053391403 11137923032191552580087105)
    ·
      refine ⟨8353442274143664435065329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11137923032191552580087105 8353442274143664435065329)
      ·
        refine ⟨6265081705607748326298997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8353442274143664435065329 6265081705607748326298997)
        ·
          refine ⟨587351409900726405590531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6265081705607748326298997 587351409900726405590531)
          ·
            refine ⟨881027114851089608385797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587351409900726405590531 881027114851089608385797)
            ·
              refine ⟨165192584034579301572337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 881027114851089608385797 165192584034579301572337)
              ·
                refine ⟨123894438025934476179253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165192584034579301572337 123894438025934476179253)
                ·
                  refine ⟨11615103564931357141805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123894438025934476179253 11615103564931357141805)
                  ·
                    rfl

theorem cell23_203583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 5].length) (baseStart_203583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203583 prefixEnd_203583 := by exact prefixLift 203583
  have htrace : WordTrace (prefixWord ++ tailWord_203583) baseStart_203583 baseEnd_203583 := by
    simpa [prefixWord, tailWord_203583, baseEnd_203583] using wordTrace_append hprefix tailTrace_203583
  have hstable : (prefixWord ++ tailWord_203583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203583).length < 2 ^ (prefixWord ++ tailWord_203583).sum := by decide
  have hdescent : baseEnd_203583 < baseStart_203583 := by decide
  rcases family_descends (prefixWord ++ tailWord_203583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203590 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_203590 : Nat := 118140960795 + 203590 * 2 ^ 59
def prefixEnd_203590 : Nat := 4983230072969 + 3 ^ 40 * 203590 * 2
def baseEnd_203590 : Nat := 104539526448963686888713

theorem tailTrace_203590 : CollatzResearch.WordTrace tailWord_203590 prefixEnd_203590 104539526448963686888713 := by
  unfold tailWord_203590
  simp only [CollatzResearch.WordTrace]
  refine ⟨232048041638614851528007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4950358221623783499264149 232048041638614851528007)
  ·
    refine ⟨348072062457922277292011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232048041638614851528007 348072062457922277292011)
    ·
      refine ⟨522108093686883415938017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348072062457922277292011 522108093686883415938017)
      ·
        refine ⟨391581070265162561953513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522108093686883415938017 391581070265162561953513)
        ·
          refine ⟨293685802698871921465135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391581070265162561953513 293685802698871921465135)
          ·
            refine ⟨440528704048307882197703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293685802698871921465135 440528704048307882197703)
            ·
              refine ⟨660793056072461823296555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440528704048307882197703 660793056072461823296555)
              ·
                refine ⟨991189584108692734944833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660793056072461823296555 991189584108692734944833)
                ·
                  refine ⟨743392188081519551208625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 991189584108692734944833 743392188081519551208625)
                  ·
                    refine ⟨557544141061139663406469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 743392188081519551208625 557544141061139663406469)
                    ·
                      refine ⟨104539526448963686888713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 557544141061139663406469 104539526448963686888713)
                      ·
                        rfl

theorem cell23_203590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_203590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203590 prefixEnd_203590 := by exact prefixLift 203590
  have htrace : WordTrace (prefixWord ++ tailWord_203590) baseStart_203590 baseEnd_203590 := by
    simpa [prefixWord, tailWord_203590, baseEnd_203590] using wordTrace_append hprefix tailTrace_203590
  have hstable : (prefixWord ++ tailWord_203590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203590).length < 2 ^ (prefixWord ++ tailWord_203590).sum := by decide
  have hdescent : baseEnd_203590 < baseStart_203590 := by decide
  rcases family_descends (prefixWord ++ tailWord_203590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203616 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 1, 6, 2]
def baseStart_203616 : Nat := 118140960795 + 203616 * 2 ^ 59
def prefixEnd_203616 : Nat := 4983230072969 + 3 ^ 40 * 203616 * 2
def baseEnd_203616 : Nat := 104552876945980585163593

theorem tailTrace_203616 : CollatzResearch.WordTrace tailWord_203616 prefixEnd_203616 104552876945980585163593 := by
  unfold tailWord_203616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713242815170740844671351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4950990420227654459561801 3713242815170740844671351)
  ·
    refine ⟨5569864222756111267007027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3713242815170740844671351 5569864222756111267007027)
    ·
      refine ⟨8354796334134166900510541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5569864222756111267007027 8354796334134166900510541)
      ·
        refine ⟨3133048625300312587691453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8354796334134166900510541 3133048625300312587691453)
        ·
          refine ⟨1174893234487617220384295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3133048625300312587691453 1174893234487617220384295)
          ·
            refine ⟨1762339851731425830576443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174893234487617220384295 1762339851731425830576443)
            ·
              refine ⟨2643509777597138745864665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762339851731425830576443 2643509777597138745864665)
              ·
                refine ⟨1982632333197854059398499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643509777597138745864665 1982632333197854059398499)
                ·
                  refine ⟨2973948499796781089097749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982632333197854059398499 2973948499796781089097749)
                  ·
                    refine ⟨139403835927974113551457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2973948499796781089097749 139403835927974113551457)
                    ·
                      refine ⟨104552876945980585163593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139403835927974113551457 104552876945980585163593)
                      ·
                        rfl

theorem cell23_203616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_203616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203616 prefixEnd_203616 := by exact prefixLift 203616
  have htrace : WordTrace (prefixWord ++ tailWord_203616) baseStart_203616 baseEnd_203616 := by
    simpa [prefixWord, tailWord_203616, baseEnd_203616] using wordTrace_append hprefix tailTrace_203616
  have hstable : (prefixWord ++ tailWord_203616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203616).length < 2 ^ (prefixWord ++ tailWord_203616).sum := by decide
  have hdescent : baseEnd_203616 < baseStart_203616 := by decide
  rcases family_descends (prefixWord ++ tailWord_203616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203643 : List Nat := [1, 1, 1, 1, 1, 5, 4, 4, 1, 4]
def baseStart_203643 : Nat := 118140960795 + 203643 * 2 ^ 59
def prefixEnd_203643 : Nat := 4983230072969 + 3 ^ 40 * 203643 * 2
def baseEnd_203643 : Nat := 34855580307883993175323

theorem tailTrace_203643 : CollatzResearch.WordTrace tailWord_203643 prefixEnd_203643 34855580307883993175323 := by
  unfold tailWord_203643
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427470401243665300575583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4951646934162443533717055 7427470401243665300575583)
  ·
    refine ⟨11141205601865497950863375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7427470401243665300575583 11141205601865497950863375)
    ·
      refine ⟨16711808402798246926295063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11141205601865497950863375 16711808402798246926295063)
      ·
        refine ⟨25067712604197370389442595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16711808402798246926295063 25067712604197370389442595)
        ·
          refine ⟨37601568906296055584163893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25067712604197370389442595 37601568906296055584163893)
          ·
            refine ⟨3525147084965255211015365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37601568906296055584163893 3525147084965255211015365)
            ·
              refine ⟨660965078430985352065381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3525147084965255211015365 660965078430985352065381)
              ·
                refine ⟨123930952205809753512259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660965078430985352065381 123930952205809753512259)
                ·
                  refine ⟨185896428308714630268389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123930952205809753512259 185896428308714630268389)
                  ·
                    refine ⟨34855580307883993175323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185896428308714630268389 34855580307883993175323)
                    ·
                      rfl

theorem cell23_203643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 4].length) (baseStart_203643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203643 prefixEnd_203643 := by exact prefixLift 203643
  have htrace : WordTrace (prefixWord ++ tailWord_203643) baseStart_203643 baseEnd_203643 := by
    simpa [prefixWord, tailWord_203643, baseEnd_203643] using wordTrace_append hprefix tailTrace_203643
  have hstable : (prefixWord ++ tailWord_203643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203643).length < 2 ^ (prefixWord ++ tailWord_203643).sum := by decide
  have hdescent : baseEnd_203643 < baseStart_203643 := by decide
  rcases family_descends (prefixWord ++ tailWord_203643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203699 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 5, 6]
def baseStart_203699 : Nat := 118140960795 + 203699 * 2 ^ 59
def prefixEnd_203699 : Nat := 4983230072969 + 3 ^ 40 * 203699 * 2
def baseEnd_203699 : Nat := 34865165280101253475237

theorem tailTrace_203699 : CollatzResearch.WordTrace tailWord_203699 prefixEnd_203699 34865165280101253475237 := by
  unfold tailWord_203699
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429512889040786864614151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4953008592693857909742767 7429512889040786864614151)
  ·
    refine ⟨11144269333561180296921227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7429512889040786864614151 11144269333561180296921227)
    ·
      refine ⟨16716404000341770445381841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11144269333561180296921227 16716404000341770445381841)
      ·
        refine ⟨12537303000256327834036381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16716404000341770445381841 12537303000256327834036381)
        ·
          refine ⟨4701488625096122937763643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12537303000256327834036381 4701488625096122937763643)
          ·
            refine ⟨7052232937644184406645465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701488625096122937763643 7052232937644184406645465)
            ·
              refine ⟨5289174703233138304984099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7052232937644184406645465 5289174703233138304984099)
              ·
                refine ⟨7933762054849707457476149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289174703233138304984099 7933762054849707457476149)
                ·
                  refine ⟨743790192642160074138389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7933762054849707457476149 743790192642160074138389)
                  ·
                    refine ⟨34865165280101253475237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 743790192642160074138389 34865165280101253475237)
                    ·
                      rfl

theorem cell23_203699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 6].length) (baseStart_203699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203699 prefixEnd_203699 := by exact prefixLift 203699
  have htrace : WordTrace (prefixWord ++ tailWord_203699) baseStart_203699 baseEnd_203699 := by
    simpa [prefixWord, tailWord_203699, baseEnd_203699] using wordTrace_append hprefix tailTrace_203699
  have hstable : (prefixWord ++ tailWord_203699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203699).length < 2 ^ (prefixWord ++ tailWord_203699).sum := by decide
  have hdescent : baseEnd_203699 < baseStart_203699 := by decide
  rcases family_descends (prefixWord ++ tailWord_203699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203706 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_203706 : Nat := 118140960795 + 203706 * 2 ^ 59
def prefixEnd_203706 : Nat := 4983230072969 + 3 ^ 40 * 203706 * 2
def baseEnd_203706 : Nat := 104599090204885233038179

theorem tailTrace_203706 : CollatzResearch.WordTrace tailWord_203706 prefixEnd_203706 104599090204885233038179 := by
  unfold tailWord_203706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857442050003856765029743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4953178800010284706745981 1857442050003856765029743)
  ·
    refine ⟨2786163075005785147544615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1857442050003856765029743 2786163075005785147544615)
    ·
      refine ⟨4179244612508677721316923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2786163075005785147544615 4179244612508677721316923)
      ·
        refine ⟨6268866918763016581975385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179244612508677721316923 6268866918763016581975385)
        ·
          refine ⟨4701650189072262436481539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6268866918763016581975385 4701650189072262436481539)
          ·
            refine ⟨7052475283608393654722309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701650189072262436481539 7052475283608393654722309)
            ·
              refine ⟨1322339115676573810260433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7052475283608393654722309 1322339115676573810260433)
              ·
                refine ⟨991754336757430357695325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322339115676573810260433 991754336757430357695325)
                ·
                  refine ⟨371907876284036384135747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991754336757430357695325 371907876284036384135747)
                  ·
                    refine ⟨557861814426054576203621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371907876284036384135747 557861814426054576203621)
                    ·
                      refine ⟨104599090204885233038179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 557861814426054576203621 104599090204885233038179)
                      ·
                        rfl

theorem cell23_203706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_203706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203706 prefixEnd_203706 := by exact prefixLift 203706
  have htrace : WordTrace (prefixWord ++ tailWord_203706) baseStart_203706 baseEnd_203706 := by
    simpa [prefixWord, tailWord_203706, baseEnd_203706] using wordTrace_append hprefix tailTrace_203706
  have hstable : (prefixWord ++ tailWord_203706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203706).length < 2 ^ (prefixWord ++ tailWord_203706).sum := by decide
  have hdescent : baseEnd_203706 < baseStart_203706 := by decide
  rcases family_descends (prefixWord ++ tailWord_203706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203720 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 1, 5]
def baseStart_203720 : Nat := 118140960795 + 203720 * 2 ^ 59
def prefixEnd_203720 : Nat := 4983230072969 + 3 ^ 40 * 203720 * 2
def baseEnd_203720 : Nat := 34868759644682726087705

theorem tailTrace_203720 : CollatzResearch.WordTrace tailWord_203720 prefixEnd_203720 34868759644682726087705 := by
  unfold tailWord_203720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715139410982353725564307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4953519214643138300752409 3715139410982353725564307)
  ·
    refine ⟨5572709116473530588346461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3715139410982353725564307 5572709116473530588346461)
    ·
      refine ⟨2089765918677573970629923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5572709116473530588346461 2089765918677573970629923)
      ·
        refine ⟨3134648878016360955944885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089765918677573970629923 3134648878016360955944885)
        ·
          refine ⟨293873332314033839619833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3134648878016360955944885 293873332314033839619833)
          ·
            refine ⟨220404999235525379714875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293873332314033839619833 220404999235525379714875)
            ·
              refine ⟨330607498853288069572313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220404999235525379714875 330607498853288069572313)
              ·
                refine ⟨247955624139966052179235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330607498853288069572313 247955624139966052179235)
                ·
                  refine ⟨371933436209949078268853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247955624139966052179235 371933436209949078268853)
                  ·
                    refine ⟨34868759644682726087705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 371933436209949078268853 34868759644682726087705)
                    ·
                      rfl

theorem cell23_203720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_203720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203720 prefixEnd_203720 := by exact prefixLift 203720
  have htrace : WordTrace (prefixWord ++ tailWord_203720) baseStart_203720 baseEnd_203720 := by
    simpa [prefixWord, tailWord_203720, baseEnd_203720] using wordTrace_append hprefix tailTrace_203720
  have hstable : (prefixWord ++ tailWord_203720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203720).length < 2 ^ (prefixWord ++ tailWord_203720).sum := by decide
  have hdescent : baseEnd_203720 < baseStart_203720 := by decide
  rcases family_descends (prefixWord ++ tailWord_203720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203723 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 4]
def baseStart_203723 : Nat := 118140960795 + 203723 * 2 ^ 59
def prefixEnd_203723 : Nat := 4983230072969 + 3 ^ 40 * 203723 * 2
def baseEnd_203723 : Nat := 104607819376011666525601

theorem tailTrace_203723 : CollatzResearch.WordTrace tailWord_203723 prefixEnd_203723 104607819376011666525601 := by
  unfold tailWord_203723
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430388240953838963487823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4953592160635892642325215 7430388240953838963487823)
  ·
    refine ⟨11145582361430758445231735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7430388240953838963487823 11145582361430758445231735)
    ·
      refine ⟨16718373542146137667847603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11145582361430758445231735 16718373542146137667847603)
      ·
        refine ⟨25077560313219206501771405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16718373542146137667847603 25077560313219206501771405)
        ·
          refine ⟨9404085117457202438164277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25077560313219206501771405 9404085117457202438164277)
          ·
            refine ⟨881632979761612728577901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9404085117457202438164277 881632979761612728577901)
            ·
              refine ⟨330612367410604773216713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 881632979761612728577901 330612367410604773216713)
              ·
                refine ⟨247959275557953579912535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330612367410604773216713 247959275557953579912535)
                ·
                  refine ⟨371938913336930369868803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247959275557953579912535 371938913336930369868803)
                  ·
                    refine ⟨557908370005395554803205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371938913336930369868803 557908370005395554803205)
                    ·
                      refine ⟨104607819376011666525601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 557908370005395554803205 104607819376011666525601)
                      ·
                        rfl

theorem cell23_203723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 4].length) (baseStart_203723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203723 prefixEnd_203723 := by exact prefixLift 203723
  have htrace : WordTrace (prefixWord ++ tailWord_203723) baseStart_203723 baseEnd_203723 := by
    simpa [prefixWord, tailWord_203723, baseEnd_203723] using wordTrace_append hprefix tailTrace_203723
  have hstable : (prefixWord ++ tailWord_203723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203723).length < 2 ^ (prefixWord ++ tailWord_203723).sum := by decide
  have hdescent : baseEnd_203723 < baseStart_203723 := by decide
  rcases family_descends (prefixWord ++ tailWord_203723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203729 : List Nat := [1, 2, 2, 1, 2, 1, 3, 11]
def baseStart_203729 : Nat := 118140960795 + 203729 * 2 ^ 59
def prefixEnd_203729 : Nat := 4983230072969 + 3 ^ 40 * 203729 * 2
def baseEnd_203729 : Nat := 3874477787405134927799

theorem tailTrace_203729 : CollatzResearch.WordTrace tailWord_203729 prefixEnd_203729 3874477787405134927799 := by
  unfold tailWord_203729
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430607078932101988206241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4953738052621401325470827 7430607078932101988206241)
  ·
    refine ⟨5572955309199076491154681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7430607078932101988206241 5572955309199076491154681)
    ·
      refine ⟨4179716481899307368366011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5572955309199076491154681 4179716481899307368366011)
      ·
        refine ⟨6269574722848961052549017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179716481899307368366011 6269574722848961052549017)
        ·
          refine ⟨4702181042136720789411763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6269574722848961052549017 4702181042136720789411763)
          ·
            refine ⟨7053271563205081184117645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4702181042136720789411763 7053271563205081184117645)
            ·
              refine ⟨2644976836201905444044117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7053271563205081184117645 2644976836201905444044117)
              ·
                refine ⟨3874477787405134927799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 2644976836201905444044117 3874477787405134927799)
                ·
                  rfl

theorem cell23_203729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 11].length) (baseStart_203729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203729 prefixEnd_203729 := by exact prefixLift 203729
  have htrace : WordTrace (prefixWord ++ tailWord_203729) baseStart_203729 baseEnd_203729 := by
    simpa [prefixWord, tailWord_203729, baseEnd_203729] using wordTrace_append hprefix tailTrace_203729
  have hstable : (prefixWord ++ tailWord_203729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203729).length < 2 ^ (prefixWord ++ tailWord_203729).sum := by decide
  have hdescent : baseEnd_203729 < baseStart_203729 := by decide
  rcases family_descends (prefixWord ++ tailWord_203729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203733 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_203733 : Nat := 118140960795 + 203733 * 2 ^ 59
def prefixEnd_203733 : Nat := 4983230072969 + 3 ^ 40 * 203733 * 2
def baseEnd_203733 : Nat := 34870984727518875800185

theorem tailTrace_203733 : CollatzResearch.WordTrace tailWord_203733 prefixEnd_203733 34870984727518875800185 := by
  unfold tailWord_203733
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430752970917610671351853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4953835313945073780901235 7430752970917610671351853)
  ·
    refine ⟨2786532364094104001756945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7430752970917610671351853 2786532364094104001756945)
    ·
      refine ⟨2089899273070578001317709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2786532364094104001756945 2089899273070578001317709)
      ·
        refine ⟨783712227401466750494141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2089899273070578001317709 783712227401466750494141)
        ·
          refine ⟨293892085275550031435303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783712227401466750494141 293892085275550031435303)
          ·
            refine ⟨440838127913325047152955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293892085275550031435303 440838127913325047152955)
            ·
              refine ⟨661257191869987570729433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440838127913325047152955 661257191869987570729433)
              ·
                refine ⟨495942893902490678047075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661257191869987570729433 495942893902490678047075)
                ·
                  refine ⟨743914340853736017070613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495942893902490678047075 743914340853736017070613)
                  ·
                    refine ⟨34870984727518875800185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 743914340853736017070613 34870984727518875800185)
                    ·
                      rfl

theorem cell23_203733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_203733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203733 prefixEnd_203733 := by exact prefixLift 203733
  have htrace : WordTrace (prefixWord ++ tailWord_203733) baseStart_203733 baseEnd_203733 := by
    simpa [prefixWord, tailWord_203733, baseEnd_203733] using wordTrace_append hprefix tailTrace_203733
  have hstable : (prefixWord ++ tailWord_203733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203733).length < 2 ^ (prefixWord ++ tailWord_203733).sum := by decide
  have hdescent : baseEnd_203733 < baseStart_203733 := by decide
  rcases family_descends (prefixWord ++ tailWord_203733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203736 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_203736 : Nat := 118140960795 + 203736 * 2 ^ 59
def prefixEnd_203736 : Nat := 4983230072969 + 3 ^ 40 * 203736 * 2
def baseEnd_203736 : Nat := 104614494624520115663041

theorem tailTrace_203736 : CollatzResearch.WordTrace tailWord_203736 prefixEnd_203736 104614494624520115663041 := by
  unfold tailWord_203736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715431194953371091855531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4953908259937828122474041 3715431194953371091855531)
  ·
    refine ⟨5573146792430056637783297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3715431194953371091855531 5573146792430056637783297)
    ·
      refine ⟨4179860094322542478337473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5573146792430056637783297 4179860094322542478337473)
      ·
        refine ⟨3134895070741906858753105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4179860094322542478337473 3134895070741906858753105)
        ·
          refine ⟨2351171303056430144064829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134895070741906858753105 2351171303056430144064829)
          ·
            refine ⟨881689238646161304024311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2351171303056430144064829 881689238646161304024311)
            ·
              refine ⟨1322533857969241956036467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881689238646161304024311 1322533857969241956036467)
              ·
                refine ⟨1983800786953862934054701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322533857969241956036467 1983800786953862934054701)
                ·
                  refine ⟨743925295107698600270513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1983800786953862934054701 743925295107698600270513)
                  ·
                    refine ⟨557943971330773950202885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 743925295107698600270513 557943971330773950202885)
                    ·
                      refine ⟨104614494624520115663041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 557943971330773950202885 104614494624520115663041)
                      ·
                        rfl

theorem cell23_203736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_203736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203736 prefixEnd_203736 := by exact prefixLift 203736
  have htrace : WordTrace (prefixWord ++ tailWord_203736) baseStart_203736 baseEnd_203736 := by
    simpa [prefixWord, tailWord_203736, baseEnd_203736] using wordTrace_append hprefix tailTrace_203736
  have hstable : (prefixWord ++ tailWord_203736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203736).length < 2 ^ (prefixWord ++ tailWord_203736).sum := by decide
  have hdescent : baseEnd_203736 < baseStart_203736 := by decide
  rcases family_descends (prefixWord ++ tailWord_203736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203773 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_203773 : Nat := 118140960795 + 203773 * 2 ^ 59
def prefixEnd_203773 : Nat := 4983230072969 + 3 ^ 40 * 203773 * 2
def baseEnd_203773 : Nat := 104633493408736470900371

theorem tailTrace_203773 : CollatzResearch.WordTrace tailWord_203773 prefixEnd_203773 104633493408736470900371 := by
  unfold tailWord_203773
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432211890772697502807973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4954807927181798335205315 7432211890772697502807973)
  ·
    refine ⟨1393539729519880781776495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7432211890772697502807973 1393539729519880781776495)
    ·
      refine ⟨2090309594279821172664743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393539729519880781776495 2090309594279821172664743)
      ·
        refine ⟨3135464391419731758997115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090309594279821172664743 3135464391419731758997115)
        ·
          refine ⟨4703196587129597638495673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135464391419731758997115 4703196587129597638495673)
          ·
            refine ⟨3527397440347198228871755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4703196587129597638495673 3527397440347198228871755)
            ·
              refine ⟨5291096160520797343307633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527397440347198228871755 5291096160520797343307633)
              ·
                refine ⟨3968322120390598007480725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5291096160520797343307633 3968322120390598007480725)
                ·
                  refine ⟨186015099393309281600659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3968322120390598007480725 186015099393309281600659)
                  ·
                    refine ⟨279022649089963922400989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 186015099393309281600659 279022649089963922400989)
                    ·
                      refine ⟨104633493408736470900371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 279022649089963922400989 104633493408736470900371)
                      ·
                        rfl

theorem cell23_203773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_203773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203773 prefixEnd_203773 := by exact prefixLift 203773
  have htrace : WordTrace (prefixWord ++ tailWord_203773) baseStart_203773 baseEnd_203773 := by
    simpa [prefixWord, tailWord_203773, baseEnd_203773] using wordTrace_append hprefix tailTrace_203773
  have hstable : (prefixWord ++ tailWord_203773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203773).length < 2 ^ (prefixWord ++ tailWord_203773).sum := by decide
  have hdescent : baseEnd_203773 < baseStart_203773 := by decide
  rcases family_descends (prefixWord ++ tailWord_203773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203774 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_203774 : Nat := 118140960795 + 203774 * 2 ^ 59
def prefixEnd_203774 : Nat := 4983230072969 + 3 ^ 40 * 203774 * 2
def baseEnd_203774 : Nat := 104634006889390966987867

theorem tailTrace_203774 : CollatzResearch.WordTrace tailWord_203774 prefixEnd_203774 104634006889390966987867 := by
  unfold tailWord_203774
  simp only [CollatzResearch.WordTrace]
  refine ⟨929031045471134334199297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4954832242512716449062917 929031045471134334199297)
  ·
    refine ⟨696773284103350750649473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 929031045471134334199297 696773284103350750649473)
    ·
      refine ⟨522579963077513062987105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 696773284103350750649473 522579963077513062987105)
      ·
        refine ⟨391934972308134797240329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522579963077513062987105 391934972308134797240329)
        ·
          refine ⟨293951229231101097930247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391934972308134797240329 293951229231101097930247)
          ·
            refine ⟨440926843846651646895371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293951229231101097930247 440926843846651646895371)
            ·
              refine ⟨661390265769977470343057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440926843846651646895371 661390265769977470343057)
              ·
                refine ⟨496042699327483102757293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661390265769977470343057 496042699327483102757293)
                ·
                  refine ⟨186016012247806163533985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496042699327483102757293 186016012247806163533985)
                  ·
                    refine ⟨139512009185854622650489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186016012247806163533985 139512009185854622650489)
                    ·
                      refine ⟨104634006889390966987867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139512009185854622650489 104634006889390966987867)
                      ·
                        rfl

theorem cell23_203774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_203774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203774 prefixEnd_203774 := by exact prefixLift 203774
  have htrace : WordTrace (prefixWord ++ tailWord_203774) baseStart_203774 baseEnd_203774 := by
    simpa [prefixWord, tailWord_203774, baseEnd_203774] using wordTrace_append hprefix tailTrace_203774
  have hstable : (prefixWord ++ tailWord_203774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203774).length < 2 ^ (prefixWord ++ tailWord_203774).sum := by decide
  have hdescent : baseEnd_203774 < baseStart_203774 := by decide
  rcases family_descends (prefixWord ++ tailWord_203774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203807 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 3]
def baseStart_203807 : Nat := 118140960795 + 203807 * 2 ^ 59
def prefixEnd_203807 : Nat := 4983230072969 + 3 ^ 40 * 203807 * 2
def baseEnd_203807 : Nat := 104650951750989337875215

theorem tailTrace_203807 : CollatzResearch.WordTrace tailWord_203807 prefixEnd_203807 104650951750989337875215 := by
  unfold tailWord_203807
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433451972649521309545675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4955634648433014206363783 7433451972649521309545675)
  ·
    refine ⟨11150177958974281964318513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7433451972649521309545675 11150177958974281964318513)
    ·
      refine ⟨8362633469230711473238885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11150177958974281964318513 8362633469230711473238885)
      ·
        refine ⟨1567993775480758401232291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8362633469230711473238885 1567993775480758401232291)
        ·
          refine ⟨2351990663221137601848437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567993775480758401232291 2351990663221137601848437)
          ·
            refine ⟨220499124676981650173291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2351990663221137601848437 220499124676981650173291)
            ·
              refine ⟨330748687015472475259937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220499124676981650173291 330748687015472475259937)
              ·
                refine ⟨248061515261604356444953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330748687015472475259937 248061515261604356444953)
                ·
                  refine ⟨186046136446203267333715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248061515261604356444953 186046136446203267333715)
                  ·
                    refine ⟨279069204669304901000573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 186046136446203267333715 279069204669304901000573)
                    ·
                      refine ⟨104650951750989337875215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 279069204669304901000573 104650951750989337875215)
                      ·
                        rfl

theorem cell23_203807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_203807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203807 prefixEnd_203807 := by exact prefixLift 203807
  have htrace : WordTrace (prefixWord ++ tailWord_203807) baseStart_203807 baseEnd_203807 := by
    simpa [prefixWord, tailWord_203807, baseEnd_203807] using wordTrace_append hprefix tailTrace_203807
  have hstable : (prefixWord ++ tailWord_203807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203807).length < 2 ^ (prefixWord ++ tailWord_203807).sum := by decide
  have hdescent : baseEnd_203807 < baseStart_203807 := by decide
  rcases family_descends (prefixWord ++ tailWord_203807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203866 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_203866 : Nat := 118140960795 + 203866 * 2 ^ 59
def prefixEnd_203866 : Nat := 4983230072969 + 3 ^ 40 * 203866 * 2
def baseEnd_203866 : Nat := 34893749036534869012481

theorem tailTrace_203866 : CollatzResearch.WordTrace tailWord_203866 prefixEnd_203866 34893749036534869012481 := by
  unfold tailWord_203866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858900969858943596485863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4957069252957182923962301 1858900969858943596485863)
  ·
    refine ⟨2788351454788415394728795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858900969858943596485863 2788351454788415394728795)
    ·
      refine ⟨4182527182182623092093193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788351454788415394728795 4182527182182623092093193)
      ·
        refine ⟨3136895386636967319069895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4182527182182623092093193 3136895386636967319069895)
        ·
          refine ⟨4705343079955450978604843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136895386636967319069895 4705343079955450978604843)
          ·
            refine ⟨7058014619933176467907265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705343079955450978604843 7058014619933176467907265)
            ·
              refine ⟨5293510964949882350930449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7058014619933176467907265 5293510964949882350930449)
              ·
                refine ⟨3970133223712411763197837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5293510964949882350930449 3970133223712411763197837)
                ·
                  refine ⟨1488799958892154411199189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3970133223712411763197837 1488799958892154411199189)
                  ·
                    refine ⟨34893749036534869012481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1488799958892154411199189 34893749036534869012481)
                    ·
                      rfl

theorem cell23_203866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_203866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203866 prefixEnd_203866 := by exact prefixLift 203866
  have htrace : WordTrace (prefixWord ++ tailWord_203866) baseStart_203866 baseEnd_203866 := by
    simpa [prefixWord, tailWord_203866, baseEnd_203866] using wordTrace_append hprefix tailTrace_203866
  have hstable : (prefixWord ++ tailWord_203866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203866).length < 2 ^ (prefixWord ++ tailWord_203866).sum := by decide
  have hdescent : baseEnd_203866 < baseStart_203866 := by decide
  rcases family_descends (prefixWord ++ tailWord_203866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203896 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 2, 8]
def baseStart_203896 : Nat := 118140960795 + 203896 * 2 ^ 59
def prefixEnd_203896 : Nat := 4983230072969 + 3 ^ 40 * 203896 * 2
def baseEnd_203896 : Nat := 34898883843079829887435

theorem tailTrace_203896 : CollatzResearch.WordTrace tailWord_203896 prefixEnd_203896 34898883843079829887435 := by
  unfold tailWord_203896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718349034663544754767771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4957798712884726339690361 3718349034663544754767771)
  ·
    refine ⟨5577523551995317132151657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3718349034663544754767771 5577523551995317132151657)
    ·
      refine ⟨4183142663996487849113743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5577523551995317132151657 4183142663996487849113743)
      ·
        refine ⟨6274713995994731773670615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183142663996487849113743 6274713995994731773670615)
        ·
          refine ⟨9412070993992097660505923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6274713995994731773670615 9412070993992097660505923)
          ·
            refine ⟨14118106490988146490758885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9412070993992097660505923 14118106490988146490758885)
            ·
              refine ⟨2647144967060277467017291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14118106490988146490758885 2647144967060277467017291)
              ·
                refine ⟨3970717450590416200525937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647144967060277467017291 3970717450590416200525937)
                ·
                  refine ⟨2978038087942812150394453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3970717450590416200525937 2978038087942812150394453)
                  ·
                    refine ⟨34898883843079829887435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2978038087942812150394453 34898883843079829887435)
                    ·
                      rfl

theorem cell23_203896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_203896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203896 prefixEnd_203896 := by exact prefixLift 203896
  have htrace : WordTrace (prefixWord ++ tailWord_203896) baseStart_203896 baseEnd_203896 := by
    simpa [prefixWord, tailWord_203896, baseEnd_203896] using wordTrace_append hprefix tailTrace_203896
  have hstable : (prefixWord ++ tailWord_203896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203896).length < 2 ^ (prefixWord ++ tailWord_203896).sum := by decide
  have hdescent : baseEnd_203896 < baseStart_203896 := by decide
  rcases family_descends (prefixWord ++ tailWord_203896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203964 : List Nat := [2, 2, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_203964 : Nat := 118140960795 + 203964 * 2 ^ 59
def prefixEnd_203964 : Nat := 4983230072969 + 3 ^ 40 * 203964 * 2
def baseEnd_203964 : Nat := 34910522737915074537331

theorem tailTrace_203964 : CollatzResearch.WordTrace tailWord_203964 prefixEnd_203964 34910522737915074537331 := by
  unfold tailWord_203964
  simp only [CollatzResearch.WordTrace]
  refine ⟨3719589116540368561505473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4959452155387158082007297 3719589116540368561505473)
  ·
    refine ⟨2789691837405276421129105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3719589116540368561505473 2789691837405276421129105)
    ·
      refine ⟨2092268878053957315846829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2789691837405276421129105 2092268878053957315846829)
      ·
        refine ⟨784600829270233993442561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2092268878053957315846829 784600829270233993442561)
        ·
          refine ⟨588450621952675495081921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784600829270233993442561 588450621952675495081921)
          ·
            refine ⟨441337966464506621311441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588450621952675495081921 441337966464506621311441)
            ·
              refine ⟨331003474848379965983581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441337966464506621311441 331003474848379965983581)
              ·
                refine ⟨124126303068142487243843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331003474848379965983581 124126303068142487243843)
                ·
                  refine ⟨186189454602213730865765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124126303068142487243843 186189454602213730865765)
                  ·
                    refine ⟨34910522737915074537331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186189454602213730865765 34910522737915074537331)
                    ·
                      rfl

theorem cell23_203964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_203964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203964 prefixEnd_203964 := by exact prefixLift 203964
  have htrace : WordTrace (prefixWord ++ tailWord_203964) baseStart_203964 baseEnd_203964 := by
    simpa [prefixWord, tailWord_203964, baseEnd_203964] using wordTrace_append hprefix tailTrace_203964
  have hstable : (prefixWord ++ tailWord_203964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203964).length < 2 ^ (prefixWord ++ tailWord_203964).sum := by decide
  have hdescent : baseEnd_203964 < baseStart_203964 := by decide
  rcases family_descends (prefixWord ++ tailWord_203964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203981 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_203981 : Nat := 118140960795 + 203981 * 2 ^ 59
def prefixEnd_203981 : Nat := 4983230072969 + 3 ^ 40 * 203981 * 2
def baseEnd_203981 : Nat := 34913432461623885699805

theorem tailTrace_203981 : CollatzResearch.WordTrace tailWord_203981 prefixEnd_203981 34913432461623885699805 := by
  unfold tailWord_203981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7439798274019149026379797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4959865516012766017586531 7439798274019149026379797)
  ·
    refine ⟨348740544094647610611553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7439798274019149026379797 348740544094647610611553)
    ·
      refine ⟨261555408070985707958665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348740544094647610611553 261555408070985707958665)
      ·
        refine ⟨196166556053239280968999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261555408070985707958665 196166556053239280968999)
        ·
          refine ⟨294249834079858921453499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196166556053239280968999 294249834079858921453499)
          ·
            refine ⟨441374751119788382180249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294249834079858921453499 441374751119788382180249)
            ·
              refine ⟨331031063339841286635187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441374751119788382180249 331031063339841286635187)
              ·
                refine ⟨496546595009761929952781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331031063339841286635187 496546595009761929952781)
                ·
                  refine ⟨186204973128660723732293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496546595009761929952781 186204973128660723732293)
                  ·
                    refine ⟨34913432461623885699805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186204973128660723732293 34913432461623885699805)
                    ·
                      rfl

theorem cell23_203981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_203981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_203981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_203981 prefixEnd_203981 := by exact prefixLift 203981
  have htrace : WordTrace (prefixWord ++ tailWord_203981) baseStart_203981 baseEnd_203981 := by
    simpa [prefixWord, tailWord_203981, baseEnd_203981] using wordTrace_append hprefix tailTrace_203981
  have hstable : (prefixWord ++ tailWord_203981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203981).length < 2 ^ (prefixWord ++ tailWord_203981).sum := by decide
  have hdescent : baseEnd_203981 < baseStart_203981 := by decide
  rcases family_descends (prefixWord ++ tailWord_203981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204033 : List Nat := [1, 2, 4, 1, 1, 3, 11]
def baseStart_204033 : Nat := 118140960795 + 204033 * 2 ^ 59
def prefixEnd_204033 : Nat := 4983230072969 + 3 ^ 40 * 204033 * 2
def baseEnd_204033 : Nat := 1293419733072906835175

theorem tailTrace_204033 : CollatzResearch.WordTrace tailWord_204033 prefixEnd_204033 1293419733072906835175 := by
  unfold tailWord_204033
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441694869830761907272753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4961129913220507938181835 7441694869830761907272753)
  ·
    refine ⟨5581271152373071430454565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7441694869830761907272753 5581271152373071430454565)
    ·
      refine ⟨1046488341069950893210231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5581271152373071430454565 1046488341069950893210231)
      ·
        refine ⟨1569732511604926339815347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046488341069950893210231 1569732511604926339815347)
        ·
          refine ⟨2354598767407389509723021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569732511604926339815347 2354598767407389509723021)
          ·
            refine ⟨882974537777771066146133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2354598767407389509723021 882974537777771066146133)
            ·
              refine ⟨1293419733072906835175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 882974537777771066146133 1293419733072906835175)
              ·
                rfl

theorem cell23_204033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 11].length) (baseStart_204033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204033 prefixEnd_204033 := by exact prefixLift 204033
  have htrace : WordTrace (prefixWord ++ tailWord_204033) baseStart_204033 baseEnd_204033 := by
    simpa [prefixWord, tailWord_204033, baseEnd_204033] using wordTrace_append hprefix tailTrace_204033
  have hstable : (prefixWord ++ tailWord_204033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204033).length < 2 ^ (prefixWord ++ tailWord_204033).sum := by decide
  have hdescent : baseEnd_204033 < baseStart_204033 := by decide
  rcases family_descends (prefixWord ++ tailWord_204033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204044 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 3, 2, 2]
def baseStart_204044 : Nat := 118140960795 + 204044 * 2 ^ 59
def prefixEnd_204044 : Nat := 4983230072969 + 3 ^ 40 * 204044 * 2
def baseEnd_204044 : Nat := 104772646666104910611625

theorem tailTrace_204044 : CollatzResearch.WordTrace tailWord_204044 prefixEnd_204044 104772646666104910611625 := by
  unfold tailWord_204044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721048036395455392961593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4961397381860607190615457 3721048036395455392961593)
  ·
    refine ⟨2790786027296591544721195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3721048036395455392961593 2790786027296591544721195)
    ·
      refine ⟨4186179040944887317081793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790786027296591544721195 4186179040944887317081793)
      ·
        refine ⟨3139634280708665487811345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4186179040944887317081793 3139634280708665487811345)
        ·
          refine ⟨2354725710531499115858509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3139634280708665487811345 2354725710531499115858509)
          ·
            refine ⟨883022141449312168446941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2354725710531499115858509 883022141449312168446941)
            ·
              refine ⟨331133303043492063167603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883022141449312168446941 331133303043492063167603)
              ·
                refine ⟨496699954565238094751405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331133303043492063167603 496699954565238094751405)
                ·
                  refine ⟨186262482961964285531777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496699954565238094751405 186262482961964285531777)
                  ·
                    refine ⟨139696862221473214148833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186262482961964285531777 139696862221473214148833)
                    ·
                      refine ⟨104772646666104910611625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139696862221473214148833 104772646666104910611625)
                      ·
                        rfl

theorem cell23_204044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_204044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204044 prefixEnd_204044 := by exact prefixLift 204044
  have htrace : WordTrace (prefixWord ++ tailWord_204044) baseStart_204044 baseEnd_204044 := by
    simpa [prefixWord, tailWord_204044, baseEnd_204044] using wordTrace_append hprefix tailTrace_204044
  have hstable : (prefixWord ++ tailWord_204044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204044).length < 2 ^ (prefixWord ++ tailWord_204044).sum := by decide
  have hdescent : baseEnd_204044 < baseStart_204044 := by decide
  rcases family_descends (prefixWord ++ tailWord_204044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204053 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_204053 : Nat := 118140960795 + 204053 * 2 ^ 59
def prefixEnd_204053 : Nat := 4983230072969 + 3 ^ 40 * 204053 * 2
def baseEnd_204053 : Nat := 104777267991995375399083

theorem tailTrace_204053 : CollatzResearch.WordTrace tailWord_204053 prefixEnd_204053 104777267991995375399083 := by
  unfold tailWord_204053
  simp only [CollatzResearch.WordTrace]
  refine ⟨7442424329758305323000813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4961616219838870215333875 7442424329758305323000813)
  ·
    refine ⟨2790909123659364496125305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7442424329758305323000813 2790909123659364496125305)
    ·
      refine ⟨2093181842744523372093979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2790909123659364496125305 2093181842744523372093979)
      ·
        refine ⟨3139772764116785058140969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093181842744523372093979 3139772764116785058140969)
        ·
          refine ⟨2354829573087588793605727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3139772764116785058140969 2354829573087588793605727)
          ·
            refine ⟨3532244359631383190408591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354829573087588793605727 3532244359631383190408591)
            ·
              refine ⟨5298366539447074785612887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532244359631383190408591 5298366539447074785612887)
              ·
                refine ⟨7947549809170612178419331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5298366539447074785612887 7947549809170612178419331)
                ·
                  refine ⟨11921324713755918267628997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7947549809170612178419331 11921324713755918267628997)
                  ·
                    refine ⟨2235248383829234675180437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11921324713755918267628997 2235248383829234675180437)
                    ·
                      refine ⟨104777267991995375399083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2235248383829234675180437 104777267991995375399083)
                      ·
                        rfl

theorem cell23_204053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_204053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204053 prefixEnd_204053 := by exact prefixLift 204053
  have htrace : WordTrace (prefixWord ++ tailWord_204053) baseStart_204053 baseEnd_204053 := by
    simpa [prefixWord, tailWord_204053, baseEnd_204053] using wordTrace_append hprefix tailTrace_204053
  have hstable : (prefixWord ++ tailWord_204053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204053).length < 2 ^ (prefixWord ++ tailWord_204053).sum := by decide
  have hdescent : baseEnd_204053 < baseStart_204053 := by decide
  rcases family_descends (prefixWord ++ tailWord_204053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204073 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_204073 : Nat := 118140960795 + 204073 * 2 ^ 59
def prefixEnd_204073 : Nat := 4983230072969 + 3 ^ 40 * 204073 * 2
def baseEnd_204073 : Nat := 104787537605085297148991

theorem tailTrace_204073 : CollatzResearch.WordTrace tailWord_204073 prefixEnd_204073 104787537605085297148991 := by
  unfold tailWord_204073
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443153789685848738728873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4962102526457232492485915 7443153789685848738728873)
  ·
    refine ⟨5582365342264386554046655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7443153789685848738728873 5582365342264386554046655)
    ·
      refine ⟨8373548013396579831069983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5582365342264386554046655 8373548013396579831069983)
      ·
        refine ⟨12560322020094869746604975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8373548013396579831069983 12560322020094869746604975)
        ·
          refine ⟨18840483030142304619907463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12560322020094869746604975 18840483030142304619907463)
          ·
            refine ⟨28260724545213456929861195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18840483030142304619907463 28260724545213456929861195)
            ·
              refine ⟨42391086817820185394791793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28260724545213456929861195 42391086817820185394791793)
              ·
                refine ⟨31793315113365139046093845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42391086817820185394791793 31793315113365139046093845)
                ·
                  refine ⟨1490311645938990892785649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31793315113365139046093845 1490311645938990892785649)
                  ·
                    refine ⟨1117733734454243169589237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1490311645938990892785649 1117733734454243169589237)
                    ·
                      refine ⟨104787537605085297148991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1117733734454243169589237 104787537605085297148991)
                      ·
                        rfl

theorem cell23_204073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_204073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204073 prefixEnd_204073 := by exact prefixLift 204073
  have htrace : WordTrace (prefixWord ++ tailWord_204073) baseStart_204073 baseEnd_204073 := by
    simpa [prefixWord, tailWord_204073, baseEnd_204073] using wordTrace_append hprefix tailTrace_204073
  have hstable : (prefixWord ++ tailWord_204073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204073).length < 2 ^ (prefixWord ++ tailWord_204073).sum := by decide
  have hdescent : baseEnd_204073 < baseStart_204073 := by decide
  rcases family_descends (prefixWord ++ tailWord_204073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204110 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_204110 : Nat := 118140960795 + 204110 * 2 ^ 59
def prefixEnd_204110 : Nat := 4983230072969 + 3 ^ 40 * 204110 * 2
def baseEnd_204110 : Nat := 34935512129767217462107

theorem tailTrace_204110 : CollatzResearch.WordTrace tailWord_204110 prefixEnd_204110 34935512129767217462107 := by
  unfold tailWord_204110
  simp only [CollatzResearch.WordTrace]
  refine ⟨930562911318975507228223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4963002193701202705217189 930562911318975507228223)
  ·
    refine ⟨1395844366978463260842335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 930562911318975507228223 1395844366978463260842335)
    ·
      refine ⟨2093766550467694891263503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395844366978463260842335 2093766550467694891263503)
      ·
        refine ⟨3140649825701542336895255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093766550467694891263503 3140649825701542336895255)
        ·
          refine ⟨4710974738552313505342883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140649825701542336895255 4710974738552313505342883)
          ·
            refine ⟨7066462107828470258014325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710974738552313505342883 7066462107828470258014325)
            ·
              refine ⟨662480822608919086688843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7066462107828470258014325 662480822608919086688843)
              ·
                refine ⟨993721233913378630033265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662480822608919086688843 993721233913378630033265)
                ·
                  refine ⟨745290925435033972524949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 993721233913378630033265 745290925435033972524949)
                  ·
                    refine ⟨34935512129767217462107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 745290925435033972524949 34935512129767217462107)
                    ·
                      rfl

theorem cell23_204110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_204110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204110 prefixEnd_204110 := by exact prefixLift 204110
  have htrace : WordTrace (prefixWord ++ tailWord_204110) baseStart_204110 baseEnd_204110 := by
    simpa [prefixWord, tailWord_204110, baseEnd_204110] using wordTrace_append hprefix tailTrace_204110
  have hstable : (prefixWord ++ tailWord_204110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204110).length < 2 ^ (prefixWord ++ tailWord_204110).sum := by decide
  have hdescent : baseEnd_204110 < baseStart_204110 := by decide
  rcases family_descends (prefixWord ++ tailWord_204110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204118 : List Nat := [5, 2, 3, 1, 1, 1, 3, 7]
def baseStart_204118 : Nat := 118140960795 + 204118 * 2 ^ 59
def prefixEnd_204118 : Nat := 4983230072969 + 3 ^ 40 * 204118 * 2
def baseEnd_204118 : Nat := 3881875712390282262455

theorem tailTrace_204118 : CollatzResearch.WordTrace tailWord_204118 prefixEnd_204118 3881875712390282262455 := by
  unfold tailWord_204118
  simp only [CollatzResearch.WordTrace]
  refine ⟨465299692157676339007313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4963196716348547616078005 465299692157676339007313)
  ·
    refine ⟨348974769118257254255485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 465299692157676339007313 348974769118257254255485)
    ·
      refine ⟨130865538419346470345807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348974769118257254255485 130865538419346470345807)
      ·
        refine ⟨196298307629019705518711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130865538419346470345807 196298307629019705518711)
        ·
          refine ⟨294447461443529558278067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196298307629019705518711 294447461443529558278067)
          ·
            refine ⟨441671192165294337417101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294447461443529558278067 441671192165294337417101)
            ·
              refine ⟨165626697061985376531413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441671192165294337417101 165626697061985376531413)
              ·
                refine ⟨3881875712390282262455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165626697061985376531413 3881875712390282262455)
                ·
                  rfl

theorem cell23_204118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_204118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204118 prefixEnd_204118 := by exact prefixLift 204118
  have htrace : WordTrace (prefixWord ++ tailWord_204118) baseStart_204118 baseEnd_204118 := by
    simpa [prefixWord, tailWord_204118, baseEnd_204118] using wordTrace_append hprefix tailTrace_204118
  have hstable : (prefixWord ++ tailWord_204118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204118).length < 2 ^ (prefixWord ++ tailWord_204118).sum := by decide
  have hdescent : baseEnd_204118 < baseStart_204118 := by decide
  rcases family_descends (prefixWord ++ tailWord_204118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204120 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_204120 : Nat := 118140960795 + 204120 * 2 ^ 59
def prefixEnd_204120 : Nat := 4983230072969 + 3 ^ 40 * 204120 * 2
def baseEnd_204120 : Nat := 104811671195846613261275

theorem tailTrace_204120 : CollatzResearch.WordTrace tailWord_204120 prefixEnd_204120 104811671195846613261275 := by
  unfold tailWord_204120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722434010257787882844907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4963245347010383843793209 3722434010257787882844907)
  ·
    refine ⟨5583651015386681824267361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3722434010257787882844907 5583651015386681824267361)
    ·
      refine ⟨4187738261540011368200521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5583651015386681824267361 4187738261540011368200521)
      ·
        refine ⟨3140803696155008526150391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4187738261540011368200521 3140803696155008526150391)
        ·
          refine ⟨4711205544232512789225587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140803696155008526150391 4711205544232512789225587)
          ·
            refine ⟨7066808316348769183838381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711205544232512789225587 7066808316348769183838381)
            ·
              refine ⟨2650053118630788443939393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7066808316348769183838381 2650053118630788443939393)
              ·
                refine ⟨1987539838973091332954545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2650053118630788443939393 1987539838973091332954545)
                ·
                  refine ⟨1490654879229818499715909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987539838973091332954545 1490654879229818499715909)
                  ·
                    refine ⟨279497789855590968696733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490654879229818499715909 279497789855590968696733)
                    ·
                      refine ⟨104811671195846613261275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 279497789855590968696733 104811671195846613261275)
                      ·
                        rfl

theorem cell23_204120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_204120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204120 prefixEnd_204120 := by exact prefixLift 204120
  have htrace : WordTrace (prefixWord ++ tailWord_204120) baseStart_204120 baseEnd_204120 := by
    simpa [prefixWord, tailWord_204120, baseEnd_204120] using wordTrace_append hprefix tailTrace_204120
  have hstable : (prefixWord ++ tailWord_204120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204120).length < 2 ^ (prefixWord ++ tailWord_204120).sum := by decide
  have hdescent : baseEnd_204120 < baseStart_204120 := by decide
  rcases family_descends (prefixWord ++ tailWord_204120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204157 : List Nat := [1, 4, 1, 1, 2, 2, 1, 6, 5]
def baseStart_204157 : Nat := 118140960795 + 204157 * 2 ^ 59
def prefixEnd_204157 : Nat := 4983230072969 + 3 ^ 40 * 204157 * 2
def baseEnd_204157 : Nat := 11647852220006996499845

theorem tailTrace_204157 : CollatzResearch.WordTrace tailWord_204157 prefixEnd_204157 11647852220006996499845 := by
  unfold tailWord_204157
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446217521381531084786725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4964145014254354056524483 7446217521381531084786725)
  ·
    refine ⟨1396165785259037078397511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7446217521381531084786725 1396165785259037078397511)
    ·
      refine ⟨2094248677888555617596267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1396165785259037078397511 2094248677888555617596267)
      ·
        refine ⟨3141373016832833426394401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094248677888555617596267 3141373016832833426394401)
        ·
          refine ⟨2356029762624625069795801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3141373016832833426394401 2356029762624625069795801)
          ·
            refine ⟨1767022321968468802346851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2356029762624625069795801 1767022321968468802346851)
            ·
              refine ⟨2650533482952703203520277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767022321968468802346851 2650533482952703203520277)
              ·
                refine ⟨124243757013407962665013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2650533482952703203520277 124243757013407962665013)
                ·
                  refine ⟨11647852220006996499845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124243757013407962665013 11647852220006996499845)
                  ·
                    rfl

theorem cell23_204157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_204157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204157 prefixEnd_204157 := by exact prefixLift 204157
  have htrace : WordTrace (prefixWord ++ tailWord_204157) baseStart_204157 baseEnd_204157 := by
    simpa [prefixWord, tailWord_204157, baseEnd_204157] using wordTrace_append hprefix tailTrace_204157
  have hstable : (prefixWord ++ tailWord_204157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204157).length < 2 ^ (prefixWord ++ tailWord_204157).sum := by decide
  have hdescent : baseEnd_204157 < baseStart_204157 := by decide
  rcases family_descends (prefixWord ++ tailWord_204157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204167 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_204167 : Nat := 118140960795 + 204167 * 2 ^ 59
def prefixEnd_204167 : Nat := 4983230072969 + 3 ^ 40 * 204167 * 2
def baseEnd_204167 : Nat := 104835804786607929373559

theorem tailTrace_204167 : CollatzResearch.WordTrace tailWord_204167 prefixEnd_204167 104835804786607929373559 := by
  unfold tailWord_204167
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446582251345302792650755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4964388167563535195100503 7446582251345302792650755)
  ·
    refine ⟨11169873377017954188976133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7446582251345302792650755 11169873377017954188976133)
    ·
      refine ⟨2094351258190866410433025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11169873377017954188976133 2094351258190866410433025)
      ·
        refine ⟨1570763443643149807824769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2094351258190866410433025 1570763443643149807824769)
        ·
          refine ⟨1178072582732362355868577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570763443643149807824769 1178072582732362355868577)
          ·
            refine ⟨883554437049271766901433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178072582732362355868577 883554437049271766901433)
            ·
              refine ⟨662665827786953825176075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883554437049271766901433 662665827786953825176075)
              ·
                refine ⟨993998741680430737764113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662665827786953825176075 993998741680430737764113)
                ·
                  refine ⟨745499056260323053323085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 993998741680430737764113 745499056260323053323085)
                  ·
                    refine ⟨279562146097621144996157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745499056260323053323085 279562146097621144996157)
                    ·
                      refine ⟨104835804786607929373559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 279562146097621144996157 104835804786607929373559)
                      ·
                        rfl

theorem cell23_204167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_204167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204167 prefixEnd_204167 := by exact prefixLift 204167
  have htrace : WordTrace (prefixWord ++ tailWord_204167) baseStart_204167 baseEnd_204167 := by
    simpa [prefixWord, tailWord_204167, baseEnd_204167] using wordTrace_append hprefix tailTrace_204167
  have hstable : (prefixWord ++ tailWord_204167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204167).length < 2 ^ (prefixWord ++ tailWord_204167).sum := by decide
  have hdescent : baseEnd_204167 < baseStart_204167 := by decide
  rcases family_descends (prefixWord ++ tailWord_204167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204168 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_204168 : Nat := 118140960795 + 204168 * 2 ^ 59
def prefixEnd_204168 : Nat := 4983230072969 + 3 ^ 40 * 204168 * 2
def baseEnd_204168 : Nat := 104836318267262425461055

theorem tailTrace_204168 : CollatzResearch.WordTrace tailWord_204168 prefixEnd_204168 104836318267262425461055 := by
  unfold tailWord_204168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723309362170839981718579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4964412482894453308958105 3723309362170839981718579)
  ·
    refine ⟨5584964043256259972577869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3723309362170839981718579 5584964043256259972577869)
    ·
      refine ⟨2094361516221097489716701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5584964043256259972577869 2094361516221097489716701)
      ·
        refine ⟨785385568582911558643763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2094361516221097489716701 785385568582911558643763)
        ·
          refine ⟨1178078352874367337965645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785385568582911558643763 1178078352874367337965645)
          ·
            refine ⟨441779382327887751737117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1178078352874367337965645 441779382327887751737117)
            ·
              refine ⟨165667268372957906901419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441779382327887751737117 165667268372957906901419)
              ·
                refine ⟨248500902559436860352129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165667268372957906901419 248500902559436860352129)
                ·
                  refine ⟨186375676919577645264097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248500902559436860352129 186375676919577645264097)
                  ·
                    refine ⟨139781757689683233948073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186375676919577645264097 139781757689683233948073)
                    ·
                      refine ⟨104836318267262425461055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139781757689683233948073 104836318267262425461055)
                      ·
                        rfl

theorem cell23_204168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_204168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204168 prefixEnd_204168 := by exact prefixLift 204168
  have htrace : WordTrace (prefixWord ++ tailWord_204168) baseStart_204168 baseEnd_204168 := by
    simpa [prefixWord, tailWord_204168, baseEnd_204168] using wordTrace_append hprefix tailTrace_204168
  have hstable : (prefixWord ++ tailWord_204168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204168).length < 2 ^ (prefixWord ++ tailWord_204168).sum := by decide
  have hdescent : baseEnd_204168 < baseStart_204168 := by decide
  rcases family_descends (prefixWord ++ tailWord_204168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204207 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 4, 4, 2]
def baseStart_204207 : Nat := 118140960795 + 204207 * 2 ^ 59
def prefixEnd_204207 : Nat := 4983230072969 + 3 ^ 40 * 204207 * 2
def baseEnd_204207 : Nat := 104856344012787772873375

theorem tailTrace_204207 : CollatzResearch.WordTrace tailWord_204207 prefixEnd_204207 104856344012787772873375 := by
  unfold tailWord_204207
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448041171200389624106875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4965360780800259749404583 7448041171200389624106875)
  ·
    refine ⟨11172061756800584436160313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7448041171200389624106875 11172061756800584436160313)
    ·
      refine ⟨8379046317600438327120235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11172061756800584436160313 8379046317600438327120235)
      ·
        refine ⟨12568569476400657490680353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8379046317600438327120235 12568569476400657490680353)
        ·
          refine ⟨9426427107300493118010265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12568569476400657490680353 9426427107300493118010265)
          ·
            refine ⟨7069820330475369838507699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9426427107300493118010265 7069820330475369838507699)
            ·
              refine ⟨10604730495713054757761549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069820330475369838507699 10604730495713054757761549)
              ·
                refine ⟨3976773935892395534160581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10604730495713054757761549 3976773935892395534160581)
                ·
                  refine ⟨745645112979824162655109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3976773935892395534160581 745645112979824162655109)
                  ·
                    refine ⟨139808458683717030497833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745645112979824162655109 139808458683717030497833)
                    ·
                      refine ⟨104856344012787772873375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139808458683717030497833 104856344012787772873375)
                      ·
                        rfl

theorem cell23_204207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4, 2].length) (baseStart_204207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204207 prefixEnd_204207 := by exact prefixLift 204207
  have htrace : WordTrace (prefixWord ++ tailWord_204207) baseStart_204207 baseEnd_204207 := by
    simpa [prefixWord, tailWord_204207, baseEnd_204207] using wordTrace_append hprefix tailTrace_204207
  have hstable : (prefixWord ++ tailWord_204207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204207).length < 2 ^ (prefixWord ++ tailWord_204207).sum := by decide
  have hdescent : baseEnd_204207 < baseStart_204207 := by decide
  rcases family_descends (prefixWord ++ tailWord_204207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204210 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_204210 : Nat := 118140960795 + 204210 * 2 ^ 59
def prefixEnd_204210 : Nat := 4983230072969 + 3 ^ 40 * 204210 * 2
def baseEnd_204210 : Nat := 104857884454751261135861

theorem tailTrace_204210 : CollatzResearch.WordTrace tailWord_204210 prefixEnd_204210 104857884454751261135861 := by
  unfold tailWord_204210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1862037647547380284116521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4965433726793014090977389 1862037647547380284116521)
  ·
    refine ⟨1396528235660535213087391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1862037647547380284116521 1396528235660535213087391)
    ·
      refine ⟨2094792353490802819631087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1396528235660535213087391 2094792353490802819631087)
      ·
        refine ⟨3142188530236204229446631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094792353490802819631087 3142188530236204229446631)
        ·
          refine ⟨4713282795354306344169947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142188530236204229446631 4713282795354306344169947)
          ·
            refine ⟨7069924193031459516254921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713282795354306344169947 7069924193031459516254921)
            ·
              refine ⟨5302443144773594637191191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7069924193031459516254921 5302443144773594637191191)
              ·
                refine ⟨7953664717160391955786787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5302443144773594637191191 7953664717160391955786787)
                ·
                  refine ⟨11930497075740587933680181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7953664717160391955786787 11930497075740587933680181)
                  ·
                    refine ⟨1118484100850680118782517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11930497075740587933680181 1118484100850680118782517)
                    ·
                      refine ⟨104857884454751261135861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1118484100850680118782517 104857884454751261135861)
                      ·
                        rfl

theorem cell23_204210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_204210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204210 prefixEnd_204210 := by exact prefixLift 204210
  have htrace : WordTrace (prefixWord ++ tailWord_204210) baseStart_204210 baseEnd_204210 := by
    simpa [prefixWord, tailWord_204210, baseEnd_204210] using wordTrace_append hprefix tailTrace_204210
  have hstable : (prefixWord ++ tailWord_204210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204210).length < 2 ^ (prefixWord ++ tailWord_204210).sum := by decide
  have hdescent : baseEnd_204210 < baseStart_204210 := by decide
  rcases family_descends (prefixWord ++ tailWord_204210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204284 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_204284 : Nat := 118140960795 + 204284 * 2 ^ 59
def prefixEnd_204284 : Nat := 4983230072969 + 3 ^ 40 * 204284 * 2
def baseEnd_204284 : Nat := 104895882023183971610521

theorem tailTrace_204284 : CollatzResearch.WordTrace tailWord_204284 prefixEnd_204284 104895882023183971610521 := by
  unfold tailWord_204284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3725424795960715887329953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4967233061280954516439937 3725424795960715887329953)
  ·
    refine ⟨2794068596970536915497465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3725424795960715887329953 2794068596970536915497465)
    ·
      refine ⟨2095551447727902686623099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2794068596970536915497465 2095551447727902686623099)
      ·
        refine ⟨3143327171591854029934649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095551447727902686623099 3143327171591854029934649)
        ·
          refine ⟨2357495378693890522450987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143327171591854029934649 2357495378693890522450987)
          ·
            refine ⟨3536243068040835783676481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357495378693890522450987 3536243068040835783676481)
            ·
              refine ⟨2652182301030626837757361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536243068040835783676481 2652182301030626837757361)
              ·
                refine ⟨1989136725772970128318021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652182301030626837757361 1989136725772970128318021)
                ·
                  refine ⟨372963136082431899059629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989136725772970128318021 372963136082431899059629)
                  ·
                    refine ⟨139861176030911962147361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372963136082431899059629 139861176030911962147361)
                    ·
                      refine ⟨104895882023183971610521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139861176030911962147361 104895882023183971610521)
                      ·
                        rfl

theorem cell23_204284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_204284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204284 prefixEnd_204284 := by exact prefixLift 204284
  have htrace : WordTrace (prefixWord ++ tailWord_204284) baseStart_204284 baseEnd_204284 := by
    simpa [prefixWord, tailWord_204284, baseEnd_204284] using wordTrace_append hprefix tailTrace_204284
  have hstable : (prefixWord ++ tailWord_204284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204284).length < 2 ^ (prefixWord ++ tailWord_204284).sum := by decide
  have hdescent : baseEnd_204284 < baseStart_204284 := by decide
  rcases family_descends (prefixWord ++ tailWord_204284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204297 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_204297 : Nat := 118140960795 + 204297 * 2 ^ 59
def prefixEnd_204297 : Nat := 4983230072969 + 3 ^ 40 * 204297 * 2
def baseEnd_204297 : Nat := 104902557271692420747961

theorem tailTrace_204297 : CollatzResearch.WordTrace tailWord_204297 prefixEnd_204297 104902557271692420747961 := by
  unfold tailWord_204297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7451323740874334994883145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4967549160582889996588763 7451323740874334994883145)
  ·
    refine ⟨5588492805655751246162359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7451323740874334994883145 5588492805655751246162359)
    ·
      refine ⟨8382739208483626869243539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588492805655751246162359 8382739208483626869243539)
      ·
        refine ⟨12574108812725440303865309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8382739208483626869243539 12574108812725440303865309)
        ·
          refine ⟨4715290804772040113949491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12574108812725440303865309 4715290804772040113949491)
          ·
            refine ⟨7072936207158060170924237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715290804772040113949491 7072936207158060170924237)
            ·
              refine ⟨2652351077684272564096589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7072936207158060170924237 2652351077684272564096589)
              ·
                refine ⟨994631654131602211536221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2652351077684272564096589 994631654131602211536221)
                ·
                  refine ⟨372986870299350829326083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994631654131602211536221 372986870299350829326083)
                  ·
                    refine ⟨559480305449026243989125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 372986870299350829326083 559480305449026243989125)
                    ·
                      refine ⟨104902557271692420747961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 559480305449026243989125 104902557271692420747961)
                      ·
                        rfl

theorem cell23_204297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_204297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204297 prefixEnd_204297 := by exact prefixLift 204297
  have htrace : WordTrace (prefixWord ++ tailWord_204297) baseStart_204297 baseEnd_204297 := by
    simpa [prefixWord, tailWord_204297, baseEnd_204297] using wordTrace_append hprefix tailTrace_204297
  have hstable : (prefixWord ++ tailWord_204297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204297).length < 2 ^ (prefixWord ++ tailWord_204297).sum := by decide
  have hdescent : baseEnd_204297 < baseStart_204297 := by decide
  rcases family_descends (prefixWord ++ tailWord_204297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204307 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 1, 6]
def baseStart_204307 : Nat := 118140960795 + 204307 * 2 ^ 59
def prefixEnd_204307 : Nat := 4983230072969 + 3 ^ 40 * 204307 * 2
def baseEnd_204307 : Nat := 34969230692745793874305

theorem tailTrace_204307 : CollatzResearch.WordTrace tailWord_204307 prefixEnd_204307 34969230692745793874305 := by
  unfold tailWord_204307
  simp only [CollatzResearch.WordTrace]
  refine ⟨7451688470838106702747175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4967792313892071135164783 7451688470838106702747175)
  ·
    refine ⟨11177532706257160054120763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7451688470838106702747175 11177532706257160054120763)
    ·
      refine ⟨16766299059385740081181145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11177532706257160054120763 16766299059385740081181145)
      ·
        refine ⟨12574724294539305060885859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16766299059385740081181145 12574724294539305060885859)
        ·
          refine ⟨18862086441808957591328789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574724294539305060885859 18862086441808957591328789)
          ·
            refine ⟨884160301959794887093537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18862086441808957591328789 884160301959794887093537)
            ·
              refine ⟨663120226469846165320153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884160301959794887093537 663120226469846165320153)
              ·
                refine ⟨497340169852384623990115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663120226469846165320153 497340169852384623990115)
                ·
                  refine ⟨746010254778576935985173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497340169852384623990115 746010254778576935985173)
                  ·
                    refine ⟨34969230692745793874305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 746010254778576935985173 34969230692745793874305)
                    ·
                      rfl

theorem cell23_204307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 6].length) (baseStart_204307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204307 prefixEnd_204307 := by exact prefixLift 204307
  have htrace : WordTrace (prefixWord ++ tailWord_204307) baseStart_204307 baseEnd_204307 := by
    simpa [prefixWord, tailWord_204307, baseEnd_204307] using wordTrace_append hprefix tailTrace_204307
  have hstable : (prefixWord ++ tailWord_204307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204307).length < 2 ^ (prefixWord ++ tailWord_204307).sum := by decide
  have hdescent : baseEnd_204307 < baseStart_204307 := by decide
  rcases family_descends (prefixWord ++ tailWord_204307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204334 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_204334 : Nat := 118140960795 + 204334 * 2 ^ 59
def prefixEnd_204334 : Nat := 4983230072969 + 3 ^ 40 * 204334 * 2
def baseEnd_204334 : Nat := 104921556055908775985291

theorem tailTrace_204334 : CollatzResearch.WordTrace tailWord_204334 prefixEnd_204334 104921556055908775985291 := by
  unfold tailWord_204334
  simp only [CollatzResearch.WordTrace]
  refine ⟨931584155217536289247507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4968448827826860209320037 931584155217536289247507)
  ·
    refine ⟨1397376232826304433871261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 931584155217536289247507 1397376232826304433871261)
    ·
      refine ⟨524016087309864162701723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1397376232826304433871261 524016087309864162701723)
      ·
        refine ⟨786024130964796244052585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524016087309864162701723 786024130964796244052585)
        ·
          refine ⟨589518098223597183039439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786024130964796244052585 589518098223597183039439)
          ·
            refine ⟨884277147335395774559159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589518098223597183039439 884277147335395774559159)
            ·
              refine ⟨1326415721003093661838739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884277147335395774559159 1326415721003093661838739)
              ·
                refine ⟨1989623581504640492758109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326415721003093661838739 1989623581504640492758109)
                ·
                  refine ⟨746108843064240184784291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1989623581504640492758109 746108843064240184784291)
                  ·
                    refine ⟨1119163264596360277176437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 746108843064240184784291 1119163264596360277176437)
                    ·
                      refine ⟨104921556055908775985291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1119163264596360277176437 104921556055908775985291)
                      ·
                        rfl

theorem cell23_204334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_204334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204334 prefixEnd_204334 := by exact prefixLift 204334
  have htrace : WordTrace (prefixWord ++ tailWord_204334) baseStart_204334 baseEnd_204334 := by
    simpa [prefixWord, tailWord_204334, baseEnd_204334] using wordTrace_append hprefix tailTrace_204334
  have hstable : (prefixWord ++ tailWord_204334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204334).length < 2 ^ (prefixWord ++ tailWord_204334).sum := by decide
  have hdescent : baseEnd_204334 < baseStart_204334 := by decide
  rcases family_descends (prefixWord ++ tailWord_204334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204344 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_204344 : Nat := 118140960795 + 204344 * 2 ^ 59
def prefixEnd_204344 : Nat := 4983230072969 + 3 ^ 40 * 204344 * 2
def baseEnd_204344 : Nat := 104926690862453736860245

theorem tailTrace_204344 : CollatzResearch.WordTrace tailWord_204344 prefixEnd_204344 104926690862453736860245 := by
  unfold tailWord_204344
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726518985852031010922043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4968691981136041347896057 3726518985852031010922043)
  ·
    refine ⟨5589778478778046516383065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3726518985852031010922043 5589778478778046516383065)
    ·
      refine ⟨4192333859083534887287299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5589778478778046516383065 4192333859083534887287299)
      ·
        refine ⟨6288500788625302330930949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192333859083534887287299 6288500788625302330930949)
        ·
          refine ⟨1179093897867244187049553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6288500788625302330930949 1179093897867244187049553)
          ·
            refine ⟨884320423400433140287165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179093897867244187049553 884320423400433140287165)
            ·
              refine ⟨331620158775162427607687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884320423400433140287165 331620158775162427607687)
              ·
                refine ⟨497430238162743641411531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331620158775162427607687 497430238162743641411531)
                ·
                  refine ⟨746145357244115462117297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497430238162743641411531 746145357244115462117297)
                  ·
                    refine ⟨559609017933086596587973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 746145357244115462117297 559609017933086596587973)
                    ·
                      refine ⟨104926690862453736860245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 559609017933086596587973 104926690862453736860245)
                      ·
                        rfl

theorem cell23_204344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_204344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204344 prefixEnd_204344 := by exact prefixLift 204344
  have htrace : WordTrace (prefixWord ++ tailWord_204344) baseStart_204344 baseEnd_204344 := by
    simpa [prefixWord, tailWord_204344, baseEnd_204344] using wordTrace_append hprefix tailTrace_204344
  have hstable : (prefixWord ++ tailWord_204344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204344).length < 2 ^ (prefixWord ++ tailWord_204344).sum := by decide
  have hdescent : baseEnd_204344 < baseStart_204344 := by decide
  rcases family_descends (prefixWord ++ tailWord_204344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204351 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 3]
def baseStart_204351 : Nat := 118140960795 + 204351 * 2 ^ 59
def prefixEnd_204351 : Nat := 4983230072969 + 3 ^ 40 * 204351 * 2
def baseEnd_204351 : Nat := 104930285227035209472713

theorem tailTrace_204351 : CollatzResearch.WordTrace tailWord_204351 prefixEnd_204351 104930285227035209472713 := by
  unfold tailWord_204351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453293282678702217348907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4968862188452468144899271 7453293282678702217348907)
  ·
    refine ⟨11179939924018053326023361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7453293282678702217348907 11179939924018053326023361)
    ·
      refine ⟨8384954943013539994517521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11179939924018053326023361 8384954943013539994517521)
      ·
        refine ⟨6288716207260154995888141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8384954943013539994517521 6288716207260154995888141)
        ·
          refine ⟨2358268577722558123458053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6288716207260154995888141 2358268577722558123458053)
          ·
            refine ⟨442175358322979648148385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2358268577722558123458053 442175358322979648148385)
            ·
              refine ⟨331631518742234736111289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442175358322979648148385 331631518742234736111289)
              ·
                refine ⟨248723639056676052083467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331631518742234736111289 248723639056676052083467)
                ·
                  refine ⟨373085458585014078125201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248723639056676052083467 373085458585014078125201)
                  ·
                    refine ⟨279814093938760558593901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 373085458585014078125201 279814093938760558593901)
                    ·
                      refine ⟨104930285227035209472713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 279814093938760558593901 104930285227035209472713)
                      ·
                        rfl

theorem cell23_204351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_204351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204351 prefixEnd_204351 := by exact prefixLift 204351
  have htrace : WordTrace (prefixWord ++ tailWord_204351) baseStart_204351 baseEnd_204351 := by
    simpa [prefixWord, tailWord_204351, baseEnd_204351] using wordTrace_append hprefix tailTrace_204351
  have hstable : (prefixWord ++ tailWord_204351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204351).length < 2 ^ (prefixWord ++ tailWord_204351).sum := by decide
  have hdescent : baseEnd_204351 < baseStart_204351 := by decide
  rcases family_descends (prefixWord ++ tailWord_204351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204421 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 1, 4, 2]
def baseStart_204421 : Nat := 118140960795 + 204421 * 2 ^ 59
def prefixEnd_204421 : Nat := 4983230072969 + 3 ^ 40 * 204421 * 2
def baseEnd_204421 : Nat := 104966228872849935597391

theorem tailTrace_204421 : CollatzResearch.WordTrace tailWord_204421 prefixEnd_204421 104966228872849935597391 := by
  unfold tailWord_204421
  simp only [CollatzResearch.WordTrace]
  refine ⟨7455846392425104172397117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4970564261616736114931411 7455846392425104172397117)
  ·
    refine ⟨2795942397159414064648919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7455846392425104172397117 2795942397159414064648919)
    ·
      refine ⟨4193913595739121096973379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795942397159414064648919 4193913595739121096973379)
      ·
        refine ⟨6290870393608681645460069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193913595739121096973379 6290870393608681645460069)
        ·
          refine ⟨1179538198801627808523763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6290870393608681645460069 1179538198801627808523763)
          ·
            refine ⟨1769307298202441712785645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179538198801627808523763 1769307298202441712785645)
            ·
              refine ⟨663490236825915642294617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1769307298202441712785645 663490236825915642294617)
              ·
                refine ⟨497617677619436731720963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663490236825915642294617 497617677619436731720963)
                ·
                  refine ⟨746426516429155097581445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497617677619436731720963 746426516429155097581445)
                  ·
                    refine ⟨139954971830466580796521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 746426516429155097581445 139954971830466580796521)
                    ·
                      refine ⟨104966228872849935597391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 139954971830466580796521 104966228872849935597391)
                      ·
                        rfl

theorem cell23_204421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_204421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204421 prefixEnd_204421 := by exact prefixLift 204421
  have htrace : WordTrace (prefixWord ++ tailWord_204421) baseStart_204421 baseEnd_204421 := by
    simpa [prefixWord, tailWord_204421, baseEnd_204421] using wordTrace_append hprefix tailTrace_204421
  have hstable : (prefixWord ++ tailWord_204421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204421).length < 2 ^ (prefixWord ++ tailWord_204421).sum := by decide
  have hdescent : baseEnd_204421 < baseStart_204421 := by decide
  rcases family_descends (prefixWord ++ tailWord_204421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204437 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_204437 : Nat := 118140960795 + 204437 * 2 ^ 59
def prefixEnd_204437 : Nat := 4983230072969 + 3 ^ 40 * 204437 * 2
def baseEnd_204437 : Nat := 104974444563321872997317

theorem tailTrace_204437 : CollatzResearch.WordTrace tailWord_204437 prefixEnd_204437 104974444563321872997317 := by
  unfold tailWord_204437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456429960367138904979565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4970953306911425936653043 7456429960367138904979565)
  ·
    refine ⟨2796161235137677089367337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7456429960367138904979565 2796161235137677089367337)
    ·
      refine ⟨2097120926353257817025503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2796161235137677089367337 2097120926353257817025503)
      ·
        refine ⟨3145681389529886725538255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097120926353257817025503 3145681389529886725538255)
        ·
          refine ⟨4718522084294830088307383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145681389529886725538255 4718522084294830088307383)
          ·
            refine ⟨7077783126442245132461075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718522084294830088307383 7077783126442245132461075)
            ·
              refine ⟨10616674689663367698691613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077783126442245132461075 10616674689663367698691613)
              ·
                refine ⟨3981253008623762887009355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10616674689663367698691613 3981253008623762887009355)
                ·
                  refine ⟨5971879512935644330514033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981253008623762887009355 5971879512935644330514033)
                  ·
                    refine ⟨4478909634701733247885525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5971879512935644330514033 4478909634701733247885525)
                    ·
                      refine ⟨104974444563321872997317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4478909634701733247885525 104974444563321872997317)
                      ·
                        rfl

theorem cell23_204437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_204437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204437 prefixEnd_204437 := by exact prefixLift 204437
  have htrace : WordTrace (prefixWord ++ tailWord_204437) baseStart_204437 baseEnd_204437 := by
    simpa [prefixWord, tailWord_204437, baseEnd_204437] using wordTrace_append hprefix tailTrace_204437
  have hstable : (prefixWord ++ tailWord_204437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204437).length < 2 ^ (prefixWord ++ tailWord_204437).sum := by decide
  have hdescent : baseEnd_204437 < baseStart_204437 := by decide
  rcases family_descends (prefixWord ++ tailWord_204437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204474 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_204474 : Nat := 118140960795 + 204474 * 2 ^ 59
def prefixEnd_204474 : Nat := 4983230072969 + 3 ^ 40 * 204474 * 2
def baseEnd_204474 : Nat := 34997814449179409411549

theorem tailTrace_204474 : CollatzResearch.WordTrace tailWord_204474 prefixEnd_204474 34997814449179409411549 := by
  unfold tailWord_204474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864444865308273556019119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4971852974155396149384317 1864444865308273556019119)
  ·
    refine ⟨2796667297962410334028679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1864444865308273556019119 2796667297962410334028679)
    ·
      refine ⟨4195000946943615501043019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796667297962410334028679 4195000946943615501043019)
      ·
        refine ⟨6292501420415423251564529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4195000946943615501043019 6292501420415423251564529)
        ·
          refine ⟨4719376065311567438673397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6292501420415423251564529 4719376065311567438673397)
          ·
            refine ⟨442441506122959447375631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4719376065311567438673397 442441506122959447375631)
            ·
              refine ⟨663662259184439171063447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442441506122959447375631 663662259184439171063447)
              ·
                refine ⟨995493388776658756595171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663662259184439171063447 995493388776658756595171)
                ·
                  refine ⟨1493240083164988134892757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995493388776658756595171 1493240083164988134892757)
                  ·
                    refine ⟨34997814449179409411549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1493240083164988134892757 34997814449179409411549)
                    ·
                      rfl

theorem cell23_204474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_204474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204474 prefixEnd_204474 := by exact prefixLift 204474
  have htrace : WordTrace (prefixWord ++ tailWord_204474) baseStart_204474 baseEnd_204474 := by
    simpa [prefixWord, tailWord_204474, baseEnd_204474] using wordTrace_append hprefix tailTrace_204474
  have hstable : (prefixWord ++ tailWord_204474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204474).length < 2 ^ (prefixWord ++ tailWord_204474).sum := by decide
  have hdescent : baseEnd_204474 < baseStart_204474 := by decide
  rcases family_descends (prefixWord ++ tailWord_204474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204478 : List Nat := [4, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_204478 : Nat := 118140960795 + 204478 * 2 ^ 59
def prefixEnd_204478 : Nat := 4983230072969 + 3 ^ 40 * 204478 * 2
def baseEnd_204478 : Nat := 11666166363350690287181

theorem tailTrace_204478 : CollatzResearch.WordTrace tailWord_204478 prefixEnd_204478 11666166363350690287181 := by
  unfold tailWord_204478
  simp only [CollatzResearch.WordTrace]
  refine ⟨932240669152325363402761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4971950235479068604814725 932240669152325363402761)
  ·
    refine ⟨699180501864244022552071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 932240669152325363402761 699180501864244022552071)
    ·
      refine ⟨1048770752796366033828107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699180501864244022552071 1048770752796366033828107)
      ·
        refine ⟨1573156129194549050742161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048770752796366033828107 1573156129194549050742161)
        ·
          refine ⟨1179867096895911788056621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573156129194549050742161 1179867096895911788056621)
          ·
            refine ⟨442450161335966920521233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1179867096895911788056621 442450161335966920521233)
            ·
              refine ⟨331837621001975190390925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442450161335966920521233 331837621001975190390925)
              ·
                refine ⟨124439107875740696396597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331837621001975190390925 124439107875740696396597)
                ·
                  refine ⟨11666166363350690287181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124439107875740696396597 11666166363350690287181)
                  ·
                    rfl

theorem cell23_204478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_204478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204478 prefixEnd_204478 := by exact prefixLift 204478
  have htrace : WordTrace (prefixWord ++ tailWord_204478) baseStart_204478 baseEnd_204478 := by
    simpa [prefixWord, tailWord_204478, baseEnd_204478] using wordTrace_append hprefix tailTrace_204478
  have hstable : (prefixWord ++ tailWord_204478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204478).length < 2 ^ (prefixWord ++ tailWord_204478).sum := by decide
  have hdescent : baseEnd_204478 < baseStart_204478 := by decide
  rcases family_descends (prefixWord ++ tailWord_204478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204511 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 2, 4, 2]
def baseStart_204511 : Nat := 118140960795 + 204511 * 2 ^ 59
def prefixEnd_204511 : Nat := 4983230072969 + 3 ^ 40 * 204511 * 2
def baseEnd_204511 : Nat := 105012442131754583471977

theorem tailTrace_204511 : CollatzResearch.WordTrace tailWord_204511 prefixEnd_204511 105012442131754583471977 := by
  unfold tailWord_204511
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459128962099049543173387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4972752641399366362115591 7459128962099049543173387)
  ·
    refine ⟨11188693443148574314760081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7459128962099049543173387 11188693443148574314760081)
    ·
      refine ⟨8391520082361430736070061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11188693443148574314760081 8391520082361430736070061)
      ·
        refine ⟨3146820030885536526026273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8391520082361430736070061 3146820030885536526026273)
        ·
          refine ⟨2360115023164152394519705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3146820030885536526026273 2360115023164152394519705)
          ·
            refine ⟨1770086267373114295889779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2360115023164152394519705 1770086267373114295889779)
            ·
              refine ⟨2655129401059671443834669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770086267373114295889779 2655129401059671443834669)
              ·
                refine ⟨995673525397376791438001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2655129401059671443834669 995673525397376791438001)
                ·
                  refine ⟨746755144048032593578501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 995673525397376791438001 746755144048032593578501)
                  ·
                    refine ⟨140016589509006111295969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 746755144048032593578501 140016589509006111295969)
                    ·
                      refine ⟨105012442131754583471977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140016589509006111295969 105012442131754583471977)
                      ·
                        rfl

theorem cell23_204511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_204511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204511 prefixEnd_204511 := by exact prefixLift 204511
  have htrace : WordTrace (prefixWord ++ tailWord_204511) baseStart_204511 baseEnd_204511 := by
    simpa [prefixWord, tailWord_204511, baseEnd_204511] using wordTrace_append hprefix tailTrace_204511
  have hstable : (prefixWord ++ tailWord_204511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204511).length < 2 ^ (prefixWord ++ tailWord_204511).sum := by decide
  have hdescent : baseEnd_204511 < baseStart_204511 := by decide
  rcases family_descends (prefixWord ++ tailWord_204511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204544 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3]
def baseStart_204544 : Nat := 118140960795 + 204544 * 2 ^ 59
def prefixEnd_204544 : Nat := 4983230072969 + 3 ^ 40 * 204544 * 2
def baseEnd_204544 : Nat := 105029386993352954359325

theorem tailTrace_204544 : CollatzResearch.WordTrace tailWord_204544 prefixEnd_204544 105029386993352954359325 := by
  unfold tailWord_204544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730166285489748089562343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4973555047319664119416457 3730166285489748089562343)
  ·
    refine ⟨5595249428234622134343515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3730166285489748089562343 5595249428234622134343515)
    ·
      refine ⟨8392874142351933201515273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5595249428234622134343515 8392874142351933201515273)
      ·
        refine ⟨6294655606763949901136455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8392874142351933201515273 6294655606763949901136455)
        ·
          refine ⟨9441983410145924851704683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294655606763949901136455 9441983410145924851704683)
          ·
            refine ⟨14162975115218887277557025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441983410145924851704683 14162975115218887277557025)
            ·
              refine ⟨10622231336414165458167769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14162975115218887277557025 10622231336414165458167769)
              ·
                refine ⟨7966673502310624093625827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10622231336414165458167769 7966673502310624093625827)
                ·
                  refine ⟨11950010253465936140438741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7966673502310624093625827 11950010253465936140438741)
                  ·
                    refine ⟨280078365315607878291533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11950010253465936140438741 280078365315607878291533)
                    ·
                      refine ⟨105029386993352954359325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 280078365315607878291533 105029386993352954359325)
                      ·
                        rfl

theorem cell23_204544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_204544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204544 prefixEnd_204544 := by exact prefixLift 204544
  have htrace : WordTrace (prefixWord ++ tailWord_204544) baseStart_204544 baseEnd_204544 := by
    simpa [prefixWord, tailWord_204544, baseEnd_204544] using wordTrace_append hprefix tailTrace_204544
  have hstable : (prefixWord ++ tailWord_204544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204544).length < 2 ^ (prefixWord ++ tailWord_204544).sum := by decide
  have hdescent : baseEnd_204544 < baseStart_204544 := by decide
  rcases family_descends (prefixWord ++ tailWord_204544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204548 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_204548 : Nat := 118140960795 + 204548 * 2 ^ 59
def prefixEnd_204548 : Nat := 4983230072969 + 3 ^ 40 * 204548 * 2
def baseEnd_204548 : Nat := 105031440915970938709307

theorem tailTrace_204548 : CollatzResearch.WordTrace tailWord_204548 prefixEnd_204548 105031440915970938709307 := by
  unfold tailWord_204548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730239231482502431135149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4973652308643336574846865 3730239231482502431135149)
  ·
    refine ⟨1398839711805938411675681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3730239231482502431135149 1398839711805938411675681)
    ·
      refine ⟨1049129783854453808756761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1398839711805938411675681 1049129783854453808756761)
      ·
        refine ⟨786847337890840356567571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1049129783854453808756761 786847337890840356567571)
        ·
          refine ⟨1180271006836260534851357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786847337890840356567571 1180271006836260534851357)
          ·
            refine ⟨442601627563597700569259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1180271006836260534851357 442601627563597700569259)
            ·
              refine ⟨663902441345396550853889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442601627563597700569259 663902441345396550853889)
              ·
                refine ⟨497926831009047413140417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663902441345396550853889 497926831009047413140417)
                ·
                  refine ⟨373445123256785559855313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497926831009047413140417 373445123256785559855313)
                  ·
                    refine ⟨280083842442589169891485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 373445123256785559855313 280083842442589169891485)
                    ·
                      refine ⟨105031440915970938709307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 280083842442589169891485 105031440915970938709307)
                      ·
                        rfl

theorem cell23_204548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_204548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204548 prefixEnd_204548 := by exact prefixLift 204548
  have htrace : WordTrace (prefixWord ++ tailWord_204548) baseStart_204548 baseEnd_204548 := by
    simpa [prefixWord, tailWord_204548, baseEnd_204548] using wordTrace_append hprefix tailTrace_204548
  have hstable : (prefixWord ++ tailWord_204548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204548).length < 2 ^ (prefixWord ++ tailWord_204548).sum := by decide
  have hdescent : baseEnd_204548 < baseStart_204548 := by decide
  rcases family_descends (prefixWord ++ tailWord_204548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204578 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_204578 : Nat := 118140960795 + 204578 * 2 ^ 59
def prefixEnd_204578 : Nat := 4983230072969 + 3 ^ 40 * 204578 * 2
def baseEnd_204578 : Nat := 105046845335605821334169

theorem tailTrace_204578 : CollatzResearch.WordTrace tailWord_204578 prefixEnd_204578 105046845335605821334169 := by
  unfold tailWord_204578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865393163214079996465597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4974381768570879990574925 1865393163214079996465597)
  ·
    refine ⟨699522436205279998674599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1865393163214079996465597 699522436205279998674599)
    ·
      refine ⟨1049283654307919998011899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699522436205279998674599 1049283654307919998011899)
      ·
        refine ⟨1573925481461879997017849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049283654307919998011899 1573925481461879997017849)
        ·
          refine ⟨1180444111096409997763387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573925481461879997017849 1180444111096409997763387)
          ·
            refine ⟨1770666166644614996645081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180444111096409997763387 1770666166644614996645081)
            ·
              refine ⟨1327999624983461247483811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770666166644614996645081 1327999624983461247483811)
              ·
                refine ⟨1991999437475191871225717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327999624983461247483811 1991999437475191871225717)
                ·
                  refine ⟨186749947263299237927411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991999437475191871225717 186749947263299237927411)
                  ·
                    refine ⟨280124920894948856891117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 186749947263299237927411 280124920894948856891117)
                    ·
                      refine ⟨105046845335605821334169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 280124920894948856891117 105046845335605821334169)
                      ·
                        rfl

theorem cell23_204578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_204578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204578 prefixEnd_204578 := by exact prefixLift 204578
  have htrace : WordTrace (prefixWord ++ tailWord_204578) baseStart_204578 baseEnd_204578 := by
    simpa [prefixWord, tailWord_204578, baseEnd_204578] using wordTrace_append hprefix tailTrace_204578
  have hstable : (prefixWord ++ tailWord_204578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204578).length < 2 ^ (prefixWord ++ tailWord_204578).sum := by decide
  have hdescent : baseEnd_204578 < baseStart_204578 := by decide
  rcases family_descends (prefixWord ++ tailWord_204578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204581 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_204581 : Nat := 118140960795 + 204581 * 2 ^ 59
def prefixEnd_204581 : Nat := 4983230072969 + 3 ^ 40 * 204581 * 2
def baseEnd_204581 : Nat := 35016128592523103198885

theorem tailTrace_204581 : CollatzResearch.WordTrace tailWord_204581 prefixEnd_204581 35016128592523103198885 := by
  unfold tailWord_204581
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461682071845451498221597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4974454714563634332147731 7461682071845451498221597)
  ·
    refine ⟨2798130776942044311833099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7461682071845451498221597 2798130776942044311833099)
    ·
      refine ⟨4197196165413066467749649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798130776942044311833099 4197196165413066467749649)
      ·
        refine ⟨3147897124059799850812237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4197196165413066467749649 3147897124059799850812237)
        ·
          refine ⟨1180461421522424944054589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3147897124059799850812237 1180461421522424944054589)
          ·
            refine ⟨442673033070909354020471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1180461421522424944054589 442673033070909354020471)
            ·
              refine ⟨664009549606364031030707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442673033070909354020471 664009549606364031030707)
              ·
                refine ⟨996014324409546046546061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664009549606364031030707 996014324409546046546061)
                ·
                  refine ⟨373505371653579767454773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996014324409546046546061 373505371653579767454773)
                  ·
                    refine ⟨35016128592523103198885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 373505371653579767454773 35016128592523103198885)
                    ·
                      rfl

theorem cell23_204581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_204581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204581 prefixEnd_204581 := by exact prefixLift 204581
  have htrace : WordTrace (prefixWord ++ tailWord_204581) baseStart_204581 baseEnd_204581 := by
    simpa [prefixWord, tailWord_204581, baseEnd_204581] using wordTrace_append hprefix tailTrace_204581
  have hstable : (prefixWord ++ tailWord_204581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204581).length < 2 ^ (prefixWord ++ tailWord_204581).sum := by decide
  have hdescent : baseEnd_204581 < baseStart_204581 := by decide
  rcases family_descends (prefixWord ++ tailWord_204581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204588 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 2, 3, 2]
def baseStart_204588 : Nat := 118140960795 + 204588 * 2 ^ 59
def prefixEnd_204588 : Nat := 4983230072969 + 3 ^ 40 * 204588 * 2
def baseEnd_204588 : Nat := 105051980142150782209123

theorem tailTrace_204588 : CollatzResearch.WordTrace tailWord_204588 prefixEnd_204588 105051980142150782209123 := by
  unfold tailWord_204588
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730968691410045846863209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4974624921880061129150945 3730968691410045846863209)
  ·
    refine ⟨2798226518557534385147407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3730968691410045846863209 2798226518557534385147407)
    ·
      refine ⟨4197339777836301577721111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798226518557534385147407 4197339777836301577721111)
      ·
        refine ⟨6296009666754452366581667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197339777836301577721111 6296009666754452366581667)
        ·
          refine ⟨9444014500131678549872501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296009666754452366581667 9444014500131678549872501)
          ·
            refine ⟨885376359387344864050547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9444014500131678549872501 885376359387344864050547)
            ·
              refine ⟨1328064539081017296075821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885376359387344864050547 1328064539081017296075821)
              ·
                refine ⟨498024202155381486028433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328064539081017296075821 498024202155381486028433)
                ·
                  refine ⟨373518151616536114521325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498024202155381486028433 373518151616536114521325)
                  ·
                    refine ⟨140069306856201042945497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373518151616536114521325 140069306856201042945497)
                    ·
                      refine ⟨105051980142150782209123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140069306856201042945497 105051980142150782209123)
                      ·
                        rfl

theorem cell23_204588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_204588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204588 prefixEnd_204588 := by exact prefixLift 204588
  have htrace : WordTrace (prefixWord ++ tailWord_204588) baseStart_204588 baseEnd_204588 := by
    simpa [prefixWord, tailWord_204588, baseEnd_204588] using wordTrace_append hprefix tailTrace_204588
  have hstable : (prefixWord ++ tailWord_204588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204588).length < 2 ^ (prefixWord ++ tailWord_204588).sum := by decide
  have hdescent : baseEnd_204588 < baseStart_204588 := by decide
  rcases family_descends (prefixWord ++ tailWord_204588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204605 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_204605 : Nat := 118140960795 + 204605 * 2 ^ 59
def prefixEnd_204605 : Nat := 4983230072969 + 3 ^ 40 * 204605 * 2
def baseEnd_204605 : Nat := 105060709313277215696545

theorem tailTrace_204605 : CollatzResearch.WordTrace tailWord_204605 prefixEnd_204605 105060709313277215696545 := by
  unfold tailWord_204605
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462557423758503597095269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4975038282505669064730179 7462557423758503597095269)
  ·
    refine ⟨1399229516954719424455363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7462557423758503597095269 1399229516954719424455363)
    ·
      refine ⟨2098844275432079136683045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399229516954719424455363 2098844275432079136683045)
      ·
        refine ⟨393533301643514838128071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2098844275432079136683045 393533301643514838128071)
        ·
          refine ⟨590299952465272257192107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393533301643514838128071 590299952465272257192107)
          ·
            refine ⟨885449928697908385788161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590299952465272257192107 885449928697908385788161)
            ·
              refine ⟨664087446523431289341121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885449928697908385788161 664087446523431289341121)
              ·
                refine ⟨498065584892573467005841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664087446523431289341121 498065584892573467005841)
                ·
                  refine ⟨373549188669430100254381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498065584892573467005841 373549188669430100254381)
                  ·
                    refine ⟨140080945751036287595393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373549188669430100254381 140080945751036287595393)
                    ·
                      refine ⟨105060709313277215696545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140080945751036287595393 105060709313277215696545)
                      ·
                        rfl

theorem cell23_204605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_204605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204605 prefixEnd_204605 := by exact prefixLift 204605
  have htrace : WordTrace (prefixWord ++ tailWord_204605) baseStart_204605 baseEnd_204605 := by
    simpa [prefixWord, tailWord_204605, baseEnd_204605] using wordTrace_append hprefix tailTrace_204605
  have hstable : (prefixWord ++ tailWord_204605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204605).length < 2 ^ (prefixWord ++ tailWord_204605).sum := by decide
  have hdescent : baseEnd_204605 < baseStart_204605 := by decide
  rcases family_descends (prefixWord ++ tailWord_204605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204628 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_204628 : Nat := 118140960795 + 204628 * 2 ^ 59
def prefixEnd_204628 : Nat := 4983230072969 + 3 ^ 40 * 204628 * 2
def baseEnd_204628 : Nat := 35024173122776875236313

theorem tailTrace_204628 : CollatzResearch.WordTrace tailWord_204628 prefixEnd_204628 35024173122776875236313 := by
  unfold tailWord_204628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731698151337589262591269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4975597535116785683455025 3731698151337589262591269)
  ·
    refine ⟨699693403375797986735863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3731698151337589262591269 699693403375797986735863)
    ·
      refine ⟨1049540105063696980103795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699693403375797986735863 1049540105063696980103795)
      ·
        refine ⟨1574310157595545470155693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049540105063696980103795 1574310157595545470155693)
        ·
          refine ⟨590366309098329551308385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1574310157595545470155693 590366309098329551308385)
          ·
            refine ⟨442774731823747163481289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590366309098329551308385 442774731823747163481289)
            ·
              refine ⟨332081048867810372610967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442774731823747163481289 332081048867810372610967)
              ·
                refine ⟨498121573301715558916451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332081048867810372610967 498121573301715558916451)
                ·
                  refine ⟨747182359952573338374677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498121573301715558916451 747182359952573338374677)
                  ·
                    refine ⟨35024173122776875236313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 747182359952573338374677 35024173122776875236313)
                    ·
                      rfl

theorem cell23_204628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_204628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204628 prefixEnd_204628 := by exact prefixLift 204628
  have htrace : WordTrace (prefixWord ++ tailWord_204628) baseStart_204628 baseEnd_204628 := by
    simpa [prefixWord, tailWord_204628, baseEnd_204628] using wordTrace_append hprefix tailTrace_204628
  have hstable : (prefixWord ++ tailWord_204628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204628).length < 2 ^ (prefixWord ++ tailWord_204628).sum := by decide
  have hdescent : baseEnd_204628 < baseStart_204628 := by decide
  rcases family_descends (prefixWord ++ tailWord_204628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204641 : List Nat := [1, 2, 3, 1, 1, 1, 7, 7]
def baseStart_204641 : Nat := 118140960795 + 204641 * 2 ^ 59
def prefixEnd_204641 : Nat := 4983230072969 + 3 ^ 40 * 204641 * 2
def baseEnd_204641 : Nat := 3891822022845891660977

theorem tailTrace_204641 : CollatzResearch.WordTrace tailWord_204641 prefixEnd_204641 3891822022845891660977 := by
  unfold tailWord_204641
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463870451628081745405777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4975913634418721163603851 7463870451628081745405777)
  ·
    refine ⟨5597902838721061309054333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7463870451628081745405777 5597902838721061309054333)
    ·
      refine ⟨2099213564520397990895375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5597902838721061309054333 2099213564520397990895375)
      ·
        refine ⟨3148820346780596986343063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099213564520397990895375 3148820346780596986343063)
        ·
          refine ⟨4723230520170895479514595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148820346780596986343063 4723230520170895479514595)
          ·
            refine ⟨7084845780256343219271893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4723230520170895479514595 7084845780256343219271893)
            ·
              refine ⟨166051072974758044201685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7084845780256343219271893 166051072974758044201685)
              ·
                refine ⟨3891822022845891660977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166051072974758044201685 3891822022845891660977)
                ·
                  rfl

theorem cell23_204641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 7].length) (baseStart_204641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204641 prefixEnd_204641 := by exact prefixLift 204641
  have htrace : WordTrace (prefixWord ++ tailWord_204641) baseStart_204641 baseEnd_204641 := by
    simpa [prefixWord, tailWord_204641, baseEnd_204641] using wordTrace_append hprefix tailTrace_204641
  have hstable : (prefixWord ++ tailWord_204641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204641).length < 2 ^ (prefixWord ++ tailWord_204641).sum := by decide
  have hdescent : baseEnd_204641 < baseStart_204641 := by decide
  rcases family_descends (prefixWord ++ tailWord_204641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204652 : List Nat := [2, 2, 1, 1, 4, 2, 1, 5, 1, 2, 2]
def baseStart_204652 : Nat := 118140960795 + 204652 * 2 ^ 59
def prefixEnd_204652 : Nat := 4983230072969 + 3 ^ 40 * 204652 * 2
def baseEnd_204652 : Nat := 105084842904038531808829

theorem tailTrace_204652 : CollatzResearch.WordTrace tailWord_204652 prefixEnd_204652 105084842904038531808829 := by
  unfold tailWord_204652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732135827294115312028105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4976181103058820416037473 3732135827294115312028105)
  ·
    refine ⟨2799101870470586484021079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3732135827294115312028105 2799101870470586484021079)
    ·
      refine ⟨4198652805705879726031619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799101870470586484021079 4198652805705879726031619)
      ·
        refine ⟨6297979208558819589047429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198652805705879726031619 6297979208558819589047429)
        ·
          refine ⟨1180871101604778672946393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6297979208558819589047429 1180871101604778672946393)
          ·
            refine ⟨885653326203584004709795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1180871101604778672946393 885653326203584004709795)
            ·
              refine ⟨1328479989305376007064693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885653326203584004709795 1328479989305376007064693)
              ·
                refine ⟨124544998997379000662315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1328479989305376007064693 124544998997379000662315)
                ·
                  refine ⟨186817498496068500993473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124544998997379000662315 186817498496068500993473)
                  ·
                    refine ⟨140113123872051375745105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186817498496068500993473 140113123872051375745105)
                    ·
                      refine ⟨105084842904038531808829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140113123872051375745105 105084842904038531808829)
                      ·
                        rfl

theorem cell23_204652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_204652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204652 prefixEnd_204652 := by exact prefixLift 204652
  have htrace : WordTrace (prefixWord ++ tailWord_204652) baseStart_204652 baseEnd_204652 := by
    simpa [prefixWord, tailWord_204652, baseEnd_204652] using wordTrace_append hprefix tailTrace_204652
  have hstable : (prefixWord ++ tailWord_204652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204652).length < 2 ^ (prefixWord ++ tailWord_204652).sum := by decide
  have hdescent : baseEnd_204652 < baseStart_204652 := by decide
  rcases family_descends (prefixWord ++ tailWord_204652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204682 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_204682 : Nat := 118140960795 + 204682 * 2 ^ 59
def prefixEnd_204682 : Nat := 4983230072969 + 3 ^ 40 * 204682 * 2
def baseEnd_204682 : Nat := 105100247323673414433691

theorem tailTrace_204682 : CollatzResearch.WordTrace tailWord_204682 prefixEnd_204682 105100247323673414433691 := by
  unfold tailWord_204682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866341461119886436912075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4976910562986363831765533 1866341461119886436912075)
  ·
    refine ⟨2799512191679829655368113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866341461119886436912075 2799512191679829655368113)
    ·
      refine ⟨2099634143759872241526085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2799512191679829655368113 2099634143759872241526085)
      ·
        refine ⟨393681401954976045286141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2099634143759872241526085 393681401954976045286141)
        ·
          refine ⟨147630525733116016982303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393681401954976045286141 147630525733116016982303)
          ·
            refine ⟨221445788599674025473455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147630525733116016982303 221445788599674025473455)
            ·
              refine ⟨332168682899511038210183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221445788599674025473455 332168682899511038210183)
              ·
                refine ⟨498253024349266557315275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332168682899511038210183 498253024349266557315275)
                ·
                  refine ⟨747379536523899835972913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498253024349266557315275 747379536523899835972913)
                  ·
                    refine ⟨560534652392924876979685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 747379536523899835972913 560534652392924876979685)
                    ·
                      refine ⟨105100247323673414433691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 560534652392924876979685 105100247323673414433691)
                      ·
                        rfl

theorem cell23_204682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_204682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204682 prefixEnd_204682 := by exact prefixLift 204682
  have htrace : WordTrace (prefixWord ++ tailWord_204682) baseStart_204682 baseEnd_204682 := by
    simpa [prefixWord, tailWord_204682, baseEnd_204682] using wordTrace_append hprefix tailTrace_204682
  have hstable : (prefixWord ++ tailWord_204682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204682).length < 2 ^ (prefixWord ++ tailWord_204682).sum := by decide
  have hdescent : baseEnd_204682 < baseStart_204682 := by decide
  rcases family_descends (prefixWord ++ tailWord_204682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204695 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 1, 3, 2]
def baseStart_204695 : Nat := 118140960795 + 204695 * 2 ^ 59
def prefixEnd_204695 : Nat := 4983230072969 + 3 ^ 40 * 204695 * 2
def baseEnd_204695 : Nat := 105106922572181863571131

theorem tailTrace_204695 : CollatzResearch.WordTrace tailWord_204695 prefixEnd_204695 105106922572181863571131 := by
  unfold tailWord_204695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465839993432448967871539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4977226662288299311914359 7465839993432448967871539)
  ·
    refine ⟨11198759990148673451807309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7465839993432448967871539 11198759990148673451807309)
    ·
      refine ⟨4199534996305752544427741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11198759990148673451807309 4199534996305752544427741)
      ·
        refine ⟨1574825623614657204160403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4199534996305752544427741 1574825623614657204160403)
        ·
          refine ⟨2362238435421985806240605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574825623614657204160403 2362238435421985806240605)
          ·
            refine ⟨885839413283244677340227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2362238435421985806240605 885839413283244677340227)
            ·
              refine ⟨1328759119924867016010341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885839413283244677340227 1328759119924867016010341)
              ·
                refine ⟨249142334985912565501939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1328759119924867016010341 249142334985912565501939)
                ·
                  refine ⟨373713502478868848252909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249142334985912565501939 373713502478868848252909)
                  ·
                    refine ⟨140142563429575818094841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373713502478868848252909 140142563429575818094841)
                    ·
                      refine ⟨105106922572181863571131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140142563429575818094841 105106922572181863571131)
                      ·
                        rfl

theorem cell23_204695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_204695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204695 prefixEnd_204695 := by exact prefixLift 204695
  have htrace : WordTrace (prefixWord ++ tailWord_204695) baseStart_204695 baseEnd_204695 := by
    simpa [prefixWord, tailWord_204695, baseEnd_204695] using wordTrace_append hprefix tailTrace_204695
  have hstable : (prefixWord ++ tailWord_204695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204695).length < 2 ^ (prefixWord ++ tailWord_204695).sum := by decide
  have hdescent : baseEnd_204695 < baseStart_204695 := by decide
  rcases family_descends (prefixWord ++ tailWord_204695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204768 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 4, 5, 2]
def baseStart_204768 : Nat := 118140960795 + 204768 * 2 ^ 59
def prefixEnd_204768 : Nat := 4983230072969 + 3 ^ 40 * 204768 * 2
def baseEnd_204768 : Nat := 105144406659960077958295

theorem tailTrace_204768 : CollatzResearch.WordTrace tailWord_204768 prefixEnd_204768 105144406659960077958295 := by
  unfold tailWord_204768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734251261083991217639479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4979001681445321623519305 3734251261083991217639479)
  ·
    refine ⟨5601376891625986826459219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3734251261083991217639479 5601376891625986826459219)
    ·
      refine ⟨8402065337438980239688829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5601376891625986826459219 8402065337438980239688829)
      ·
        refine ⟨3150774501539617589883311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8402065337438980239688829 3150774501539617589883311)
        ·
          refine ⟨4726161752309426384824967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150774501539617589883311 4726161752309426384824967)
          ·
            refine ⟨7089242628464139577237451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726161752309426384824967 7089242628464139577237451)
            ·
              refine ⟨10633863942696209365856177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7089242628464139577237451 10633863942696209365856177)
              ·
                refine ⟨7975397957022157024392133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10633863942696209365856177 7975397957022157024392133)
                ·
                  refine ⟨1495387116941654442073525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7975397957022157024392133 1495387116941654442073525)
                  ·
                    refine ⟨140192542213280103944393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1495387116941654442073525 140192542213280103944393)
                    ·
                      refine ⟨105144406659960077958295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140192542213280103944393 105144406659960077958295)
                      ·
                        rfl

theorem cell23_204768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_204768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204768 prefixEnd_204768 := by exact prefixLift 204768
  have htrace : WordTrace (prefixWord ++ tailWord_204768) baseStart_204768 baseEnd_204768 := by
    simpa [prefixWord, tailWord_204768, baseEnd_204768] using wordTrace_append hprefix tailTrace_204768
  have hstable : (prefixWord ++ tailWord_204768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204768).length < 2 ^ (prefixWord ++ tailWord_204768).sum := by decide
  have hdescent : baseEnd_204768 < baseStart_204768 := by decide
  rcases family_descends (prefixWord ++ tailWord_204768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204778 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_204778 : Nat := 118140960795 + 204778 * 2 ^ 59
def prefixEnd_204778 : Nat := 4983230072969 + 3 ^ 40 * 204778 * 2
def baseEnd_204778 : Nat := 35049847155501679611083

theorem tailTrace_204778 : CollatzResearch.WordTrace tailWord_204778 prefixEnd_204778 35049847155501679611083 := by
  unfold tailWord_204778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867216813032938535785747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4979244834754502762095325 1867216813032938535785747)
  ·
    refine ⟨2800825219549407803678621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1867216813032938535785747 2800825219549407803678621)
    ·
      refine ⟨1050309457331027926379483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2800825219549407803678621 1050309457331027926379483)
      ·
        refine ⟨1575464185996541889569225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050309457331027926379483 1575464185996541889569225)
        ·
          refine ⟨1181598139497406417176919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1575464185996541889569225 1181598139497406417176919)
          ·
            refine ⟨1772397209246109625765379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181598139497406417176919 1772397209246109625765379)
            ·
              refine ⟨2658595813869164438648069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772397209246109625765379 2658595813869164438648069)
              ·
                refine ⟨498486715100468332246513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2658595813869164438648069 498486715100468332246513)
                ·
                  refine ⟨373865036325351249184885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498486715100468332246513 373865036325351249184885)
                  ·
                    refine ⟨35049847155501679611083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 373865036325351249184885 35049847155501679611083)
                    ·
                      rfl

theorem cell23_204778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_204778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204778 prefixEnd_204778 := by exact prefixLift 204778
  have htrace : WordTrace (prefixWord ++ tailWord_204778) baseStart_204778 baseEnd_204778 := by
    simpa [prefixWord, tailWord_204778, baseEnd_204778] using wordTrace_append hprefix tailTrace_204778
  have hstable : (prefixWord ++ tailWord_204778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204778).length < 2 ^ (prefixWord ++ tailWord_204778).sum := by decide
  have hdescent : baseEnd_204778 < baseStart_204778 := by decide
  rcases family_descends (prefixWord ++ tailWord_204778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204782 : List Nat := [4, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_204782 : Nat := 118140960795 + 204782 * 2 ^ 59
def prefixEnd_204782 : Nat := 4983230072969 + 3 ^ 40 * 204782 * 2
def baseEnd_204782 : Nat := 11683510598791447020359

theorem tailTrace_204782 : CollatzResearch.WordTrace tailWord_204782 prefixEnd_204782 11683510598791447020359 := by
  unfold tailWord_204782
  simp only [CollatzResearch.WordTrace]
  refine ⟨933626643014657853286075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4979342096078175217525733 933626643014657853286075)
  ·
    refine ⟨1400439964521986779929113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 933626643014657853286075 1400439964521986779929113)
    ·
      refine ⟨1050329973391490084946835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1400439964521986779929113 1050329973391490084946835)
      ·
        refine ⟨1575494960087235127420253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050329973391490084946835 1575494960087235127420253)
        ·
          refine ⟨590810610032713172782595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1575494960087235127420253 590810610032713172782595)
          ·
            refine ⟨886215915049069759173893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590810610032713172782595 886215915049069759173893)
            ·
              refine ⟨166165484071700579845105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 886215915049069759173893 166165484071700579845105)
              ·
                refine ⟨124624113053775434883829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166165484071700579845105 124624113053775434883829)
                ·
                  refine ⟨11683510598791447020359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124624113053775434883829 11683510598791447020359)
                  ·
                    rfl

theorem cell23_204782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_204782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204782 prefixEnd_204782 := by exact prefixLift 204782
  have htrace : WordTrace (prefixWord ++ tailWord_204782) baseStart_204782 baseEnd_204782 := by
    simpa [prefixWord, tailWord_204782, baseEnd_204782] using wordTrace_append hprefix tailTrace_204782
  have hstable : (prefixWord ++ tailWord_204782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204782).length < 2 ^ (prefixWord ++ tailWord_204782).sum := by decide
  have hdescent : baseEnd_204782 < baseStart_204782 := by decide
  rcases family_descends (prefixWord ++ tailWord_204782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204828 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_204828 : Nat := 118140960795 + 204828 * 2 ^ 59
def prefixEnd_204828 : Nat := 4983230072969 + 3 ^ 40 * 204828 * 2
def baseEnd_204828 : Nat := 105175215499229843208019

theorem tailTrace_204828 : CollatzResearch.WordTrace tailWord_204828 prefixEnd_204828 105175215499229843208019 := by
  unfold tailWord_204828
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735345450975306341231569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4980460601300408454975425 3735345450975306341231569)
  ·
    refine ⟨2801509088231479755923677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3735345450975306341231569 2801509088231479755923677)
    ·
      refine ⟨1050565908086804908471379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2801509088231479755923677 1050565908086804908471379)
      ·
        refine ⟨1575848862130207362707069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050565908086804908471379 1575848862130207362707069)
        ·
          refine ⟨590943323298827761015151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1575848862130207362707069 590943323298827761015151)
          ·
            refine ⟨886414984948241641522727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590943323298827761015151 886414984948241641522727)
            ·
              refine ⟨1329622477422362462284091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886414984948241641522727 1329622477422362462284091)
              ·
                refine ⟨1994433716133543693426137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329622477422362462284091 1994433716133543693426137)
                ·
                  refine ⟨1495825287100157770069603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994433716133543693426137 1495825287100157770069603)
                  ·
                    refine ⟨2243737930650236655104405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1495825287100157770069603 2243737930650236655104405)
                    ·
                      refine ⟨105175215499229843208019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2243737930650236655104405 105175215499229843208019)
                      ·
                        rfl

theorem cell23_204828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_204828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204828 prefixEnd_204828 := by exact prefixLift 204828
  have htrace : WordTrace (prefixWord ++ tailWord_204828) baseStart_204828 baseEnd_204828 := by
    simpa [prefixWord, tailWord_204828, baseEnd_204828] using wordTrace_append hprefix tailTrace_204828
  have hstable : (prefixWord ++ tailWord_204828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204828).length < 2 ^ (prefixWord ++ tailWord_204828).sum := by decide
  have hdescent : baseEnd_204828 < baseStart_204828 := by decide
  rcases family_descends (prefixWord ++ tailWord_204828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204842 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_204842 : Nat := 118140960795 + 204842 * 2 ^ 59
def prefixEnd_204842 : Nat := 4983230072969 + 3 ^ 40 * 204842 * 2
def baseEnd_204842 : Nat := 35060801409464262810985

theorem tailTrace_204842 : CollatzResearch.WordTrace tailWord_204842 prefixEnd_204842 35060801409464262810985 := by
  unfold tailWord_204842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867800380974973268368195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4980801015933262048981853 1867800380974973268368195)
  ·
    refine ⟨2801700571462459902552293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1867800380974973268368195 2801700571462459902552293)
    ·
      refine ⟨525318857149211231728555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2801700571462459902552293 525318857149211231728555)
      ·
        refine ⟨787978285723816847592833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525318857149211231728555 787978285723816847592833)
        ·
          refine ⟨590983714292862635694625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787978285723816847592833 590983714292862635694625)
          ·
            refine ⟨443237785719646976770969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590983714292862635694625 443237785719646976770969)
            ·
              refine ⟨332428339289735232578227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443237785719646976770969 332428339289735232578227)
              ·
                refine ⟨498642508934602848867341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332428339289735232578227 498642508934602848867341)
                ·
                  refine ⟨186990940850476068325253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498642508934602848867341 186990940850476068325253)
                  ·
                    refine ⟨35060801409464262810985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186990940850476068325253 35060801409464262810985)
                    ·
                      rfl

theorem cell23_204842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_204842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204842 prefixEnd_204842 := by exact prefixLift 204842
  have htrace : WordTrace (prefixWord ++ tailWord_204842) baseStart_204842 baseEnd_204842 := by
    simpa [prefixWord, tailWord_204842, baseEnd_204842] using wordTrace_append hprefix tailTrace_204842
  have hstable : (prefixWord ++ tailWord_204842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204842).length < 2 ^ (prefixWord ++ tailWord_204842).sum := by decide
  have hdescent : baseEnd_204842 < baseStart_204842 := by decide
  rcases family_descends (prefixWord ++ tailWord_204842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204885 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_204885 : Nat := 118140960795 + 204885 * 2 ^ 59
def prefixEnd_204885 : Nat := 4983230072969 + 3 ^ 40 * 204885 * 2
def baseEnd_204885 : Nat := 35068161298845373398419

theorem tailTrace_204885 : CollatzResearch.WordTrace tailWord_204885 prefixEnd_204885 35068161298845373398419 := by
  unfold tailWord_204885
  simp only [CollatzResearch.WordTrace]
  refine ⟨7472769862744111417288109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4981846575162740944858739 7472769862744111417288109)
  ·
    refine ⟨2802288698529041781483041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7472769862744111417288109 2802288698529041781483041)
    ·
      refine ⟨2101716523896781336112281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2802288698529041781483041 2101716523896781336112281)
      ·
        refine ⟨1576287392922586002084211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2101716523896781336112281 1576287392922586002084211)
        ·
          refine ⟨2364431089383879003126317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576287392922586002084211 2364431089383879003126317)
          ·
            refine ⟨886661658518954626172369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2364431089383879003126317 886661658518954626172369)
            ·
              refine ⟨664996243889215969629277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886661658518954626172369 664996243889215969629277)
              ·
                refine ⟨249373591458455988610979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664996243889215969629277 249373591458455988610979)
                ·
                  refine ⟨374060387187683982916469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249373591458455988610979 374060387187683982916469)
                  ·
                    refine ⟨35068161298845373398419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 374060387187683982916469 35068161298845373398419)
                    ·
                      rfl

theorem cell23_204885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_204885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204885 prefixEnd_204885 := by exact prefixLift 204885
  have htrace : WordTrace (prefixWord ++ tailWord_204885) baseStart_204885 baseEnd_204885 := by
    simpa [prefixWord, tailWord_204885, baseEnd_204885] using wordTrace_append hprefix tailTrace_204885
  have hstable : (prefixWord ++ tailWord_204885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204885).length < 2 ^ (prefixWord ++ tailWord_204885).sum := by decide
  have hdescent : baseEnd_204885 < baseStart_204885 := by decide
  rcases family_descends (prefixWord ++ tailWord_204885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204892 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_204892 : Nat := 118140960795 + 204892 * 2 ^ 59
def prefixEnd_204892 : Nat := 4983230072969 + 3 ^ 40 * 204892 * 2
def baseEnd_204892 : Nat := 105208078261117592807725

theorem tailTrace_204892 : CollatzResearch.WordTrace tailWord_204892 prefixEnd_204892 105208078261117592807725 := by
  unfold tailWord_204892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736512586859375806396465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4982016782479167741861953 3736512586859375806396465)
  ·
    refine ⟨2802384440144531854797349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3736512586859375806396465 2802384440144531854797349)
    ·
      refine ⟨525447082527099722774503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2802384440144531854797349 525447082527099722774503)
      ·
        refine ⟨788170623790649584161755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525447082527099722774503 788170623790649584161755)
        ·
          refine ⟨1182255935685974376242633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788170623790649584161755 1182255935685974376242633)
          ·
            refine ⟨886691951764480782181975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182255935685974376242633 886691951764480782181975)
            ·
              refine ⟨1330037927646721173272963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886691951764480782181975 1330037927646721173272963)
              ·
                refine ⟨1995056891470081759909445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330037927646721173272963 1995056891470081759909445)
                ·
                  refine ⟨374073167150640329983021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1995056891470081759909445 374073167150640329983021)
                  ·
                    refine ⟨140277437681490123743633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374073167150640329983021 140277437681490123743633)
                    ·
                      refine ⟨105208078261117592807725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140277437681490123743633 105208078261117592807725)
                      ·
                        rfl

theorem cell23_204892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_204892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204892 prefixEnd_204892 := by exact prefixLift 204892
  have htrace : WordTrace (prefixWord ++ tailWord_204892) baseStart_204892 baseEnd_204892 := by
    simpa [prefixWord, tailWord_204892, baseEnd_204892] using wordTrace_append hprefix tailTrace_204892
  have hstable : (prefixWord ++ tailWord_204892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204892).length < 2 ^ (prefixWord ++ tailWord_204892).sum := by decide
  have hdescent : baseEnd_204892 < baseStart_204892 := by decide
  rcases family_descends (prefixWord ++ tailWord_204892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204956 : List Nat := [2, 2, 3, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_204956 : Nat := 118140960795 + 204956 * 2 ^ 59
def prefixEnd_204956 : Nat := 4983230072969 + 3 ^ 40 * 204956 * 2
def baseEnd_204956 : Nat := 105240941023005342407431

theorem tailTrace_204956 : CollatzResearch.WordTrace tailWord_204956 prefixEnd_204956 105240941023005342407431 := by
  unfold tailWord_204956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737679722743445271561361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4983572963657927028748481 3737679722743445271561361)
  ·
    refine ⟨2803259792057583953671021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3737679722743445271561361 2803259792057583953671021)
    ·
      refine ⟨1051222422021593982626633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2803259792057583953671021 1051222422021593982626633)
      ·
        refine ⟨788416816516195486969975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1051222422021593982626633 788416816516195486969975)
        ·
          refine ⟨1182625224774293230454963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788416816516195486969975 1182625224774293230454963)
          ·
            refine ⟨1773937837161439845682445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182625224774293230454963 1773937837161439845682445)
            ·
              refine ⟨665226688935539942130917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1773937837161439845682445 665226688935539942130917)
              ·
                refine ⟨124730004175413739149547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 665226688935539942130917 124730004175413739149547)
                ·
                  refine ⟨187095006263120608724321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124730004175413739149547 187095006263120608724321)
                  ·
                    refine ⟨140321254697340456543241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187095006263120608724321 140321254697340456543241)
                    ·
                      refine ⟨105240941023005342407431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140321254697340456543241 105240941023005342407431)
                      ·
                        rfl

theorem cell23_204956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_204956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204956 prefixEnd_204956 := by exact prefixLift 204956
  have htrace : WordTrace (prefixWord ++ tailWord_204956) baseStart_204956 baseEnd_204956 := by
    simpa [prefixWord, tailWord_204956, baseEnd_204956] using wordTrace_append hprefix tailTrace_204956
  have hstable : (prefixWord ++ tailWord_204956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204956).length < 2 ^ (prefixWord ++ tailWord_204956).sum := by decide
  have hdescent : baseEnd_204956 < baseStart_204956 := by decide
  rcases family_descends (prefixWord ++ tailWord_204956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204962 : List Nat := [3, 3, 1, 3, 1, 3, 1, 8]
def baseStart_204962 : Nat := 118140960795 + 204962 * 2 ^ 59
def prefixEnd_204962 : Nat := 4983230072969 + 3 ^ 40 * 204962 * 2
def baseEnd_204962 : Nat := 3897926737293789590089

theorem tailTrace_204962 : CollatzResearch.WordTrace tailWord_204962 prefixEnd_204962 3897926737293789590089 := by
  unfold tailWord_204962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868894570866288391960285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4983718855643435711894093 1868894570866288391960285)
  ·
    refine ⟨700835464074858146985107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1868894570866288391960285 700835464074858146985107)
    ·
      refine ⟨1051253196112287220477661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700835464074858146985107 1051253196112287220477661)
      ·
        refine ⟨394219948542107707679123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1051253196112287220477661 394219948542107707679123)
        ·
          refine ⟨591329922813161561518685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394219948542107707679123 591329922813161561518685)
          ·
            refine ⟨221748721054935585569507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591329922813161561518685 221748721054935585569507)
            ·
              refine ⟨332623081582403378354261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221748721054935585569507 332623081582403378354261)
              ·
                refine ⟨3897926737293789590089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 332623081582403378354261 3897926737293789590089)
                ·
                  rfl

theorem cell23_204962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 8].length) (baseStart_204962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204962 prefixEnd_204962 := by exact prefixLift 204962
  have htrace : WordTrace (prefixWord ++ tailWord_204962) baseStart_204962 baseEnd_204962 := by
    simpa [prefixWord, tailWord_204962, baseEnd_204962] using wordTrace_append hprefix tailTrace_204962
  have hstable : (prefixWord ++ tailWord_204962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204962).length < 2 ^ (prefixWord ++ tailWord_204962).sum := by decide
  have hdescent : baseEnd_204962 < baseStart_204962 := by decide
  rcases family_descends (prefixWord ++ tailWord_204962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204993 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_204993 : Nat := 118140960795 + 204993 * 2 ^ 59
def prefixEnd_204993 : Nat := 4983230072969 + 3 ^ 40 * 204993 * 2
def baseEnd_204993 : Nat := 105259939807221697644761

theorem tailTrace_204993 : CollatzResearch.WordTrace tailWord_204993 prefixEnd_204993 105259939807221697644761 := by
  unfold tailWord_204993
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476708946352845862219633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4984472630901897241479755 7476708946352845862219633)
  ·
    refine ⟨5607531709764634396664725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7476708946352845862219633 5607531709764634396664725)
    ·
      refine ⟨262853048895217237343659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5607531709764634396664725 262853048895217237343659)
      ·
        refine ⟨394279573342825856015489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262853048895217237343659 394279573342825856015489)
        ·
          refine ⟨295709680007119392011617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394279573342825856015489 295709680007119392011617)
          ·
            refine ⟨221782260005339544008713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295709680007119392011617 221782260005339544008713)
            ·
              refine ⟨166336695004004658006535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221782260005339544008713 166336695004004658006535)
              ·
                refine ⟨249505042506006987009803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166336695004004658006535 249505042506006987009803)
                ·
                  refine ⟨374257563759010480514705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249505042506006987009803 374257563759010480514705)
                  ·
                    refine ⟨280693172819257860386029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 374257563759010480514705 280693172819257860386029)
                    ·
                      refine ⟨105259939807221697644761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 280693172819257860386029 105259939807221697644761)
                      ·
                        rfl

theorem cell23_204993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_204993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204993 prefixEnd_204993 := by exact prefixLift 204993
  have htrace : WordTrace (prefixWord ++ tailWord_204993) baseStart_204993 baseEnd_204993 := by
    simpa [prefixWord, tailWord_204993, baseEnd_204993] using wordTrace_append hprefix tailTrace_204993
  have hstable : (prefixWord ++ tailWord_204993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204993).length < 2 ^ (prefixWord ++ tailWord_204993).sum := by decide
  have hdescent : baseEnd_204993 < baseStart_204993 := by decide
  rcases family_descends (prefixWord ++ tailWord_204993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204995 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 8, 2]
def baseStart_204995 : Nat := 118140960795 + 204995 * 2 ^ 59
def prefixEnd_204995 : Nat := 4983230072969 + 3 ^ 40 * 204995 * 2
def baseEnd_204995 : Nat := 105260966768530689819751

theorem tailTrace_204995 : CollatzResearch.WordTrace tailWord_204995 prefixEnd_204995 105260966768530689819751 := by
  unfold tailWord_204995
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476781892345600203792439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4984521261563733469194959 7476781892345600203792439)
  ·
    refine ⟨11215172838518400305688659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7476781892345600203792439 11215172838518400305688659)
    ·
      refine ⟨16822759257777600458532989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11215172838518400305688659 16822759257777600458532989)
      ·
        refine ⟨6308534721666600171949871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16822759257777600458532989 6308534721666600171949871)
        ·
          refine ⟨9462802082499900257924807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308534721666600171949871 9462802082499900257924807)
          ·
            refine ⟨14194203123749850386887211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9462802082499900257924807 14194203123749850386887211)
            ·
              refine ⟨21291304685624775580330817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14194203123749850386887211 21291304685624775580330817)
              ·
                refine ⟨15968478514218581685248113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21291304685624775580330817 15968478514218581685248113)
                ·
                  refine ⟨11976358885663936263936085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15968478514218581685248113 11976358885663936263936085)
                  ·
                    refine ⟨140347955691374253093001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11976358885663936263936085 140347955691374253093001)
                    ·
                      refine ⟨105260966768530689819751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140347955691374253093001 105260966768530689819751)
                      ·
                        rfl

theorem cell23_204995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_204995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_204995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_204995 prefixEnd_204995 := by exact prefixLift 204995
  have htrace : WordTrace (prefixWord ++ tailWord_204995) baseStart_204995 baseEnd_204995 := by
    simpa [prefixWord, tailWord_204995, baseEnd_204995] using wordTrace_append hprefix tailTrace_204995
  have hstable : (prefixWord ++ tailWord_204995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204995).length < 2 ^ (prefixWord ++ tailWord_204995).sum := by decide
  have hdescent : baseEnd_204995 < baseStart_204995 := by decide
  rcases family_descends (prefixWord ++ tailWord_204995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205006 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_205006 : Nat := 118140960795 + 205006 * 2 ^ 59
def prefixEnd_205006 : Nat := 4983230072969 + 3 ^ 40 * 205006 * 2
def baseEnd_205006 : Nat := 105266615055730146782201

theorem tailTrace_205006 : CollatzResearch.WordTrace tailWord_205006 prefixEnd_205006 105266615055730146782201 := by
  unfold tailWord_205006
  simp only [CollatzResearch.WordTrace]
  refine ⟨934647886913218635305359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4984788730203832721628581 934647886913218635305359)
  ·
    refine ⟨1401971830369827952958039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 934647886913218635305359 1401971830369827952958039)
    ·
      refine ⟨2102957745554741929437059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1401971830369827952958039 2102957745554741929437059)
      ·
        refine ⟨3154436618332112894155589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102957745554741929437059 3154436618332112894155589)
        ·
          refine ⟨591456865937271167654173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3154436618332112894155589 591456865937271167654173)
          ·
            refine ⟨221796324726476687870315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591456865937271167654173 221796324726476687870315)
            ·
              refine ⟨332694487089715031805473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221796324726476687870315 332694487089715031805473)
              ·
                refine ⟨249520865317286273854105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332694487089715031805473 249520865317286273854105)
                ·
                  refine ⟨187140648987964705390579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249520865317286273854105 187140648987964705390579)
                  ·
                    refine ⟨280710973481947058085869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187140648987964705390579 280710973481947058085869)
                    ·
                      refine ⟨105266615055730146782201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 280710973481947058085869 105266615055730146782201)
                      ·
                        rfl

theorem cell23_205006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_205006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205006 prefixEnd_205006 := by exact prefixLift 205006
  have htrace : WordTrace (prefixWord ++ tailWord_205006) baseStart_205006 baseEnd_205006 := by
    simpa [prefixWord, tailWord_205006, baseEnd_205006] using wordTrace_append hprefix tailTrace_205006
  have hstable : (prefixWord ++ tailWord_205006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205006).length < 2 ^ (prefixWord ++ tailWord_205006).sum := by decide
  have hdescent : baseEnd_205006 < baseStart_205006 := by decide
  rcases family_descends (prefixWord ++ tailWord_205006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205025 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_205025 : Nat := 118140960795 + 205025 * 2 ^ 59
def prefixEnd_205025 : Nat := 4983230072969 + 3 ^ 40 * 205025 * 2
def baseEnd_205025 : Nat := 105276371188165572444613

theorem tailTrace_205025 : CollatzResearch.WordTrace tailWord_205025 prefixEnd_205025 105276371188165572444613 := by
  unfold tailWord_205025
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477876082236915327384529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4985250721491276884923019 7477876082236915327384529)
  ·
    refine ⟨5608407061677686495538397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7477876082236915327384529 5608407061677686495538397)
    ·
      refine ⟨2103152648129132435826899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5608407061677686495538397 2103152648129132435826899)
      ·
        refine ⟨3154728972193698653740349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103152648129132435826899 3154728972193698653740349)
        ·
          refine ⟨1183023364572636995152631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3154728972193698653740349 1183023364572636995152631)
          ·
            refine ⟨1774535046858955492728947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183023364572636995152631 1774535046858955492728947)
            ·
              refine ⟨2661802570288433239093421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774535046858955492728947 2661802570288433239093421)
              ·
                refine ⟨998175963858162464660033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661802570288433239093421 998175963858162464660033)
                ·
                  refine ⟨748631972893621848495025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 998175963858162464660033 748631972893621848495025)
                  ·
                    refine ⟨561473979670216386371269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748631972893621848495025 561473979670216386371269)
                    ·
                      refine ⟨105276371188165572444613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 561473979670216386371269 105276371188165572444613)
                      ·
                        rfl

theorem cell23_205025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_205025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205025 prefixEnd_205025 := by exact prefixLift 205025
  have htrace : WordTrace (prefixWord ++ tailWord_205025) baseStart_205025 baseEnd_205025 := by
    simpa [prefixWord, tailWord_205025, baseEnd_205025] using wordTrace_append hprefix tailTrace_205025
  have hstable : (prefixWord ++ tailWord_205025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205025).length < 2 ^ (prefixWord ++ tailWord_205025).sum := by decide
  have hdescent : baseEnd_205025 < baseStart_205025 := by decide
  rcases family_descends (prefixWord ++ tailWord_205025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205029 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 1, 4, 2]
def baseStart_205029 : Nat := 118140960795 + 205029 * 2 ^ 59
def prefixEnd_205029 : Nat := 4983230072969 + 3 ^ 40 * 205029 * 2
def baseEnd_205029 : Nat := 105278425110783556794595

theorem tailTrace_205029 : CollatzResearch.WordTrace tailWord_205029 prefixEnd_205029 105278425110783556794595 := by
  unfold tailWord_205029
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478021974222424010530141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4985347982814949340353427 7478021974222424010530141)
  ·
    refine ⟨2804258240333409003948803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7478021974222424010530141 2804258240333409003948803)
    ·
      refine ⟨4206387360500113505923205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804258240333409003948803 4206387360500113505923205)
      ·
        refine ⟨788697630093771282360601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4206387360500113505923205 788697630093771282360601)
        ·
          refine ⟨591523222570328461770451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788697630093771282360601 591523222570328461770451)
          ·
            refine ⟨887284833855492692655677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591523222570328461770451 887284833855492692655677)
            ·
              refine ⟨332731812695809759745879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887284833855492692655677 332731812695809759745879)
              ·
                refine ⟨499097719043714639618819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332731812695809759745879 499097719043714639618819)
                ·
                  refine ⟨748646578565571959428229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499097719043714639618819 748646578565571959428229)
                  ·
                    refine ⟨140371233481044742392793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 748646578565571959428229 140371233481044742392793)
                    ·
                      refine ⟨105278425110783556794595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140371233481044742392793 105278425110783556794595)
                      ·
                        rfl

theorem cell23_205029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_205029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205029 prefixEnd_205029 := by exact prefixLift 205029
  have htrace : WordTrace (prefixWord ++ tailWord_205029) baseStart_205029 baseEnd_205029 := by
    simpa [prefixWord, tailWord_205029, baseEnd_205029] using wordTrace_append hprefix tailTrace_205029
  have hstable : (prefixWord ++ tailWord_205029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205029).length < 2 ^ (prefixWord ++ tailWord_205029).sum := by decide
  have hdescent : baseEnd_205029 < baseStart_205029 := by decide
  rcases family_descends (prefixWord ++ tailWord_205029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205065 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 4, 5]
def baseStart_205065 : Nat := 118140960795 + 205065 * 2 ^ 59
def prefixEnd_205065 : Nat := 4983230072969 + 3 ^ 40 * 205065 * 2
def baseEnd_205065 : Nat := 35098970138115138648143

theorem tailTrace_205065 : CollatzResearch.WordTrace tailWord_205065 prefixEnd_205065 35098970138115138648143 := by
  unfold tailWord_205065
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479335002092002158840649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4986223334728001439227099 7479335002092002158840649)
  ·
    refine ⟨5609501251569001619130487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7479335002092002158840649 5609501251569001619130487)
    ·
      refine ⟨8414251877353502428695731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5609501251569001619130487 8414251877353502428695731)
      ·
        refine ⟨12621377816030253643043597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8414251877353502428695731 12621377816030253643043597)
        ·
          refine ⟨4733016681011345116141349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12621377816030253643043597 4733016681011345116141349)
          ·
            refine ⟨887440627689627209276503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4733016681011345116141349 887440627689627209276503)
            ·
              refine ⟨1331160941534440813914755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887440627689627209276503 1331160941534440813914755)
              ·
                refine ⟨1996741412301661220872133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331160941534440813914755 1996741412301661220872133)
                ·
                  refine ⟨374389014806561478913525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996741412301661220872133 374389014806561478913525)
                  ·
                    refine ⟨35098970138115138648143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 374389014806561478913525 35098970138115138648143)
                    ·
                      rfl

theorem cell23_205065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_205065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205065 prefixEnd_205065 := by exact prefixLift 205065
  have htrace : WordTrace (prefixWord ++ tailWord_205065) baseStart_205065 baseEnd_205065 := by
    simpa [prefixWord, tailWord_205065, baseEnd_205065] using wordTrace_append hprefix tailTrace_205065
  have hstable : (prefixWord ++ tailWord_205065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205065).length < 2 ^ (prefixWord ++ tailWord_205065).sum := by decide
  have hdescent : baseEnd_205065 < baseStart_205065 := by decide
  rcases family_descends (prefixWord ++ tailWord_205065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205209 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 4]
def baseStart_205209 : Nat := 118140960795 + 205209 * 2 ^ 59
def prefixEnd_205209 : Nat := 4983230072969 + 3 ^ 40 * 205209 * 2
def baseEnd_205209 : Nat := 105370851628592852543767

theorem tailTrace_205209 : CollatzResearch.WordTrace tailWord_205209 prefixEnd_205209 105370851628592852543767 := by
  unfold tailWord_205209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7484587113570314752082681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4989724742380209834721787 7484587113570314752082681)
  ·
    refine ⟨5613440335177736064062011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7484587113570314752082681 5613440335177736064062011)
    ·
      refine ⟨8420160502766604096093017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5613440335177736064062011 8420160502766604096093017)
      ·
        refine ⟨6315120377074953072069763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8420160502766604096093017 6315120377074953072069763)
        ·
          refine ⟨9472680565612429608104645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315120377074953072069763 9472680565612429608104645)
          ·
            refine ⟨1776127606052330551519621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9472680565612429608104645 1776127606052330551519621)
            ·
              refine ⟨333023926134811978409929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1776127606052330551519621 333023926134811978409929)
              ·
                refine ⟨249767944601108983807447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333023926134811978409929 249767944601108983807447)
                ·
                  refine ⟨374651916901663475711171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249767944601108983807447 374651916901663475711171)
                  ·
                    refine ⟨561977875352495213566757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 374651916901663475711171 561977875352495213566757)
                    ·
                      refine ⟨105370851628592852543767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 561977875352495213566757 105370851628592852543767)
                      ·
                        rfl

theorem cell23_205209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_205209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205209 prefixEnd_205209 := by exact prefixLift 205209
  have htrace : WordTrace (prefixWord ++ tailWord_205209) baseStart_205209 baseEnd_205209 := by
    simpa [prefixWord, tailWord_205209, baseEnd_205209] using wordTrace_append hprefix tailTrace_205209
  have hstable : (prefixWord ++ tailWord_205209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205209).length < 2 ^ (prefixWord ++ tailWord_205209).sum := by decide
  have hdescent : baseEnd_205209 < baseStart_205209 := by decide
  rcases family_descends (prefixWord ++ tailWord_205209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205292 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_205292 : Nat := 118140960795 + 205292 * 2 ^ 59
def prefixEnd_205292 : Nat := 4983230072969 + 3 ^ 40 * 205292 * 2
def baseEnd_205292 : Nat := 35137823507638675935295

theorem tailTrace_205292 : CollatzResearch.WordTrace tailWord_205292 prefixEnd_205292 35137823507638675935295 := by
  unfold tailWord_205292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743807186134809963677065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4991742914846413284902753 3743807186134809963677065)
  ·
    refine ⟨2807855389601107472757799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3743807186134809963677065 2807855389601107472757799)
    ·
      refine ⟨4211783084401661209136699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2807855389601107472757799 4211783084401661209136699)
      ·
        refine ⟨6317674626602491813705049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4211783084401661209136699 6317674626602491813705049)
        ·
          refine ⟨4738255969951868860278787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6317674626602491813705049 4738255969951868860278787)
          ·
            refine ⟨7107383954927803290418181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4738255969951868860278787 7107383954927803290418181)
            ·
              refine ⟨1332634491548963116953409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7107383954927803290418181 1332634491548963116953409)
              ·
                refine ⟨999475868661722337715057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332634491548963116953409 999475868661722337715057)
                ·
                  refine ⟨749606901496291753286293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999475868661722337715057 749606901496291753286293)
                  ·
                    refine ⟨35137823507638675935295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 749606901496291753286293 35137823507638675935295)
                    ·
                      rfl

theorem cell23_205292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_205292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205292 prefixEnd_205292 := by exact prefixLift 205292
  have htrace : WordTrace (prefixWord ++ tailWord_205292) baseStart_205292 baseEnd_205292 := by
    simpa [prefixWord, tailWord_205292, baseEnd_205292] using wordTrace_append hprefix tailTrace_205292
  have hstable : (prefixWord ++ tailWord_205292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205292).length < 2 ^ (prefixWord ++ tailWord_205292).sum := by decide
  have hdescent : baseEnd_205292 < baseStart_205292 := by decide
  rcases family_descends (prefixWord ++ tailWord_205292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205293 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_205293 : Nat := 118140960795 + 205293 * 2 ^ 59
def prefixEnd_205293 : Nat := 4983230072969 + 3 ^ 40 * 205293 * 2
def baseEnd_205293 : Nat := 105413984003570523893381

theorem tailTrace_205293 : CollatzResearch.WordTrace tailWord_205293 prefixEnd_205293 105413984003570523893381 := by
  unfold tailWord_205293
  simp only [CollatzResearch.WordTrace]
  refine ⟨7487650845265997098140533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4991767230177331398760355 7487650845265997098140533)
  ·
    refine ⟨701967266743687227950675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7487650845265997098140533 701967266743687227950675)
    ·
      refine ⟨1052950900115530841926013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701967266743687227950675 1052950900115530841926013)
      ·
        refine ⟨394856587543324065722255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1052950900115530841926013 394856587543324065722255)
        ·
          refine ⟨592284881314986098583383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394856587543324065722255 592284881314986098583383)
          ·
            refine ⟨888427321972479147875075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592284881314986098583383 888427321972479147875075)
            ·
              refine ⟨1332640982958718721812613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888427321972479147875075 1332640982958718721812613)
              ·
                refine ⟨249870184304759760339865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1332640982958718721812613 249870184304759760339865)
                ·
                  refine ⟨187402638228569820254899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249870184304759760339865 187402638228569820254899)
                  ·
                    refine ⟨281103957342854730382349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187402638228569820254899 281103957342854730382349)
                    ·
                      refine ⟨105413984003570523893381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 281103957342854730382349 105413984003570523893381)
                      ·
                        rfl

theorem cell23_205293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_205293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205293 prefixEnd_205293 := by exact prefixLift 205293
  have htrace : WordTrace (prefixWord ++ tailWord_205293) baseStart_205293 baseEnd_205293 := by
    simpa [prefixWord, tailWord_205293, baseEnd_205293] using wordTrace_append hprefix tailTrace_205293
  have hstable : (prefixWord ++ tailWord_205293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205293).length < 2 ^ (prefixWord ++ tailWord_205293).sum := by decide
  have hdescent : baseEnd_205293 < baseStart_205293 := by decide
  rcases family_descends (prefixWord ++ tailWord_205293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205299 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 3, 4, 2]
def baseStart_205299 : Nat := 118140960795 + 205299 * 2 ^ 59
def prefixEnd_205299 : Nat := 4983230072969 + 3 ^ 40 * 205299 * 2
def baseEnd_205299 : Nat := 105417064887497500418353

theorem tailTrace_205299 : CollatzResearch.WordTrace tailWord_205299 prefixEnd_205299 105417064887497500418353 := by
  unfold tailWord_205299
  simp only [CollatzResearch.WordTrace]
  refine ⟨7487869683244260122858951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4991913122162840081905967 7487869683244260122858951)
  ·
    refine ⟨11231804524866390184288427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7487869683244260122858951 11231804524866390184288427)
    ·
      refine ⟨16847706787299585276432641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11231804524866390184288427 16847706787299585276432641)
      ·
        refine ⟨12635780090474688957324481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16847706787299585276432641 12635780090474688957324481)
        ·
          refine ⟨9476835067856016717993361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12635780090474688957324481 9476835067856016717993361)
          ·
            refine ⟨7107626300892012538495021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9476835067856016717993361 7107626300892012538495021)
            ·
              refine ⟨2665359862834504701935633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7107626300892012538495021 2665359862834504701935633)
              ·
                refine ⟨1999019897125878526451725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665359862834504701935633 1999019897125878526451725)
                ·
                  refine ⟨749632461422204447419397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1999019897125878526451725 749632461422204447419397)
                  ·
                    refine ⟨140556086516663333891137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749632461422204447419397 140556086516663333891137)
                    ·
                      refine ⟨105417064887497500418353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140556086516663333891137 105417064887497500418353)
                      ·
                        rfl

theorem cell23_205299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4, 2].length) (baseStart_205299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205299 prefixEnd_205299 := by exact prefixLift 205299
  have htrace : WordTrace (prefixWord ++ tailWord_205299) baseStart_205299 baseEnd_205299 := by
    simpa [prefixWord, tailWord_205299, baseEnd_205299] using wordTrace_append hprefix tailTrace_205299
  have hstable : (prefixWord ++ tailWord_205299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205299).length < 2 ^ (prefixWord ++ tailWord_205299).sum := by decide
  have hdescent : baseEnd_205299 < baseStart_205299 := by decide
  rcases family_descends (prefixWord ++ tailWord_205299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205349 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_205349 : Nat := 118140960795 + 205349 * 2 ^ 59
def prefixEnd_205349 : Nat := 4983230072969 + 3 ^ 40 * 205349 * 2
def baseEnd_205349 : Nat := 105442738920222304793123

theorem tailTrace_205349 : CollatzResearch.WordTrace tailWord_205349 prefixEnd_205349 105442738920222304793123 := by
  unfold tailWord_205349
  simp only [CollatzResearch.WordTrace]
  refine ⟨7489693333063118662179101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4993128888708745774786067 7489693333063118662179101)
  ·
    refine ⟨2808634999898669498317163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7489693333063118662179101 2808634999898669498317163)
    ·
      refine ⟨4212952499848004247475745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2808634999898669498317163 4212952499848004247475745)
      ·
        refine ⟨3159714374886003185606809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4212952499848004247475745 3159714374886003185606809)
        ·
          refine ⟨2369785781164502389205107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3159714374886003185606809 2369785781164502389205107)
          ·
            refine ⟨3554678671746753583807661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369785781164502389205107 3554678671746753583807661)
            ·
              refine ⟨1333004501905032593927873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3554678671746753583807661 1333004501905032593927873)
              ·
                refine ⟨999753376428774445445905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333004501905032593927873 999753376428774445445905)
                ·
                  refine ⟨749815032321580834084429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999753376428774445445905 749815032321580834084429)
                  ·
                    refine ⟨281180637120592812781661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749815032321580834084429 281180637120592812781661)
                    ·
                      refine ⟨105442738920222304793123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 281180637120592812781661 105442738920222304793123)
                      ·
                        rfl

theorem cell23_205349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_205349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205349 prefixEnd_205349 := by exact prefixLift 205349
  have htrace : WordTrace (prefixWord ++ tailWord_205349) baseStart_205349 baseEnd_205349 := by
    simpa [prefixWord, tailWord_205349, baseEnd_205349] using wordTrace_append hprefix tailTrace_205349
  have hstable : (prefixWord ++ tailWord_205349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205349).length < 2 ^ (prefixWord ++ tailWord_205349).sum := by decide
  have hdescent : baseEnd_205349 < baseStart_205349 := by decide
  rcases family_descends (prefixWord ++ tailWord_205349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205494 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_205494 : Nat := 118140960795 + 205494 * 2 ^ 59
def prefixEnd_205494 : Nat := 4983230072969 + 3 ^ 40 * 205494 * 2
def baseEnd_205494 : Nat := 105517193615124237479957

theorem tailTrace_205494 : CollatzResearch.WordTrace tailWord_205494 prefixEnd_205494 105517193615124237479957 := by
  unfold tailWord_205494
  simp only [CollatzResearch.WordTrace]
  refine ⟨468436369846113026637971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4996654611691872284138357 468436369846113026637971)
  ·
    refine ⟨702654554769169539956957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468436369846113026637971 702654554769169539956957)
    ·
      refine ⟨263495458038438577483859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 702654554769169539956957 263495458038438577483859)
      ·
        refine ⟨395243187057657866225789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263495458038438577483859 395243187057657866225789)
        ·
          refine ⟨148216195146621699834671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395243187057657866225789 148216195146621699834671)
          ·
            refine ⟨222324292719932549752007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148216195146621699834671 222324292719932549752007)
            ·
              refine ⟨333486439079898824628011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222324292719932549752007 333486439079898824628011)
              ·
                refine ⟨500229658619848236942017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333486439079898824628011 500229658619848236942017)
                ·
                  refine ⟨375172243964886177706513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500229658619848236942017 375172243964886177706513)
                  ·
                    refine ⟨281379182973664633279885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 375172243964886177706513 281379182973664633279885)
                    ·
                      refine ⟨105517193615124237479957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 281379182973664633279885 105517193615124237479957)
                      ·
                        rfl

theorem cell23_205494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_205494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205494 prefixEnd_205494 := by exact prefixLift 205494
  have htrace : WordTrace (prefixWord ++ tailWord_205494) baseStart_205494 baseEnd_205494 := by
    simpa [prefixWord, tailWord_205494, baseEnd_205494] using wordTrace_append hprefix tailTrace_205494
  have hstable : (prefixWord ++ tailWord_205494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205494).length < 2 ^ (prefixWord ++ tailWord_205494).sum := by decide
  have hdescent : baseEnd_205494 < baseStart_205494 := by decide
  rcases family_descends (prefixWord ++ tailWord_205494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205530 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2]
def baseStart_205530 : Nat := 118140960795 + 205530 * 2 ^ 59
def prefixEnd_205530 : Nat := 4983230072969 + 3 ^ 40 * 205530 * 2
def baseEnd_205530 : Nat := 105535678918686096629791

theorem tailTrace_205530 : CollatzResearch.WordTrace tailWord_205530 prefixEnd_205530 105535678918686096629791 := by
  unfold tailWord_205530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874073736351846643629511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4997529963604924383012029 1874073736351846643629511)
  ·
    refine ⟨2811110604527769965444267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1874073736351846643629511 2811110604527769965444267)
    ·
      refine ⟨4216665906791654948166401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2811110604527769965444267 4216665906791654948166401)
      ·
        refine ⟨3162499430093741211124801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4216665906791654948166401 3162499430093741211124801)
        ·
          refine ⟨2371874572570305908343601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3162499430093741211124801 2371874572570305908343601)
          ·
            refine ⟨1778905929427729431257701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2371874572570305908343601 1778905929427729431257701)
            ·
              refine ⟨333544861767699268360819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1778905929427729431257701 333544861767699268360819)
              ·
                refine ⟨500317292651548902541229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333544861767699268360819 500317292651548902541229)
                ·
                  refine ⟨187618984744330838452961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500317292651548902541229 187618984744330838452961)
                  ·
                    refine ⟨140714238558248128839721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187618984744330838452961 140714238558248128839721)
                    ·
                      refine ⟨105535678918686096629791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140714238558248128839721 105535678918686096629791)
                      ·
                        rfl

theorem cell23_205530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_205530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205530 prefixEnd_205530 := by exact prefixLift 205530
  have htrace : WordTrace (prefixWord ++ tailWord_205530) baseStart_205530 baseEnd_205530 := by
    simpa [prefixWord, tailWord_205530, baseEnd_205530] using wordTrace_append hprefix tailTrace_205530
  have hstable : (prefixWord ++ tailWord_205530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205530).length < 2 ^ (prefixWord ++ tailWord_205530).sum := by decide
  have hdescent : baseEnd_205530 < baseStart_205530 := by decide
  rcases family_descends (prefixWord ++ tailWord_205530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205540 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_205540 : Nat := 118140960795 + 205540 * 2 ^ 59
def prefixEnd_205540 : Nat := 4983230072969 + 3 ^ 40 * 205540 * 2
def baseEnd_205540 : Nat := 35180271241743685834915

theorem tailTrace_205540 : CollatzResearch.WordTrace tailWord_205540 prefixEnd_205540 35180271241743685834915 := by
  unfold tailWord_205540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3748329837685579141191037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4997773116914105521588049 3748329837685579141191037)
  ·
    refine ⟨1405623689132092177946639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3748329837685579141191037 1405623689132092177946639)
    ·
      refine ⟨2108435533698138266919959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405623689132092177946639 2108435533698138266919959)
      ·
        refine ⟨3162653300547207400379939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108435533698138266919959 3162653300547207400379939)
        ·
          refine ⟨4743979950820811100569909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162653300547207400379939 4743979950820811100569909)
          ·
            refine ⟨444748120389451040678429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4743979950820811100569909 444748120389451040678429)
            ·
              refine ⟨166780545146044140254411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444748120389451040678429 166780545146044140254411)
              ·
                refine ⟨250170817719066210381617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166780545146044140254411 250170817719066210381617)
                ·
                  refine ⟨187628113289299657786213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250170817719066210381617 187628113289299657786213)
                  ·
                    refine ⟨35180271241743685834915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187628113289299657786213 35180271241743685834915)
                    ·
                      rfl

theorem cell23_205540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_205540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205540 prefixEnd_205540 := by exact prefixLift 205540
  have htrace : WordTrace (prefixWord ++ tailWord_205540) baseStart_205540 baseEnd_205540 := by
    simpa [prefixWord, tailWord_205540, baseEnd_205540] using wordTrace_append hprefix tailTrace_205540
  have hstable : (prefixWord ++ tailWord_205540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205540).length < 2 ^ (prefixWord ++ tailWord_205540).sum := by decide
  have hdescent : baseEnd_205540 < baseStart_205540 := by decide
  rcases family_descends (prefixWord ++ tailWord_205540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205550 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_205550 : Nat := 118140960795 + 205550 * 2 ^ 59
def prefixEnd_205550 : Nat := 4983230072969 + 3 ^ 40 * 205550 * 2
def baseEnd_205550 : Nat := 105545948531776018379699

theorem tailTrace_205550 : CollatzResearch.WordTrace tailWord_205550 prefixEnd_205550 105545948531776018379699 := by
  unfold tailWord_205550
  simp only [CollatzResearch.WordTrace]
  refine ⟨937128050666866248780763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4998016270223286660164069 937128050666866248780763)
  ·
    refine ⟨1405692076000299373171145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 937128050666866248780763 1405692076000299373171145)
    ·
      refine ⟨1054269057000224529878359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1405692076000299373171145 1054269057000224529878359)
      ·
        refine ⟨1581403585500336794817539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054269057000224529878359 1581403585500336794817539)
        ·
          refine ⟨2372105378250505192226309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581403585500336794817539 2372105378250505192226309)
          ·
            refine ⟨444769758421969723542433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2372105378250505192226309 444769758421969723542433)
            ·
              refine ⟨333577318816477292656825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444769758421969723542433 333577318816477292656825)
              ·
                refine ⟨250182989112357969492619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333577318816477292656825 250182989112357969492619)
                ·
                  refine ⟨375274483668536954238929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250182989112357969492619 375274483668536954238929)
                  ·
                    refine ⟨281455862751402715679197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 375274483668536954238929 281455862751402715679197)
                    ·
                      refine ⟨105545948531776018379699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 281455862751402715679197 105545948531776018379699)
                      ·
                        rfl

theorem cell23_205550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_205550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205550 prefixEnd_205550 := by exact prefixLift 205550
  have htrace : WordTrace (prefixWord ++ tailWord_205550) baseStart_205550 baseEnd_205550 := by
    simpa [prefixWord, tailWord_205550, baseEnd_205550] using wordTrace_append hprefix tailTrace_205550
  have hstable : (prefixWord ++ tailWord_205550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205550).length < 2 ^ (prefixWord ++ tailWord_205550).sum := by decide
  have hdescent : baseEnd_205550 < baseStart_205550 := by decide
  rcases family_descends (prefixWord ++ tailWord_205550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205564 : List Nat := [2, 2, 2, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_205564 : Nat := 118140960795 + 205564 * 2 ^ 59
def prefixEnd_205564 : Nat := 4983230072969 + 3 ^ 40 * 205564 * 2
def baseEnd_205564 : Nat := 105553137260938963604635

theorem tailTrace_205564 : CollatzResearch.WordTrace tailWord_205564 prefixEnd_205564 105553137260938963604635 := by
  unfold tailWord_205564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3748767513642105190627873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4998356684856140254170497 3748767513642105190627873)
  ·
    refine ⟨2811575635231578892970905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3748767513642105190627873 2811575635231578892970905)
    ·
      refine ⟨2108681726423684169728179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2811575635231578892970905 2108681726423684169728179)
      ·
        refine ⟨3163022589635526254592269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108681726423684169728179 3163022589635526254592269)
        ·
          refine ⟨1186133471113322345472101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3163022589635526254592269 1186133471113322345472101)
          ·
            refine ⟨222400025833747939776019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1186133471113322345472101 222400025833747939776019)
            ·
              refine ⟨333600038750621909664029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222400025833747939776019 333600038750621909664029)
              ·
                refine ⟨125100014531483216124011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333600038750621909664029 125100014531483216124011)
                ·
                  refine ⟨187650021797224824186017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125100014531483216124011 187650021797224824186017)
                  ·
                    refine ⟨140737516347918618139513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187650021797224824186017 140737516347918618139513)
                    ·
                      refine ⟨105553137260938963604635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140737516347918618139513 105553137260938963604635)
                      ·
                        rfl

theorem cell23_205564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_205564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205564 prefixEnd_205564 := by exact prefixLift 205564
  have htrace : WordTrace (prefixWord ++ tailWord_205564) baseStart_205564 baseEnd_205564 := by
    simpa [prefixWord, tailWord_205564, baseEnd_205564] using wordTrace_append hprefix tailTrace_205564
  have hstable : (prefixWord ++ tailWord_205564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205564).length < 2 ^ (prefixWord ++ tailWord_205564).sum := by decide
  have hdescent : baseEnd_205564 < baseStart_205564 := by decide
  rcases family_descends (prefixWord ++ tailWord_205564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205603 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 1, 4, 2]
def baseStart_205603 : Nat := 118140960795 + 205603 * 2 ^ 59
def prefixEnd_205603 : Nat := 4983230072969 + 3 ^ 40 * 205603 * 2
def baseEnd_205603 : Nat := 105573163006464311016955

theorem tailTrace_205603 : CollatzResearch.WordTrace tailWord_205603 prefixEnd_205603 105573163006464311016955 := by
  unfold tailWord_205603
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498957474142920041925463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4999304982761946694616975 7498957474142920041925463)
  ·
    refine ⟨11248436211214380062888195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7498957474142920041925463 11248436211214380062888195)
    ·
      refine ⟨16872654316821570094332293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11248436211214380062888195 16872654316821570094332293)
      ·
        refine ⟨3163622684404044392687305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16872654316821570094332293 3163622684404044392687305)
        ·
          refine ⟨2372717013303033294515479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3163622684404044392687305 2372717013303033294515479)
          ·
            refine ⟨3559075519954549941773219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372717013303033294515479 3559075519954549941773219)
            ·
              refine ⟨5338613279931824912659829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559075519954549941773219 5338613279931824912659829)
              ·
                refine ⟨500494994993608585561859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5338613279931824912659829 500494994993608585561859)
                ·
                  refine ⟨750742492490412878342789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500494994993608585561859 750742492490412878342789)
                  ·
                    refine ⟨140764217341952414689273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750742492490412878342789 140764217341952414689273)
                    ·
                      refine ⟨105573163006464311016955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140764217341952414689273 105573163006464311016955)
                      ·
                        rfl

theorem cell23_205603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_205603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205603 prefixEnd_205603 := by exact prefixLift 205603
  have htrace : WordTrace (prefixWord ++ tailWord_205603) baseStart_205603 baseEnd_205603 := by
    simpa [prefixWord, tailWord_205603, baseEnd_205603] using wordTrace_append hprefix tailTrace_205603
  have hstable : (prefixWord ++ tailWord_205603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205603).length < 2 ^ (prefixWord ++ tailWord_205603).sum := by decide
  have hdescent : baseEnd_205603 < baseStart_205603 := by decide
  rcases family_descends (prefixWord ++ tailWord_205603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205653 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_205653 : Nat := 118140960795 + 205653 * 2 ^ 59
def prefixEnd_205653 : Nat := 4983230072969 + 3 ^ 40 * 205653 * 2
def baseEnd_205653 : Nat := 105598837039189115391725

theorem tailTrace_205653 : CollatzResearch.WordTrace tailWord_205653 prefixEnd_205653 105598837039189115391725 := by
  unfold tailWord_205653
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500781123961778581245613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5000520749307852387497075 7500781123961778581245613)
  ·
    refine ⟨2812792921485666967967105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7500781123961778581245613 2812792921485666967967105)
    ·
      refine ⟨2109594691114250225975329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2812792921485666967967105 2109594691114250225975329)
      ·
        refine ⟨1582196018335687669481497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2109594691114250225975329 1582196018335687669481497)
        ·
          refine ⟨1186647013751765752111123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1582196018335687669481497 1186647013751765752111123)
          ·
            refine ⟨1779970520627648628166685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186647013751765752111123 1779970520627648628166685)
            ·
              refine ⟨667488945235368235562507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1779970520627648628166685 667488945235368235562507)
              ·
                refine ⟨1001233417853052353343761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667488945235368235562507 1001233417853052353343761)
                ·
                  refine ⟨750925063389789265007821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1001233417853052353343761 750925063389789265007821)
                  ·
                    refine ⟨281596898771170974377933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750925063389789265007821 281596898771170974377933)
                    ·
                      refine ⟨105598837039189115391725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 281596898771170974377933 105598837039189115391725)
                      ·
                        rfl

theorem cell23_205653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_205653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205653 prefixEnd_205653 := by exact prefixLift 205653
  have htrace : WordTrace (prefixWord ++ tailWord_205653) baseStart_205653 baseEnd_205653 := by
    simpa [prefixWord, tailWord_205653, baseEnd_205653] using wordTrace_append hprefix tailTrace_205653
  have hstable : (prefixWord ++ tailWord_205653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205653).length < 2 ^ (prefixWord ++ tailWord_205653).sum := by decide
  have hdescent : baseEnd_205653 < baseStart_205653 := by decide
  rcases family_descends (prefixWord ++ tailWord_205653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205656 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 4, 5]
def baseStart_205656 : Nat := 118140960795 + 205656 * 2 ^ 59
def prefixEnd_205656 : Nat := 4983230072969 + 3 ^ 40 * 205656 * 2
def baseEnd_205656 : Nat := 35200125827050867884737

theorem tailTrace_205656 : CollatzResearch.WordTrace tailWord_205656 prefixEnd_205656 35200125827050867884737 := by
  unfold tailWord_205656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750445271475455046802411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5000593695300606729069881 3750445271475455046802411)
  ·
    refine ⟨5625667907213182570203617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3750445271475455046802411 5625667907213182570203617)
    ·
      refine ⟨4219250930409886927652713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5625667907213182570203617 4219250930409886927652713)
      ·
        refine ⟨3164438197807415195739535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4219250930409886927652713 3164438197807415195739535)
        ·
          refine ⟨4746657296711122793609303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164438197807415195739535 4746657296711122793609303)
          ·
            refine ⟨7119985945066684190413955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746657296711122793609303 7119985945066684190413955)
            ·
              refine ⟨10679978917600026285620933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7119985945066684190413955 10679978917600026285620933)
              ·
                refine ⟨2002496047050004928553925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10679978917600026285620933 2002496047050004928553925)
                ·
                  refine ⟨375468008821875924103861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002496047050004928553925 375468008821875924103861)
                  ·
                    refine ⟨35200125827050867884737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 375468008821875924103861 35200125827050867884737)
                    ·
                      rfl

theorem cell23_205656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_205656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205656 prefixEnd_205656 := by exact prefixLift 205656
  have htrace : WordTrace (prefixWord ++ tailWord_205656) baseStart_205656 baseEnd_205656 := by
    simpa [prefixWord, tailWord_205656, baseEnd_205656] using wordTrace_append hprefix tailTrace_205656
  have hstable : (prefixWord ++ tailWord_205656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205656).length < 2 ^ (prefixWord ++ tailWord_205656).sum := by decide
  have hdescent : baseEnd_205656 < baseStart_205656 := by decide
  rcases family_descends (prefixWord ++ tailWord_205656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205663 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 2, 5, 2]
def baseStart_205663 : Nat := 118140960795 + 205663 * 2 ^ 59
def prefixEnd_205663 : Nat := 4983230072969 + 3 ^ 40 * 205663 * 2
def baseEnd_205663 : Nat := 105603971845734076266679

theorem tailTrace_205663 : CollatzResearch.WordTrace tailWord_205663 prefixEnd_205663 105603971845734076266679 := by
  unfold tailWord_205663
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501145853925550289109643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5000763902617033526073095 7501145853925550289109643)
  ·
    refine ⟨11251718780888325433664465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7501145853925550289109643 11251718780888325433664465)
    ·
      refine ⟨8438789085666244075248349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11251718780888325433664465 8438789085666244075248349)
      ·
        refine ⟨3164545907124841528218131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8438789085666244075248349 3164545907124841528218131)
        ·
          refine ⟨4746818860687262292327197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164545907124841528218131 4746818860687262292327197)
          ·
            refine ⟨1780057072757723359622699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4746818860687262292327197 1780057072757723359622699)
            ·
              refine ⟨2670085609136585039434049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780057072757723359622699 2670085609136585039434049)
              ·
                refine ⟨2002564206852438779575537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670085609136585039434049 2002564206852438779575537)
                ·
                  refine ⟨1501923155139329084681653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002564206852438779575537 1501923155139329084681653)
                  ·
                    refine ⟨140805295794312101688905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1501923155139329084681653 140805295794312101688905)
                    ·
                      refine ⟨105603971845734076266679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140805295794312101688905 105603971845734076266679)
                      ·
                        rfl

theorem cell23_205663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_205663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205663 prefixEnd_205663 := by exact prefixLift 205663
  have htrace : WordTrace (prefixWord ++ tailWord_205663) baseStart_205663 baseEnd_205663 := by
    simpa [prefixWord, tailWord_205663, baseEnd_205663] using wordTrace_append hprefix tailTrace_205663
  have hstable : (prefixWord ++ tailWord_205663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205663).length < 2 ^ (prefixWord ++ tailWord_205663).sum := by decide
  have hdescent : baseEnd_205663 < baseStart_205663 := by decide
  rcases family_descends (prefixWord ++ tailWord_205663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205693 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_205693 : Nat := 118140960795 + 205693 * 2 ^ 59
def prefixEnd_205693 : Nat := 4983230072969 + 3 ^ 40 * 205693 * 2
def baseEnd_205693 : Nat := 105619376265368958891541

theorem tailTrace_205693 : CollatzResearch.WordTrace tailWord_205693 prefixEnd_205693 105619376265368958891541 := by
  unfold tailWord_205693
  simp only [CollatzResearch.WordTrace]
  refine ⟨7502240043816865412701733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5001493362544576941801155 7502240043816865412701733)
  ·
    refine ⟨1406670008215662264881575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7502240043816865412701733 1406670008215662264881575)
    ·
      refine ⟨2110005012323493397322363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1406670008215662264881575 2110005012323493397322363)
      ·
        refine ⟨3165007518485240095983545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110005012323493397322363 3165007518485240095983545)
        ·
          refine ⟨2373755638863930071987659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3165007518485240095983545 2373755638863930071987659)
          ·
            refine ⟨3560633458295895107981489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373755638863930071987659 3560633458295895107981489)
            ·
              refine ⟨2670475093721921330986117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3560633458295895107981489 2670475093721921330986117)
              ·
                refine ⟨500714080072860249559897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2670475093721921330986117 500714080072860249559897)
                ·
                  refine ⟨375535560054645187169923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500714080072860249559897 375535560054645187169923)
                  ·
                    refine ⟨563303340081967780754885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375535560054645187169923 563303340081967780754885)
                    ·
                      refine ⟨105619376265368958891541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 563303340081967780754885 105619376265368958891541)
                      ·
                        rfl

theorem cell23_205693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_205693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205693 prefixEnd_205693 := by exact prefixLift 205693
  have htrace : WordTrace (prefixWord ++ tailWord_205693) baseStart_205693 baseEnd_205693 := by
    simpa [prefixWord, tailWord_205693, baseEnd_205693] using wordTrace_append hprefix tailTrace_205693
  have hstable : (prefixWord ++ tailWord_205693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205693).length < 2 ^ (prefixWord ++ tailWord_205693).sum := by decide
  have hdescent : baseEnd_205693 < baseStart_205693 := by decide
  rcases family_descends (prefixWord ++ tailWord_205693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205730 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_205730 : Nat := 118140960795 + 205730 * 2 ^ 59
def prefixEnd_205730 : Nat := 4983230072969 + 3 ^ 40 * 205730 * 2
def baseEnd_205730 : Nat := 105638375049585314128871

theorem tailTrace_205730 : CollatzResearch.WordTrace tailWord_205730 prefixEnd_205730 105638375049585314128871 := by
  unfold tailWord_205730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875897386170705182949661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5002393029788547154532429 1875897386170705182949661)
  ·
    refine ⟨703461519814014443606123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1875897386170705182949661 703461519814014443606123)
    ·
      refine ⟨1055192279721021665409185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703461519814014443606123 1055192279721021665409185)
      ·
        refine ⟨791394209790766249056889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055192279721021665409185 791394209790766249056889)
        ·
          refine ⟨593545657343074686792667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791394209790766249056889 593545657343074686792667)
          ·
            refine ⟨890318486014612030189001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593545657343074686792667 890318486014612030189001)
            ·
              refine ⟨667738864510959022641751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890318486014612030189001 667738864510959022641751)
              ·
                refine ⟨1001608296766438533962627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667738864510959022641751 1001608296766438533962627)
                ·
                  refine ⟨1502412445149657800943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001608296766438533962627 1502412445149657800943941)
                  ·
                    refine ⟨281702333465560837676989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502412445149657800943941 281702333465560837676989)
                    ·
                      refine ⟨105638375049585314128871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 281702333465560837676989 105638375049585314128871)
                      ·
                        rfl

theorem cell23_205730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_205730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205730 prefixEnd_205730 := by exact prefixLift 205730
  have htrace : WordTrace (prefixWord ++ tailWord_205730) baseStart_205730 baseEnd_205730 := by
    simpa [prefixWord, tailWord_205730, baseEnd_205730] using wordTrace_append hprefix tailTrace_205730
  have hstable : (prefixWord ++ tailWord_205730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205730).length < 2 ^ (prefixWord ++ tailWord_205730).sum := by decide
  have hdescent : baseEnd_205730 < baseStart_205730 := by decide
  rcases family_descends (prefixWord ++ tailWord_205730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205770 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_205770 : Nat := 118140960795 + 205770 * 2 ^ 59
def prefixEnd_205770 : Nat := 4983230072969 + 3 ^ 40 * 205770 * 2
def baseEnd_205770 : Nat := 105658914275765157628687

theorem tailTrace_205770 : CollatzResearch.WordTrace tailWord_205770 prefixEnd_205770 105658914275765157628687 := by
  unfold tailWord_205770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876262116134476890813691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5003365643025271708836509 1876262116134476890813691)
  ·
    refine ⟨2814393174201715336220537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876262116134476890813691 2814393174201715336220537)
    ·
      refine ⟨2110794880651286502165403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2814393174201715336220537 2110794880651286502165403)
      ·
        refine ⟨3166192320976929753248105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110794880651286502165403 3166192320976929753248105)
        ·
          refine ⟨2374644240732697314936079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3166192320976929753248105 2374644240732697314936079)
          ·
            refine ⟨3561966361099045972404119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374644240732697314936079 3561966361099045972404119)
            ·
              refine ⟨5342949541648568958606179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561966361099045972404119 5342949541648568958606179)
              ·
                refine ⟨8014424312472853437909269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342949541648568958606179 8014424312472853437909269)
                ·
                  refine ⟨375676139647165004901997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8014424312472853437909269 375676139647165004901997)
                  ·
                    refine ⟨140878552367686876838249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375676139647165004901997 140878552367686876838249)
                    ·
                      refine ⟨105658914275765157628687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140878552367686876838249 105658914275765157628687)
                      ·
                        rfl

theorem cell23_205770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_205770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205770 prefixEnd_205770 := by exact prefixLift 205770
  have htrace : WordTrace (prefixWord ++ tailWord_205770) baseStart_205770 baseEnd_205770 := by
    simpa [prefixWord, tailWord_205770, baseEnd_205770] using wordTrace_append hprefix tailTrace_205770
  have hstable : (prefixWord ++ tailWord_205770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205770).length < 2 ^ (prefixWord ++ tailWord_205770).sum := by decide
  have hdescent : baseEnd_205770 < baseStart_205770 := by decide
  rcases family_descends (prefixWord ++ tailWord_205770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205780 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_205780 : Nat := 118140960795 + 205780 * 2 ^ 59
def prefixEnd_205780 : Nat := 4983230072969 + 3 ^ 40 * 205780 * 2
def baseEnd_205780 : Nat := 35221349694103372834547

theorem tailTrace_205780 : CollatzResearch.WordTrace tailWord_205780 prefixEnd_205780 35221349694103372834547 := by
  unfold tailWord_205780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752706597250839635559397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5003608796334452847412529 3752706597250839635559397)
  ·
    refine ⟨703632486984532431667387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3752706597250839635559397 703632486984532431667387)
    ·
      refine ⟨1055448730476798647501081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703632486984532431667387 1055448730476798647501081)
      ·
        refine ⟨791586547857598985625811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055448730476798647501081 791586547857598985625811)
        ·
          refine ⟨1187379821786398478438717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791586547857598985625811 1187379821786398478438717)
          ·
            refine ⟨445267433169899429414519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1187379821786398478438717 445267433169899429414519)
            ·
              refine ⟨667901149754849144121779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445267433169899429414519 667901149754849144121779)
              ·
                refine ⟨1001851724632273716182669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667901149754849144121779 1001851724632273716182669)
                ·
                  refine ⟨375694396737102643568501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001851724632273716182669 375694396737102643568501)
                  ·
                    refine ⟨35221349694103372834547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 375694396737102643568501 35221349694103372834547)
                    ·
                      rfl

theorem cell23_205780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_205780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205780 prefixEnd_205780 := by exact prefixLift 205780
  have htrace : WordTrace (prefixWord ++ tailWord_205780) baseStart_205780 baseEnd_205780 := by
    simpa [prefixWord, tailWord_205780, baseEnd_205780] using wordTrace_append hprefix tailTrace_205780
  have hstable : (prefixWord ++ tailWord_205780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205780).length < 2 ^ (prefixWord ++ tailWord_205780).sum := by decide
  have hdescent : baseEnd_205780 < baseStart_205780 := by decide
  rcases family_descends (prefixWord ++ tailWord_205780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205800 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_205800 : Nat := 118140960795 + 205800 * 2 ^ 59
def prefixEnd_205800 : Nat := 4983230072969 + 3 ^ 40 * 205800 * 2
def baseEnd_205800 : Nat := 105674318695400040253549

theorem tailTrace_205800 : CollatzResearch.WordTrace tailWord_205800 prefixEnd_205800 105674318695400040253549 := by
  unfold tailWord_205800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753071327214611343423427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5004095102952815124564569 3753071327214611343423427)
  ·
    refine ⟨5629606990821917015135141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3753071327214611343423427 5629606990821917015135141)
    ·
      refine ⟨1055551310779109440337839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5629606990821917015135141 1055551310779109440337839)
      ·
        refine ⟨1583326966168664160506759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055551310779109440337839 1583326966168664160506759)
        ·
          refine ⟨2374990449252996240760139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583326966168664160506759 2374990449252996240760139)
          ·
            refine ⟨3562485673879494361140209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374990449252996240760139 3562485673879494361140209)
            ·
              refine ⟨2671864255409620770855157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3562485673879494361140209 2671864255409620770855157)
              ·
                refine ⟨250487273944651947267671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2671864255409620770855157 250487273944651947267671)
                ·
                  refine ⟨375730910916977920901507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250487273944651947267671 375730910916977920901507)
                  ·
                    refine ⟨563596366375466881352261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375730910916977920901507 563596366375466881352261)
                    ·
                      refine ⟨105674318695400040253549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 563596366375466881352261 105674318695400040253549)
                      ·
                        rfl

theorem cell23_205800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_205800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205800 prefixEnd_205800 := by exact prefixLift 205800
  have htrace : WordTrace (prefixWord ++ tailWord_205800) baseStart_205800 baseEnd_205800 := by
    simpa [prefixWord, tailWord_205800, baseEnd_205800] using wordTrace_append hprefix tailTrace_205800
  have hstable : (prefixWord ++ tailWord_205800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205800).length < 2 ^ (prefixWord ++ tailWord_205800).sum := by decide
  have hdescent : baseEnd_205800 < baseStart_205800 := by decide
  rcases family_descends (prefixWord ++ tailWord_205800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205817 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 3, 2, 2]
def baseStart_205817 : Nat := 118140960795 + 205817 * 2 ^ 59
def prefixEnd_205817 : Nat := 4983230072969 + 3 ^ 40 * 205817 * 2
def baseEnd_205817 : Nat := 105683047866526473740971

theorem tailTrace_205817 : CollatzResearch.WordTrace tailWord_205817 prefixEnd_205817 105683047866526473740971 := by
  unfold tailWord_205817
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506762695367634590215705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5004508463578423060143803 7506762695367634590215705)
  ·
    refine ⟨5630072021525725942661779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7506762695367634590215705 5630072021525725942661779)
    ·
      refine ⟨8445108032288588913992669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5630072021525725942661779 8445108032288588913992669)
      ·
        refine ⟨3166915512108220842747251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8445108032288588913992669 3166915512108220842747251)
        ·
          refine ⟨4750373268162331264120877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166915512108220842747251 4750373268162331264120877)
          ·
            refine ⟨1781389975560874224045329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4750373268162331264120877 1781389975560874224045329)
            ·
              refine ⟨1336042481670655668033997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781389975560874224045329 1336042481670655668033997)
              ·
                refine ⟨501015930626495875512749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1336042481670655668033997 501015930626495875512749)
                ·
                  refine ⟨187880973984935953317281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501015930626495875512749 187880973984935953317281)
                  ·
                    refine ⟨140910730488701964987961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187880973984935953317281 140910730488701964987961)
                    ·
                      refine ⟨105683047866526473740971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140910730488701964987961 105683047866526473740971)
                      ·
                        rfl

theorem cell23_205817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_205817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205817 prefixEnd_205817 := by exact prefixLift 205817
  have htrace : WordTrace (prefixWord ++ tailWord_205817) baseStart_205817 baseEnd_205817 := by
    simpa [prefixWord, tailWord_205817, baseEnd_205817] using wordTrace_append hprefix tailTrace_205817
  have hstable : (prefixWord ++ tailWord_205817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205817).length < 2 ^ (prefixWord ++ tailWord_205817).sum := by decide
  have hdescent : baseEnd_205817 < baseStart_205817 := by decide
  rcases family_descends (prefixWord ++ tailWord_205817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205820 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_205820 : Nat := 118140960795 + 205820 * 2 ^ 59
def prefixEnd_205820 : Nat := 4983230072969 + 3 ^ 40 * 205820 * 2
def baseEnd_205820 : Nat := 105684588308489962003457

theorem tailTrace_205820 : CollatzResearch.WordTrace tailWord_205820 prefixEnd_205820 105684588308489962003457 := by
  unfold tailWord_205820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753436057178383051287457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5004581409571177401716609 3753436057178383051287457)
  ·
    refine ⟨2815077042883787288465593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3753436057178383051287457 2815077042883787288465593)
    ·
      refine ⟨2111307782162840466349195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2815077042883787288465593 2111307782162840466349195)
      ·
        refine ⟨3166961673244260699523793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111307782162840466349195 3166961673244260699523793)
        ·
          refine ⟨2375221254933195524642845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3166961673244260699523793 2375221254933195524642845)
          ·
            refine ⟨890707970599948321741067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2375221254933195524642845 890707970599948321741067)
            ·
              refine ⟨1336061955899922482611601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890707970599948321741067 1336061955899922482611601)
              ·
                refine ⟨1002046466924941861958701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336061955899922482611601 1002046466924941861958701)
                ·
                  refine ⟨375767425096853198234513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002046466924941861958701 375767425096853198234513)
                  ·
                    refine ⟨281825568822639898675885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 375767425096853198234513 281825568822639898675885)
                    ·
                      refine ⟨105684588308489962003457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 281825568822639898675885 105684588308489962003457)
                      ·
                        rfl

theorem cell23_205820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_205820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205820 prefixEnd_205820 := by exact prefixLift 205820
  have htrace : WordTrace (prefixWord ++ tailWord_205820) baseStart_205820 baseEnd_205820 := by
    simpa [prefixWord, tailWord_205820, baseEnd_205820] using wordTrace_append hprefix tailTrace_205820
  have hstable : (prefixWord ++ tailWord_205820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205820).length < 2 ^ (prefixWord ++ tailWord_205820).sum := by decide
  have hdescent : baseEnd_205820 < baseStart_205820 := by decide
  rcases family_descends (prefixWord ++ tailWord_205820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205834 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_205834 : Nat := 118140960795 + 205834 * 2 ^ 59
def prefixEnd_205834 : Nat := 4983230072969 + 3 ^ 40 * 205834 * 2
def baseEnd_205834 : Nat := 105691777037652907228393

theorem tailTrace_205834 : CollatzResearch.WordTrace tailWord_205834 prefixEnd_205834 105691777037652907228393 := by
  unfold tailWord_205834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876845684076511623396139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5004921824204030995723037 1876845684076511623396139)
  ·
    refine ⟨2815268526114767435094209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876845684076511623396139 2815268526114767435094209)
    ·
      refine ⟨2111451394586075576320657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2815268526114767435094209 2111451394586075576320657)
      ·
        refine ⟨1583588545939556682240493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111451394586075576320657 1583588545939556682240493)
        ·
          refine ⟨593845704727333755840185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1583588545939556682240493 593845704727333755840185)
          ·
            refine ⟨445384278545500316880139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593845704727333755840185 445384278545500316880139)
            ·
              refine ⟨668076417818250475320209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445384278545500316880139 668076417818250475320209)
              ·
                refine ⟨501057313363687856490157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668076417818250475320209 501057313363687856490157)
                ·
                  refine ⟨187896492511382946183809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501057313363687856490157 187896492511382946183809)
                  ·
                    refine ⟨140922369383537209637857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187896492511382946183809 140922369383537209637857)
                    ·
                      refine ⟨105691777037652907228393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140922369383537209637857 105691777037652907228393)
                      ·
                        rfl

theorem cell23_205834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_205834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205834 prefixEnd_205834 := by exact prefixLift 205834
  have htrace : WordTrace (prefixWord ++ tailWord_205834) baseStart_205834 baseEnd_205834 := by
    simpa [prefixWord, tailWord_205834, baseEnd_205834] using wordTrace_append hprefix tailTrace_205834
  have hstable : (prefixWord ++ tailWord_205834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205834).length < 2 ^ (prefixWord ++ tailWord_205834).sum := by decide
  have hdescent : baseEnd_205834 < baseStart_205834 := by decide
  rcases family_descends (prefixWord ++ tailWord_205834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205850 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_205850 : Nat := 118140960795 + 205850 * 2 ^ 59
def prefixEnd_205850 : Nat := 4983230072969 + 3 ^ 40 * 205850 * 2
def baseEnd_205850 : Nat := 105699992728124844628319

theorem tailTrace_205850 : CollatzResearch.WordTrace tailWord_205850 prefixEnd_205850 105699992728124844628319 := by
  unfold tailWord_205850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876991576062020306541751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5005310869498720817444669 1876991576062020306541751)
  ·
    refine ⟨2815487364093030459812627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876991576062020306541751 2815487364093030459812627)
    ·
      refine ⟨4223231046139545689718941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815487364093030459812627 4223231046139545689718941)
      ·
        refine ⟨1583711642302329633644603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4223231046139545689718941 1583711642302329633644603)
        ·
          refine ⟨2375567463453494450466905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583711642302329633644603 2375567463453494450466905)
          ·
            refine ⟨1781675597590120837850179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375567463453494450466905 1781675597590120837850179)
            ·
              refine ⟨2672513396385181256775269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781675597590120837850179 2672513396385181256775269)
              ·
                refine ⟨501096261822221485645363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2672513396385181256775269 501096261822221485645363)
                ·
                  refine ⟨751644392733332228468045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501096261822221485645363 751644392733332228468045)
                  ·
                    refine ⟨281866647274999585675517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751644392733332228468045 281866647274999585675517)
                    ·
                      refine ⟨105699992728124844628319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 281866647274999585675517 105699992728124844628319)
                      ·
                        rfl

theorem cell23_205850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_205850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205850 prefixEnd_205850 := by exact prefixLift 205850
  have htrace : WordTrace (prefixWord ++ tailWord_205850) baseStart_205850 baseEnd_205850 := by
    simpa [prefixWord, tailWord_205850, baseEnd_205850] using wordTrace_append hprefix tailTrace_205850
  have hstable : (prefixWord ++ tailWord_205850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205850).length < 2 ^ (prefixWord ++ tailWord_205850).sum := by decide
  have hdescent : baseEnd_205850 < baseStart_205850 := by decide
  rcases family_descends (prefixWord ++ tailWord_205850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205907 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 4, 2, 2]
def baseStart_205907 : Nat := 118140960795 + 205907 * 2 ^ 59
def prefixEnd_205907 : Nat := 4983230072969 + 3 ^ 40 * 205907 * 2
def baseEnd_205907 : Nat := 105729261125431121615557

theorem tailTrace_205907 : CollatzResearch.WordTrace tailWord_205907 prefixEnd_205907 105729261125431121615557 := by
  unfold tailWord_205907
  simp only [CollatzResearch.WordTrace]
  refine ⟨7510045265041579960991975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5006696843361053307327983 7510045265041579960991975)
  ·
    refine ⟨11265067897562369941487963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7510045265041579960991975 11265067897562369941487963)
    ·
      refine ⟨16897601846343554912231945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11265067897562369941487963 16897601846343554912231945)
      ·
        refine ⟨12673201384757666184173959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16897601846343554912231945 12673201384757666184173959)
        ·
          refine ⟨19009802077136499276260939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12673201384757666184173959 19009802077136499276260939)
          ·
            refine ⟨28514703115704748914391409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19009802077136499276260939 28514703115704748914391409)
            ·
              refine ⟨21386027336778561685793557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28514703115704748914391409 21386027336778561685793557)
              ·
                refine ⟨1002470031411495079021573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21386027336778561685793557 1002470031411495079021573)
                ·
                  refine ⟨187963130889655327316545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002470031411495079021573 187963130889655327316545)
                  ·
                    refine ⟨140972348167241495487409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187963130889655327316545 140972348167241495487409)
                    ·
                      refine ⟨105729261125431121615557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140972348167241495487409 105729261125431121615557)
                      ·
                        rfl

theorem cell23_205907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 2, 2].length) (baseStart_205907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205907 prefixEnd_205907 := by exact prefixLift 205907
  have htrace : WordTrace (prefixWord ++ tailWord_205907) baseStart_205907 baseEnd_205907 := by
    simpa [prefixWord, tailWord_205907, baseEnd_205907] using wordTrace_append hprefix tailTrace_205907
  have hstable : (prefixWord ++ tailWord_205907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205907).length < 2 ^ (prefixWord ++ tailWord_205907).sum := by decide
  have hdescent : baseEnd_205907 < baseStart_205907 := by decide
  rcases family_descends (prefixWord ++ tailWord_205907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205923 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9]
def baseStart_205923 : Nat := 118140960795 + 205923 * 2 ^ 59
def prefixEnd_205923 : Nat := 4983230072969 + 3 ^ 40 * 205923 * 2
def baseEnd_205923 : Nat := 105737476815903059015483

theorem tailTrace_205923 : CollatzResearch.WordTrace tailWord_205923 prefixEnd_205923 105737476815903059015483 := by
  unfold tailWord_205923
  simp only [CollatzResearch.WordTrace]
  refine ⟨7510628832983614693574423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5007085888655743129049615 7510628832983614693574423)
  ·
    refine ⟨11265943249475422040361635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7510628832983614693574423 11265943249475422040361635)
    ·
      refine ⟨16898914874213133060542453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11265943249475422040361635 16898914874213133060542453)
      ·
        refine ⟨1584273269457481224425855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16898914874213133060542453 1584273269457481224425855)
        ·
          refine ⟨2376409904186221836638783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584273269457481224425855 2376409904186221836638783)
          ·
            refine ⟨3564614856279332754958175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376409904186221836638783 3564614856279332754958175)
            ·
              refine ⟨5346922284418999132437263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564614856279332754958175 5346922284418999132437263)
              ·
                refine ⟨8020383426628498698655895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346922284418999132437263 8020383426628498698655895)
                ·
                  refine ⟨12030575139942748047983843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8020383426628498698655895 12030575139942748047983843)
                  ·
                    refine ⟨18045862709914122071975765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12030575139942748047983843 18045862709914122071975765)
                    ·
                      refine ⟨105737476815903059015483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 18045862709914122071975765 105737476815903059015483)
                      ·
                        rfl

theorem cell23_205923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_205923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205923 prefixEnd_205923 := by exact prefixLift 205923
  have htrace : WordTrace (prefixWord ++ tailWord_205923) baseStart_205923 baseEnd_205923 := by
    simpa [prefixWord, tailWord_205923, baseEnd_205923] using wordTrace_append hprefix tailTrace_205923
  have hstable : (prefixWord ++ tailWord_205923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205923).length < 2 ^ (prefixWord ++ tailWord_205923).sum := by decide
  have hdescent : baseEnd_205923 < baseStart_205923 := by decide
  rcases family_descends (prefixWord ++ tailWord_205923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205924 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_205924 : Nat := 118140960795 + 205924 * 2 ^ 59
def prefixEnd_205924 : Nat := 4983230072969 + 3 ^ 40 * 205924 * 2
def baseEnd_205924 : Nat := 105737990296557555102979

theorem tailTrace_205924 : CollatzResearch.WordTrace tailWord_205924 prefixEnd_205924 105737990296557555102979 := by
  unfold tailWord_205924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755332652989995932180413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5007110203986661242907217 3755332652989995932180413)
  ·
    refine ⟨1408249744871248474567655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3755332652989995932180413 1408249744871248474567655)
    ·
      refine ⟨2112374617306872711851483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408249744871248474567655 2112374617306872711851483)
      ·
        refine ⟨3168561925960309067777225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112374617306872711851483 3168561925960309067777225)
        ·
          refine ⟨2376421444470231800832919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3168561925960309067777225 2376421444470231800832919)
          ·
            refine ⟨3564632166705347701249379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376421444470231800832919 3564632166705347701249379)
            ·
              refine ⟨5346948250058021551874069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564632166705347701249379 5346948250058021551874069)
              ·
                refine ⟨250638199221469760244097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5346948250058021551874069 250638199221469760244097)
                ·
                  refine ⟨187978649416102320183073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250638199221469760244097 187978649416102320183073)
                  ·
                    refine ⟨140983987062076740137305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187978649416102320183073 140983987062076740137305)
                    ·
                      refine ⟨105737990296557555102979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 140983987062076740137305 105737990296557555102979)
                      ·
                        rfl

theorem cell23_205924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_205924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_205924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_205924 prefixEnd_205924 := by exact prefixLift 205924
  have htrace : WordTrace (prefixWord ++ tailWord_205924) baseStart_205924 baseEnd_205924 := by
    simpa [prefixWord, tailWord_205924, baseEnd_205924] using wordTrace_append hprefix tailTrace_205924
  have hstable : (prefixWord ++ tailWord_205924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205924).length < 2 ^ (prefixWord ++ tailWord_205924).sum := by decide
  have hdescent : baseEnd_205924 < baseStart_205924 := by decide
  rcases family_descends (prefixWord ++ tailWord_205924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206000 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3]
def baseStart_206000 : Nat := 118140960795 + 206000 * 2 ^ 59
def prefixEnd_206000 : Nat := 4983230072969 + 3 ^ 40 * 206000 * 2
def baseEnd_206000 : Nat := 105777014826299257752629

theorem tailTrace_206000 : CollatzResearch.WordTrace tailWord_206000 prefixEnd_206000 105777014826299257752629 := by
  unfold tailWord_206000
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756718626852328422063727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5008958169136437896084969 3756718626852328422063727)
  ·
    refine ⟨5635077940278492633095591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3756718626852328422063727 5635077940278492633095591)
    ·
      refine ⟨8452616910417738949643387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5635077940278492633095591 8452616910417738949643387)
      ·
        refine ⟨12678925365626608424465081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8452616910417738949643387 12678925365626608424465081)
        ·
          refine ⟨9509194024219956318348811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12678925365626608424465081 9509194024219956318348811)
          ·
            refine ⟨14263791036329934477523217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9509194024219956318348811 14263791036329934477523217)
            ·
              refine ⟨10697843277247450858142413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14263791036329934477523217 10697843277247450858142413)
              ·
                refine ⟨4011691228967794071803405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10697843277247450858142413 4011691228967794071803405)
                ·
                  refine ⟨1504384210862922776926277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4011691228967794071803405 1504384210862922776926277)
                  ·
                    refine ⟨282072039536798020673677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1504384210862922776926277 282072039536798020673677)
                    ·
                      refine ⟨105777014826299257752629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 282072039536798020673677 105777014826299257752629)
                      ·
                        rfl

theorem cell23_206000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_206000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206000 prefixEnd_206000 := by exact prefixLift 206000
  have htrace : WordTrace (prefixWord ++ tailWord_206000) baseStart_206000 baseEnd_206000 := by
    simpa [prefixWord, tailWord_206000, baseEnd_206000] using wordTrace_append hprefix tailTrace_206000
  have hstable : (prefixWord ++ tailWord_206000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206000).length < 2 ^ (prefixWord ++ tailWord_206000).sum := by decide
  have hdescent : baseEnd_206000 < baseStart_206000 := by decide
  rcases family_descends (prefixWord ++ tailWord_206000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206007 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 3, 4]
def baseStart_206007 : Nat := 118140960795 + 206007 * 2 ^ 59
def prefixEnd_206007 : Nat := 4983230072969 + 3 ^ 40 * 206007 * 2
def baseEnd_206007 : Nat := 35260203063626910121699

theorem tailTrace_206007 : CollatzResearch.WordTrace tailWord_206007 prefixEnd_206007 35260203063626910121699 := by
  unfold tailWord_206007
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513692564679297039632275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5009128376452864693088183 7513692564679297039632275)
  ·
    refine ⟨11270538847018945559448413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7513692564679297039632275 11270538847018945559448413)
    ·
      refine ⟨4226452067632104584793155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11270538847018945559448413 4226452067632104584793155)
      ·
        refine ⟨6339678101448156877189733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226452067632104584793155 6339678101448156877189733)
        ·
          refine ⟨1188689644021529414473075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6339678101448156877189733 1188689644021529414473075)
          ·
            refine ⟨1783034466032294121709613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188689644021529414473075 1783034466032294121709613)
            ·
              refine ⟨668637924762110295641105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1783034466032294121709613 668637924762110295641105)
              ·
                refine ⟨501478443571582721730829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668637924762110295641105 501478443571582721730829)
                ·
                  refine ⟨188054416339343520649061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501478443571582721730829 188054416339343520649061)
                  ·
                    refine ⟨35260203063626910121699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188054416339343520649061 35260203063626910121699)
                    ·
                      rfl

theorem cell23_206007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_206007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206007 prefixEnd_206007 := by exact prefixLift 206007
  have htrace : WordTrace (prefixWord ++ tailWord_206007) baseStart_206007 baseEnd_206007 := by
    simpa [prefixWord, tailWord_206007, baseEnd_206007] using wordTrace_append hprefix tailTrace_206007
  have hstable : (prefixWord ++ tailWord_206007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206007).length < 2 ^ (prefixWord ++ tailWord_206007).sum := by decide
  have hdescent : baseEnd_206007 < baseStart_206007 := by decide
  rcases family_descends (prefixWord ++ tailWord_206007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206014 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_206014 : Nat := 118140960795 + 206014 * 2 ^ 59
def prefixEnd_206014 : Nat := 4983230072969 + 3 ^ 40 * 206014 * 2
def baseEnd_206014 : Nat := 105784203555462202977565

theorem tailTrace_206014 : CollatzResearch.WordTrace tailWord_206014 prefixEnd_206014 105784203555462202977565 := by
  unfold tailWord_206014
  simp only [CollatzResearch.WordTrace]
  refine ⟨939243484456742154392137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5009298583769291490091397 939243484456742154392137)
  ·
    refine ⟨704432613342556615794103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 939243484456742154392137 704432613342556615794103)
    ·
      refine ⟨1056648920013834923691155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704432613342556615794103 1056648920013834923691155)
      ·
        refine ⟨1584973380020752385536733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056648920013834923691155 1584973380020752385536733)
        ·
          refine ⟨594365017507782144576275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1584973380020752385536733 594365017507782144576275)
          ·
            refine ⟨891547526261673216864413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594365017507782144576275 891547526261673216864413)
            ·
              refine ⟨334330322348127456324155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891547526261673216864413 334330322348127456324155)
              ·
                refine ⟨501495483522191184486233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334330322348127456324155 501495483522191184486233)
                ·
                  refine ⟨376121612641643388364675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501495483522191184486233 376121612641643388364675)
                  ·
                    refine ⟨564182418962465082547013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 376121612641643388364675 564182418962465082547013)
                    ·
                      refine ⟨105784203555462202977565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 564182418962465082547013 105784203555462202977565)
                      ·
                        rfl

theorem cell23_206014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_206014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206014 prefixEnd_206014 := by exact prefixLift 206014
  have htrace : WordTrace (prefixWord ++ tailWord_206014) baseStart_206014 baseEnd_206014 := by
    simpa [prefixWord, tailWord_206014, baseEnd_206014] using wordTrace_append hprefix tailTrace_206014
  have hstable : (prefixWord ++ tailWord_206014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206014).length < 2 ^ (prefixWord ++ tailWord_206014).sum := by decide
  have hdescent : baseEnd_206014 < baseStart_206014 := by decide
  rcases family_descends (prefixWord ++ tailWord_206014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206024 : List Nat := [2, 1, 3, 1, 2, 1, 3, 5, 1, 4]
def baseStart_206024 : Nat := 118140960795 + 206024 * 2 ^ 59
def prefixEnd_206024 : Nat := 4983230072969 + 3 ^ 40 * 206024 * 2
def baseEnd_206024 : Nat := 35263112787335721284173

theorem tailTrace_206024 : CollatzResearch.WordTrace tailWord_206024 prefixEnd_206024 35263112787335721284173 := by
  unfold tailWord_206024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3757156302808854471500563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5009541737078472628667417 3757156302808854471500563)
  ·
    refine ⟨5635734454213281707250845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3757156302808854471500563 5635734454213281707250845)
    ·
      refine ⟨2113400420329980640219067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5635734454213281707250845 2113400420329980640219067)
      ·
        refine ⟨3170100630494970960328601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113400420329980640219067 3170100630494970960328601)
        ·
          refine ⟨2377575472871228220246451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3170100630494970960328601 2377575472871228220246451)
          ·
            refine ⟨3566363209306842330369677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377575472871228220246451 3566363209306842330369677)
            ·
              refine ⟨1337386203490065873888629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3566363209306842330369677 1337386203490065873888629)
              ·
                refine ⟨125379956577193675677059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1337386203490065873888629 125379956577193675677059)
                ·
                  refine ⟨188069934865790513515589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125379956577193675677059 188069934865790513515589)
                  ·
                    refine ⟨35263112787335721284173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188069934865790513515589 35263112787335721284173)
                    ·
                      rfl

theorem cell23_206024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_206024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206024 prefixEnd_206024 := by exact prefixLift 206024
  have htrace : WordTrace (prefixWord ++ tailWord_206024) baseStart_206024 baseEnd_206024 := by
    simpa [prefixWord, tailWord_206024, baseEnd_206024] using wordTrace_append hprefix tailTrace_206024
  have hstable : (prefixWord ++ tailWord_206024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206024).length < 2 ^ (prefixWord ++ tailWord_206024).sum := by decide
  have hdescent : baseEnd_206024 < baseStart_206024 := by decide
  rcases family_descends (prefixWord ++ tailWord_206024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206037 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 8]
def baseStart_206037 : Nat := 118140960795 + 206037 * 2 ^ 59
def prefixEnd_206037 : Nat := 4983230072969 + 3 ^ 40 * 206037 * 2
def baseEnd_206037 : Nat := 11755112623390623665551

theorem tailTrace_206037 : CollatzResearch.WordTrace tailWord_206037 prefixEnd_206037 11755112623390623665551 := by
  unfold tailWord_206037
  simp only [CollatzResearch.WordTrace]
  refine ⟨7514786754570612163224365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5009857836380408108816243 7514786754570612163224365)
  ·
    refine ⟨2818045032963979561209137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7514786754570612163224365 2818045032963979561209137)
    ·
      refine ⟨2113533774722984670906853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2818045032963979561209137 2113533774722984670906853)
      ·
        refine ⟨396287582760559625795035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2113533774722984670906853 396287582760559625795035)
        ·
          refine ⟨594431374140839438692553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396287582760559625795035 594431374140839438692553)
          ·
            refine ⟨445823530605629579019415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594431374140839438692553 445823530605629579019415)
            ·
              refine ⟨668735295908444368529123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445823530605629579019415 668735295908444368529123)
              ·
                refine ⟨1003102943862666552793685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668735295908444368529123 1003102943862666552793685)
                ·
                  refine ⟨11755112623390623665551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1003102943862666552793685 11755112623390623665551)
                  ·
                    rfl

theorem cell23_206037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_206037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206037 prefixEnd_206037 := by exact prefixLift 206037
  have htrace : WordTrace (prefixWord ++ tailWord_206037) baseStart_206037 baseEnd_206037 := by
    simpa [prefixWord, tailWord_206037, baseEnd_206037] using wordTrace_append hprefix tailTrace_206037
  have hstable : (prefixWord ++ tailWord_206037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206037).length < 2 ^ (prefixWord ++ tailWord_206037).sum := by decide
  have hdescent : baseEnd_206037 < baseStart_206037 := by decide
  rcases family_descends (prefixWord ++ tailWord_206037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206067 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 1, 5]
def baseStart_206067 : Nat := 118140960795 + 206067 * 2 ^ 59
def prefixEnd_206067 : Nat := 4983230072969 + 3 ^ 40 * 206067 * 2
def baseEnd_206067 : Nat := 35270472676716831871607

theorem tailTrace_206067 : CollatzResearch.WordTrace tailWord_206067 prefixEnd_206067 35270472676716831871607 := by
  unfold tailWord_206067
  simp only [CollatzResearch.WordTrace]
  refine ⟨7515880944461927286816455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5010587296307951524544303 7515880944461927286816455)
  ·
    refine ⟨11273821416692890930224683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7515880944461927286816455 11273821416692890930224683)
    ·
      refine ⟨16910732125039336395337025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11273821416692890930224683 16910732125039336395337025)
      ·
        refine ⟨12683049093779502296502769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16910732125039336395337025 12683049093779502296502769)
        ·
          refine ⟨9512286820334626722377077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12683049093779502296502769 9512286820334626722377077)
          ·
            refine ⟨891776889406371255222851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9512286820334626722377077 891776889406371255222851)
            ·
              refine ⟨1337665334109556882834277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891776889406371255222851 1337665334109556882834277)
              ·
                refine ⟨250812250145541915531427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1337665334109556882834277 250812250145541915531427)
                ·
                  refine ⟨376218375218312873297141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250812250145541915531427 376218375218312873297141)
                  ·
                    refine ⟨35270472676716831871607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 376218375218312873297141 35270472676716831871607)
                    ·
                      rfl

theorem cell23_206067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 5].length) (baseStart_206067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206067 prefixEnd_206067 := by exact prefixLift 206067
  have htrace : WordTrace (prefixWord ++ tailWord_206067) baseStart_206067 baseEnd_206067 := by
    simpa [prefixWord, tailWord_206067, baseEnd_206067] using wordTrace_append hprefix tailTrace_206067
  have hstable : (prefixWord ++ tailWord_206067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206067).length < 2 ^ (prefixWord ++ tailWord_206067).sum := by decide
  have hdescent : baseEnd_206067 < baseStart_206067 := by decide
  rcases family_descends (prefixWord ++ tailWord_206067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206074 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2]
def baseStart_206074 : Nat := 118140960795 + 206074 * 2 ^ 59
def prefixEnd_206074 : Nat := 4983230072969 + 3 ^ 40 * 206074 * 2
def baseEnd_206074 : Nat := 105815012394731968227289

theorem tailTrace_206074 : CollatzResearch.WordTrace tailWord_206074 prefixEnd_206074 105815012394731968227289 := by
  unfold tailWord_206074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879034063859141870580319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5010757503624378321547517 1879034063859141870580319)
  ·
    refine ⟨2818551095788712805870479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1879034063859141870580319 2818551095788712805870479)
    ·
      refine ⟨4227826643683069208805719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2818551095788712805870479 4227826643683069208805719)
      ·
        refine ⟨6341739965524603813208579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227826643683069208805719 6341739965524603813208579)
        ·
          refine ⟨9512609948286905719812869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341739965524603813208579 9512609948286905719812869)
          ·
            refine ⟨1783614365303794822464913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9512609948286905719812869 1783614365303794822464913)
            ·
              refine ⟨1337710773977846116848685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783614365303794822464913 1337710773977846116848685)
              ·
                refine ⟨501641540241692293818257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1337710773977846116848685 501641540241692293818257)
                ·
                  refine ⟨376231155181269220363693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501641540241692293818257 376231155181269220363693)
                  ·
                    refine ⟨141086683192975957636385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376231155181269220363693 141086683192975957636385)
                    ·
                      refine ⟨105815012394731968227289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141086683192975957636385 105815012394731968227289)
                      ·
                        rfl

theorem cell23_206074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_206074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206074 prefixEnd_206074 := by exact prefixLift 206074
  have htrace : WordTrace (prefixWord ++ tailWord_206074) baseStart_206074 baseEnd_206074 := by
    simpa [prefixWord, tailWord_206074, baseEnd_206074] using wordTrace_append hprefix tailTrace_206074
  have hstable : (prefixWord ++ tailWord_206074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206074).length < 2 ^ (prefixWord ++ tailWord_206074).sum := by decide
  have hdescent : baseEnd_206074 < baseStart_206074 := by decide
  rcases family_descends (prefixWord ++ tailWord_206074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206080 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 3, 6]
def baseStart_206080 : Nat := 118140960795 + 206080 * 2 ^ 59
def prefixEnd_206080 : Nat := 4983230072969 + 3 ^ 40 * 206080 * 2
def baseEnd_206080 : Nat := 35272697759552981584087

theorem tailTrace_206080 : CollatzResearch.WordTrace tailWord_206080 prefixEnd_206080 35272697759552981584087 := by
  unfold tailWord_206080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758177546707415253519847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5010903395609887004693129 3758177546707415253519847)
  ·
    refine ⟨5637266320061122880279771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3758177546707415253519847 5637266320061122880279771)
    ·
      refine ⟨8455899480091684320419657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5637266320061122880279771 8455899480091684320419657)
      ·
        refine ⟨6341924610068763240314743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8455899480091684320419657 6341924610068763240314743)
        ·
          refine ⟨9512886915103144860472115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341924610068763240314743 9512886915103144860472115)
          ·
            refine ⟨14269330372654717290708173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512886915103144860472115 14269330372654717290708173)
            ·
              refine ⟨5350998889745518984015565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14269330372654717290708173 5350998889745518984015565)
              ·
                refine ⟨2006624583654569619005837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5350998889745518984015565 2006624583654569619005837)
                ·
                  refine ⟨752484218870463607127189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2006624583654569619005837 752484218870463607127189)
                  ·
                    refine ⟨35272697759552981584087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 752484218870463607127189 35272697759552981584087)
                    ·
                      rfl

theorem cell23_206080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_206080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206080 prefixEnd_206080 := by exact prefixLift 206080
  have htrace : WordTrace (prefixWord ++ tailWord_206080) baseStart_206080 baseEnd_206080 := by
    simpa [prefixWord, tailWord_206080, baseEnd_206080] using wordTrace_append hprefix tailTrace_206080
  have hstable : (prefixWord ++ tailWord_206080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206080).length < 2 ^ (prefixWord ++ tailWord_206080).sum := by decide
  have hdescent : baseEnd_206080 < baseStart_206080 := by decide
  rcases family_descends (prefixWord ++ tailWord_206080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206084 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_206084 : Nat := 118140960795 + 206084 * 2 ^ 59
def prefixEnd_206084 : Nat := 4983230072969 + 3 ^ 40 * 206084 * 2
def baseEnd_206084 : Nat := 35273382400425643034081

theorem tailTrace_206084 : CollatzResearch.WordTrace tailWord_206084 prefixEnd_206084 35273382400425643034081 := by
  unfold tailWord_206084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758250492700169595092653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5011000656933559460123537 3758250492700169595092653)
  ·
    refine ⟨1409343934762563598159745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3758250492700169595092653 1409343934762563598159745)
    ·
      refine ⟨1057007951071922698619809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1409343934762563598159745 1057007951071922698619809)
      ·
        refine ⟨792755963303942023964857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1057007951071922698619809 792755963303942023964857)
        ·
          refine ⟨594566972477956517973643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792755963303942023964857 594566972477956517973643)
          ·
            refine ⟨891850458716934776960465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594566972477956517973643 891850458716934776960465)
            ·
              refine ⟨668887844037701082720349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891850458716934776960465 668887844037701082720349)
              ·
                refine ⟨250832941514137906020131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 668887844037701082720349 250832941514137906020131)
                ·
                  refine ⟨376249412271206859030197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250832941514137906020131 376249412271206859030197)
                  ·
                    refine ⟨35273382400425643034081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 376249412271206859030197 35273382400425643034081)
                    ·
                      rfl

theorem cell23_206084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_206084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206084 prefixEnd_206084 := by exact prefixLift 206084
  have htrace : WordTrace (prefixWord ++ tailWord_206084) baseStart_206084 baseEnd_206084 := by
    simpa [prefixWord, tailWord_206084, baseEnd_206084] using wordTrace_append hprefix tailTrace_206084
  have hstable : (prefixWord ++ tailWord_206084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206084).length < 2 ^ (prefixWord ++ tailWord_206084).sum := by decide
  have hdescent : baseEnd_206084 < baseStart_206084 := by decide
  rcases family_descends (prefixWord ++ tailWord_206084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206097 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 4, 4]
def baseStart_206097 : Nat := 118140960795 + 206097 * 2 ^ 59
def prefixEnd_206097 : Nat := 4983230072969 + 3 ^ 40 * 206097 * 2
def baseEnd_206097 : Nat := 35275607483261792746561

theorem tailTrace_206097 : CollatzResearch.WordTrace tailWord_206097 prefixEnd_206097 35275607483261792746561 := by
  unfold tailWord_206097
  simp only [CollatzResearch.WordTrace]
  refine ⟨7516975134353242410408545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5011316756235494940272363 7516975134353242410408545)
  ·
    refine ⟨5637731350764931807806409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7516975134353242410408545 5637731350764931807806409)
    ·
      refine ⟨4228298513073698855854807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5637731350764931807806409 4228298513073698855854807)
      ·
        refine ⟨6342447769610548283782211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228298513073698855854807 6342447769610548283782211)
        ·
          refine ⟨9513671654415822425673317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342447769610548283782211 9513671654415822425673317)
          ·
            refine ⟨1783813435202966704813747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9513671654415822425673317 1783813435202966704813747)
            ·
              refine ⟨2675720152804450057220621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783813435202966704813747 2675720152804450057220621)
              ·
                refine ⟨1003395057301668771457733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2675720152804450057220621 1003395057301668771457733)
                ·
                  refine ⟨188136573244062894648325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003395057301668771457733 188136573244062894648325)
                  ·
                    refine ⟨35275607483261792746561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188136573244062894648325 35275607483261792746561)
                    ·
                      rfl

theorem cell23_206097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_206097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206097 prefixEnd_206097 := by exact prefixLift 206097
  have htrace : WordTrace (prefixWord ++ tailWord_206097) baseStart_206097 baseEnd_206097 := by
    simpa [prefixWord, tailWord_206097, baseEnd_206097] using wordTrace_append hprefix tailTrace_206097
  have hstable : (prefixWord ++ tailWord_206097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206097).length < 2 ^ (prefixWord ++ tailWord_206097).sum := by decide
  have hdescent : baseEnd_206097 < baseStart_206097 := by decide
  rcases family_descends (prefixWord ++ tailWord_206097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206107 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 3]
def baseStart_206107 : Nat := 118140960795 + 206107 * 2 ^ 59
def prefixEnd_206107 : Nat := 4983230072969 + 3 ^ 40 * 206107 * 2
def baseEnd_206107 : Nat := 105831957256330339114637

theorem tailTrace_206107 : CollatzResearch.WordTrace tailWord_206107 prefixEnd_206107 105831957256330339114637 := by
  unfold tailWord_206107
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517339864317014118272575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5011559909544676078848383 7517339864317014118272575)
  ·
    refine ⟨11276009796475521177408863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7517339864317014118272575 11276009796475521177408863)
    ·
      refine ⟨16914014694713281766113295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11276009796475521177408863 16914014694713281766113295)
      ·
        refine ⟨25371022042069922649169943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16914014694713281766113295 25371022042069922649169943)
        ·
          refine ⟨38056533063104883973754915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25371022042069922649169943 38056533063104883973754915)
          ·
            refine ⟨57084799594657325960632373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38056533063104883973754915 57084799594657325960632373)
            ·
              refine ⟨5351699961999124308809285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57084799594657325960632373 5351699961999124308809285)
              ·
                refine ⟨1003443742874835807901741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5351699961999124308809285 1003443742874835807901741)
                ·
                  refine ⟨376291403578063427963153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003443742874835807901741 376291403578063427963153)
                  ·
                    refine ⟨282218552683547570972365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 376291403578063427963153 282218552683547570972365)
                    ·
                      refine ⟨105831957256330339114637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 282218552683547570972365 105831957256330339114637)
                      ·
                        rfl

theorem cell23_206107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 3].length) (baseStart_206107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206107 prefixEnd_206107 := by exact prefixLift 206107
  have htrace : WordTrace (prefixWord ++ tailWord_206107) baseStart_206107 baseEnd_206107 := by
    simpa [prefixWord, tailWord_206107, baseEnd_206107] using wordTrace_append hprefix tailTrace_206107
  have hstable : (prefixWord ++ tailWord_206107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206107).length < 2 ^ (prefixWord ++ tailWord_206107).sum := by decide
  have hdescent : baseEnd_206107 < baseStart_206107 := by decide
  rcases family_descends (prefixWord ++ tailWord_206107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206117 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_206117 : Nat := 118140960795 + 206117 * 2 ^ 59
def prefixEnd_206117 : Nat := 4983230072969 + 3 ^ 40 * 206117 * 2
def baseEnd_206117 : Nat := 105837092062875299989591

theorem tailTrace_206117 : CollatzResearch.WordTrace tailWord_206117 prefixEnd_206117 105837092062875299989591 := by
  unfold tailWord_206117
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517704594280785826136605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5011803062853857217424403 7517704594280785826136605)
  ·
    refine ⟨2819139222855294684801227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7517704594280785826136605 2819139222855294684801227)
    ·
      refine ⟨4228708834282942027201841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819139222855294684801227 4228708834282942027201841)
      ·
        refine ⟨3171531625712206520401381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4228708834282942027201841 3171531625712206520401381)
        ·
          refine ⟨594662179821038722575259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3171531625712206520401381 594662179821038722575259)
          ·
            refine ⟨891993269731558083862889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594662179821038722575259 891993269731558083862889)
            ·
              refine ⟨668994952298668562897167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891993269731558083862889 668994952298668562897167)
              ·
                refine ⟨1003492428448002844345751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668994952298668562897167 1003492428448002844345751)
                ·
                  refine ⟨1505238642672004266518627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003492428448002844345751 1505238642672004266518627)
                  ·
                    refine ⟨2257857964008006399777941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1505238642672004266518627 2257857964008006399777941)
                    ·
                      refine ⟨105837092062875299989591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2257857964008006399777941 105837092062875299989591)
                      ·
                        rfl

theorem cell23_206117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_206117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206117 prefixEnd_206117 := by exact prefixLift 206117
  have htrace : WordTrace (prefixWord ++ tailWord_206117) baseStart_206117 baseEnd_206117 := by
    simpa [prefixWord, tailWord_206117, baseEnd_206117] using wordTrace_append hprefix tailTrace_206117
  have hstable : (prefixWord ++ tailWord_206117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206117).length < 2 ^ (prefixWord ++ tailWord_206117).sum := by decide
  have hdescent : baseEnd_206117 < baseStart_206117 := by decide
  rcases family_descends (prefixWord ++ tailWord_206117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206138 : List Nat := [3, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2]
def baseStart_206138 : Nat := 118140960795 + 206138 * 2 ^ 59
def prefixEnd_206138 : Nat := 4983230072969 + 3 ^ 40 * 206138 * 2
def baseEnd_206138 : Nat := 105847875156619717826995

theorem tailTrace_206138 : CollatzResearch.WordTrace tailWord_206138 prefixEnd_206138 105847875156619717826995 := by
  unfold tailWord_206138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879617631801176603162767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5012313684803137608434045 1879617631801176603162767)
  ·
    refine ⟨2819426447701764904744151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1879617631801176603162767 2819426447701764904744151)
    ·
      refine ⟨4229139671552647357116227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819426447701764904744151 4229139671552647357116227)
      ·
        refine ⟨6343709507328971035674341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229139671552647357116227 6343709507328971035674341)
        ·
          refine ⟨1189445532624182069188939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6343709507328971035674341 1189445532624182069188939)
          ·
            refine ⟨1784168298936273103783409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189445532624182069188939 1784168298936273103783409)
            ·
              refine ⟨1338126224202204827837557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784168298936273103783409 1338126224202204827837557)
              ·
                refine ⟨125449333518956702609771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1338126224202204827837557 125449333518956702609771)
                ·
                  refine ⟨188174000278435053914657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125449333518956702609771 188174000278435053914657)
                  ·
                    refine ⟨141130500208826290435993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188174000278435053914657 141130500208826290435993)
                    ·
                      refine ⟨105847875156619717826995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141130500208826290435993 105847875156619717826995)
                      ·
                        rfl

theorem cell23_206138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_206138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206138 prefixEnd_206138 := by exact prefixLift 206138
  have htrace : WordTrace (prefixWord ++ tailWord_206138) baseStart_206138 baseEnd_206138 := by
    simpa [prefixWord, tailWord_206138, baseEnd_206138] using wordTrace_append hprefix tailTrace_206138
  have hstable : (prefixWord ++ tailWord_206138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206138).length < 2 ^ (prefixWord ++ tailWord_206138).sum := by decide
  have hdescent : baseEnd_206138 < baseStart_206138 := by decide
  rcases family_descends (prefixWord ++ tailWord_206138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206148 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_206148 : Nat := 118140960795 + 206148 * 2 ^ 59
def prefixEnd_206148 : Nat := 4983230072969 + 3 ^ 40 * 206148 * 2
def baseEnd_206148 : Nat := 35284336654388226233983

theorem tailTrace_206148 : CollatzResearch.WordTrace tailWord_206148 prefixEnd_206148 35284336654388226233983 := by
  unfold tailWord_206148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759417628584239060257549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5012556838112318747010065 3759417628584239060257549)
  ·
    refine ⟨1409781610719089647596581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3759417628584239060257549 1409781610719089647596581)
    ·
      refine ⟨264334052009829308924359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1409781610719089647596581 264334052009829308924359)
      ·
        refine ⟨396501078014743963386539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264334052009829308924359 396501078014743963386539)
        ·
          refine ⟨594751617022115945079809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396501078014743963386539 594751617022115945079809)
          ·
            refine ⟨446063712766586958809857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594751617022115945079809 446063712766586958809857)
            ·
              refine ⟨334547784574940219107393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446063712766586958809857 334547784574940219107393)
              ·
                refine ⟨250910838431205164330545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334547784574940219107393 250910838431205164330545)
                ·
                  refine ⟨188183128823403873247909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250910838431205164330545 188183128823403873247909)
                  ·
                    refine ⟨35284336654388226233983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188183128823403873247909 35284336654388226233983)
                    ·
                      rfl

theorem cell23_206148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_206148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206148 prefixEnd_206148 := by exact prefixLift 206148
  have htrace : WordTrace (prefixWord ++ tailWord_206148) baseStart_206148 baseEnd_206148 := by
    simpa [prefixWord, tailWord_206148, baseEnd_206148] using wordTrace_append hprefix tailTrace_206148
  have hstable : (prefixWord ++ tailWord_206148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206148).length < 2 ^ (prefixWord ++ tailWord_206148).sum := by decide
  have hdescent : baseEnd_206148 < baseStart_206148 := by decide
  rcases family_descends (prefixWord ++ tailWord_206148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206154 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_206154 : Nat := 118140960795 + 206154 * 2 ^ 59
def prefixEnd_206154 : Nat := 4983230072969 + 3 ^ 40 * 206154 * 2
def baseEnd_206154 : Nat := 105856090847091655226921

theorem tailTrace_206154 : CollatzResearch.WordTrace tailWord_206154 prefixEnd_206154 105856090847091655226921 := by
  unfold tailWord_206154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879763523786685286308379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5012702730097827430155677 1879763523786685286308379)
  ·
    refine ⟨2819645285680027929462569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1879763523786685286308379 2819645285680027929462569)
    ·
      refine ⟨2114733964260020947096927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2819645285680027929462569 2114733964260020947096927)
      ·
        refine ⟨3172100946390031420645391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114733964260020947096927 3172100946390031420645391)
        ·
          refine ⟨4758151419585047130968087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172100946390031420645391 4758151419585047130968087)
          ·
            refine ⟨7137227129377570696452131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758151419585047130968087 7137227129377570696452131)
            ·
              refine ⟨10705840694066356044678197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137227129377570696452131 10705840694066356044678197)
              ·
                refine ⟨1003672565068720879188581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10705840694066356044678197 1003672565068720879188581)
                ·
                  refine ⟨188188605950385164847859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003672565068720879188581 188188605950385164847859)
                  ·
                    refine ⟨282282908925577747271789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188188605950385164847859 282282908925577747271789)
                    ·
                      refine ⟨105856090847091655226921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 282282908925577747271789 105856090847091655226921)
                      ·
                        rfl

theorem cell23_206154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_206154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206154 prefixEnd_206154 := by exact prefixLift 206154
  have htrace : WordTrace (prefixWord ++ tailWord_206154) baseStart_206154 baseEnd_206154 := by
    simpa [prefixWord, tailWord_206154, baseEnd_206154] using wordTrace_append hprefix tailTrace_206154
  have hstable : (prefixWord ++ tailWord_206154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206154).length < 2 ^ (prefixWord ++ tailWord_206154).sum := by decide
  have hdescent : baseEnd_206154 < baseStart_206154 := by decide
  rcases family_descends (prefixWord ++ tailWord_206154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206181 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 1, 3, 2]
def baseStart_206181 : Nat := 118140960795 + 206181 * 2 ^ 59
def prefixEnd_206181 : Nat := 4983230072969 + 3 ^ 40 * 206181 * 2
def baseEnd_206181 : Nat := 105869954824763049589297

theorem tailTrace_206181 : CollatzResearch.WordTrace tailWord_206181 prefixEnd_206181 105869954824763049589297 := by
  unfold tailWord_206181
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520038866048924756466397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5013359244032616504310931 7520038866048924756466397)
  ·
    refine ⟨2820014574768346783674899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7520038866048924756466397 2820014574768346783674899)
    ·
      refine ⟨4230021862152520175512349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820014574768346783674899 4230021862152520175512349)
      ·
        refine ⟨1586258198307195065817131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4230021862152520175512349 1586258198307195065817131)
        ·
          refine ⟨2379387297460792598725697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586258198307195065817131 2379387297460792598725697)
          ·
            refine ⟨1784540473095594449044273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379387297460792598725697 1784540473095594449044273)
            ·
              refine ⟨1338405354821695836783205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784540473095594449044273 1338405354821695836783205)
              ·
                refine ⟨250951004029067969396851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1338405354821695836783205 250951004029067969396851)
                ·
                  refine ⟨376426506043601954095277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250951004029067969396851 376426506043601954095277)
                  ·
                    refine ⟨141159939766350732785729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376426506043601954095277 141159939766350732785729)
                    ·
                      refine ⟨105869954824763049589297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141159939766350732785729 105869954824763049589297)
                      ·
                        rfl

theorem cell23_206181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_206181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206181 prefixEnd_206181 := by exact prefixLift 206181
  have htrace : WordTrace (prefixWord ++ tailWord_206181) baseStart_206181 baseEnd_206181 := by
    simpa [prefixWord, tailWord_206181, baseEnd_206181] using wordTrace_append hprefix tailTrace_206181
  have hstable : (prefixWord ++ tailWord_206181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206181).length < 2 ^ (prefixWord ++ tailWord_206181).sum := by decide
  have hdescent : baseEnd_206181 < baseStart_206181 := by decide
  rcases family_descends (prefixWord ++ tailWord_206181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206228 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_206228 : Nat := 118140960795 + 206228 * 2 ^ 59
def prefixEnd_206228 : Nat := 4983230072969 + 3 ^ 40 * 206228 * 2
def baseEnd_206228 : Nat := 105894088415524365701581

theorem tailTrace_206228 : CollatzResearch.WordTrace tailWord_206228 prefixEnd_206228 105894088415524365701581 := by
  unfold tailWord_206228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760876548439325891713669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5014502064585767855618225 3760876548439325891713669)
  ·
    refine ⟨705164352832373604696313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3760876548439325891713669 705164352832373604696313)
    ·
      refine ⟨528873264624280203522235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 705164352832373604696313 528873264624280203522235)
      ·
        refine ⟨793309896936420305283353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528873264624280203522235 793309896936420305283353)
        ·
          refine ⟨594982422702315228962515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793309896936420305283353 594982422702315228962515)
          ·
            refine ⟨892473634053472843443773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594982422702315228962515 892473634053472843443773)
            ·
              refine ⟨334677612770052316291415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 892473634053472843443773 334677612770052316291415)
              ·
                refine ⟨502016419155078474437123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334677612770052316291415 502016419155078474437123)
                ·
                  refine ⟨753024628732617711655685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502016419155078474437123 753024628732617711655685)
                  ·
                    refine ⟨141192117887365820935441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753024628732617711655685 141192117887365820935441)
                    ·
                      refine ⟨105894088415524365701581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141192117887365820935441 105894088415524365701581)
                      ·
                        rfl

theorem cell23_206228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_206228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206228 prefixEnd_206228 := by exact prefixLift 206228
  have htrace : WordTrace (prefixWord ++ tailWord_206228) baseStart_206228 baseEnd_206228 := by
    simpa [prefixWord, tailWord_206228, baseEnd_206228] using wordTrace_append hprefix tailTrace_206228
  have hstable : (prefixWord ++ tailWord_206228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206228).length < 2 ^ (prefixWord ++ tailWord_206228).sum := by decide
  have hdescent : baseEnd_206228 < baseStart_206228 := by decide
  rcases family_descends (prefixWord ++ tailWord_206228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206268 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 7]
def baseStart_206268 : Nat := 118140960795 + 206268 * 2 ^ 59
def prefixEnd_206268 : Nat := 4983230072969 + 3 ^ 40 * 206268 * 2
def baseEnd_206268 : Nat := 11768291960189356577933

theorem tailTrace_206268 : CollatzResearch.WordTrace tailWord_206268 prefixEnd_206268 11768291960189356577933 := by
  unfold tailWord_206268
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761606008366869307441729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5015474677822492409922305 3761606008366869307441729)
  ·
    refine ⟨2821204506275151980581297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3761606008366869307441729 2821204506275151980581297)
    ·
      refine ⟨2115903379706363985435973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2821204506275151980581297 2115903379706363985435973)
      ·
        refine ⟨396731883694943247269245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2115903379706363985435973 396731883694943247269245)
        ·
          refine ⟨148774456385603717725967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396731883694943247269245 148774456385603717725967)
          ·
            refine ⟨223161684578405576588951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148774456385603717725967 223161684578405576588951)
            ·
              refine ⟨334742526867608364883427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223161684578405576588951 334742526867608364883427)
              ·
                refine ⟨502113790301412547325141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334742526867608364883427 502113790301412547325141)
                ·
                  refine ⟨11768291960189356577933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 502113790301412547325141 11768291960189356577933)
                  ·
                    rfl

theorem cell23_206268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_206268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206268 prefixEnd_206268 := by exact prefixLift 206268
  have htrace : WordTrace (prefixWord ++ tailWord_206268) baseStart_206268 baseEnd_206268 := by
    simpa [prefixWord, tailWord_206268, baseEnd_206268] using wordTrace_append hprefix tailTrace_206268
  have hstable : (prefixWord ++ tailWord_206268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206268).length < 2 ^ (prefixWord ++ tailWord_206268).sum := by decide
  have hdescent : baseEnd_206268 < baseStart_206268 := by decide
  rcases family_descends (prefixWord ++ tailWord_206268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206301 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_206301 : Nat := 118140960795 + 206301 * 2 ^ 59
def prefixEnd_206301 : Nat := 4983230072969 + 3 ^ 40 * 206301 * 2
def baseEnd_206301 : Nat := 105931572503302580088745

theorem tailTrace_206301 : CollatzResearch.WordTrace tailWord_206301 prefixEnd_206301 105931572503302580088745 := by
  unfold tailWord_206301
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524415625614185250834757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5016277083742790167223171 7524415625614185250834757)
  ·
    refine ⟨1410827929802659734531517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7524415625614185250834757 1410827929802659734531517)
    ·
      refine ⟨529060473675997400449319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1410827929802659734531517 529060473675997400449319)
      ·
        refine ⟨793590710513996100673979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529060473675997400449319 793590710513996100673979)
        ·
          refine ⟨1190386065770994151010969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793590710513996100673979 1190386065770994151010969)
          ·
            refine ⟨892789549328245613258227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190386065770994151010969 892789549328245613258227)
            ·
              refine ⟨1339184323992368419887341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892789549328245613258227 1339184323992368419887341)
              ·
                refine ⟨502194121497138157457753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1339184323992368419887341 502194121497138157457753)
                ·
                  refine ⟨376645591122853618093315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502194121497138157457753 376645591122853618093315)
                  ·
                    refine ⟨564968386684280427139973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 376645591122853618093315 564968386684280427139973)
                    ·
                      refine ⟨105931572503302580088745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 564968386684280427139973 105931572503302580088745)
                      ·
                        rfl

theorem cell23_206301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_206301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206301 prefixEnd_206301 := by exact prefixLift 206301
  have htrace : WordTrace (prefixWord ++ tailWord_206301) baseStart_206301 baseEnd_206301 := by
    simpa [prefixWord, tailWord_206301, baseEnd_206301] using wordTrace_append hprefix tailTrace_206301
  have hstable : (prefixWord ++ tailWord_206301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206301).length < 2 ^ (prefixWord ++ tailWord_206301).sum := by decide
  have hdescent : baseEnd_206301 < baseStart_206301 := by decide
  rcases family_descends (prefixWord ++ tailWord_206301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206321 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_206321 : Nat := 118140960795 + 206321 * 2 ^ 59
def prefixEnd_206321 : Nat := 4983230072969 + 3 ^ 40 * 206321 * 2
def baseEnd_206321 : Nat := 105941842116392501838653

theorem tailTrace_206321 : CollatzResearch.WordTrace tailWord_206321 prefixEnd_206321 105941842116392501838653 := by
  unfold tailWord_206321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525145085541728666562817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5016763390361152444375211 7525145085541728666562817)
  ·
    refine ⟨5643858814156296499922113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7525145085541728666562817 5643858814156296499922113)
    ·
      refine ⟨4232894110617222374941585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5643858814156296499922113 4232894110617222374941585)
      ·
        refine ⟨3174670582962916781206189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4232894110617222374941585 3174670582962916781206189)
        ·
          refine ⟨1190501468611093792952321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3174670582962916781206189 1190501468611093792952321)
          ·
            refine ⟨892876101458320344714241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190501468611093792952321 892876101458320344714241)
            ·
              refine ⟨669657076093740258535681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892876101458320344714241 669657076093740258535681)
              ·
                refine ⟨502242807070305193901761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669657076093740258535681 502242807070305193901761)
                ·
                  refine ⟨376682105302728895426321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502242807070305193901761 376682105302728895426321)
                  ·
                    refine ⟨282511578977046671569741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 376682105302728895426321 282511578977046671569741)
                    ·
                      refine ⟨105941842116392501838653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 282511578977046671569741 105941842116392501838653)
                      ·
                        rfl

theorem cell23_206321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_206321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206321 prefixEnd_206321 := by exact prefixLift 206321
  have htrace : WordTrace (prefixWord ++ tailWord_206321) baseStart_206321 baseEnd_206321 := by
    simpa [prefixWord, tailWord_206321, baseEnd_206321] using wordTrace_append hprefix tailTrace_206321
  have hstable : (prefixWord ++ tailWord_206321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206321).length < 2 ^ (prefixWord ++ tailWord_206321).sum := by decide
  have hdescent : baseEnd_206321 < baseStart_206321 := by decide
  rcases family_descends (prefixWord ++ tailWord_206321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206328 : List Nat := [2, 1, 2, 1, 1, 6, 1, 4, 1, 4]
def baseStart_206328 : Nat := 118140960795 + 206328 * 2 ^ 59
def prefixEnd_206328 : Nat := 4983230072969 + 3 ^ 40 * 206328 * 2
def baseEnd_206328 : Nat := 35315145493657991483707

theorem tailTrace_206328 : CollatzResearch.WordTrace tailWord_206328 prefixEnd_206328 35315145493657991483707 := by
  unfold tailWord_206328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762700198258184431033819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5016933597677579241378425 3762700198258184431033819)
  ·
    refine ⟨5644050297387276646550729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3762700198258184431033819 5644050297387276646550729)
    ·
      refine ⟨4233037723040457484913047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5644050297387276646550729 4233037723040457484913047)
      ·
        refine ⟨6349556584560686227369571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233037723040457484913047 6349556584560686227369571)
        ·
          refine ⟨9524334876841029341054357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6349556584560686227369571 9524334876841029341054357)
          ·
            refine ⟨446453197351923250361923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9524334876841029341054357 446453197351923250361923)
            ·
              refine ⟨669679796027884875542885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446453197351923250361923 669679796027884875542885)
              ·
                refine ⟨125564961755228414164291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669679796027884875542885 125564961755228414164291)
                ·
                  refine ⟨188347442632842621246437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125564961755228414164291 188347442632842621246437)
                  ·
                    refine ⟨35315145493657991483707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188347442632842621246437 35315145493657991483707)
                    ·
                      rfl

theorem cell23_206328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_206328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206328 prefixEnd_206328 := by exact prefixLift 206328
  have htrace : WordTrace (prefixWord ++ tailWord_206328) baseStart_206328 baseEnd_206328 := by
    simpa [prefixWord, tailWord_206328, baseEnd_206328] using wordTrace_append hprefix tailTrace_206328
  have hstable : (prefixWord ++ tailWord_206328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206328).length < 2 ^ (prefixWord ++ tailWord_206328).sum := by decide
  have hdescent : baseEnd_206328 < baseStart_206328 := by decide
  rcases family_descends (prefixWord ++ tailWord_206328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206378 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_206378 : Nat := 118140960795 + 206378 * 2 ^ 59
def prefixEnd_206378 : Nat := 4983230072969 + 3 ^ 40 * 206378 * 2
def baseEnd_206378 : Nat := 105971110513698778825891

theorem tailTrace_206378 : CollatzResearch.WordTrace tailWord_206378 prefixEnd_206378 105971110513698778825891 := by
  unfold tailWord_206378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881806011583806850346947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5018149364223484934258525 1881806011583806850346947)
  ·
    refine ⟨2822709017375710275520421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1881806011583806850346947 2822709017375710275520421)
    ·
      refine ⟨529257940757945676660079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2822709017375710275520421 529257940757945676660079)
      ·
        refine ⟨793886911136918514990119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529257940757945676660079 793886911136918514990119)
        ·
          refine ⟨1190830366705377772485179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793886911136918514990119 1190830366705377772485179)
          ·
            refine ⟨1786245550058066658727769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190830366705377772485179 1786245550058066658727769)
            ·
              refine ⟨1339684162543549994045827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786245550058066658727769 1339684162543549994045827)
              ·
                refine ⟨2009526243815324991068741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339684162543549994045827 2009526243815324991068741)
                ·
                  refine ⟨376786170715373435825389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009526243815324991068741 376786170715373435825389)
                  ·
                    refine ⟨141294814018265038434521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376786170715373435825389 141294814018265038434521)
                    ·
                      refine ⟨105971110513698778825891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141294814018265038434521 105971110513698778825891)
                      ·
                        rfl

theorem cell23_206378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_206378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206378 prefixEnd_206378 := by exact prefixLift 206378
  have htrace : WordTrace (prefixWord ++ tailWord_206378) baseStart_206378 baseEnd_206378 := by
    simpa [prefixWord, tailWord_206378, baseEnd_206378] using wordTrace_append hprefix tailTrace_206378
  have hstable : (prefixWord ++ tailWord_206378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206378).length < 2 ^ (prefixWord ++ tailWord_206378).sum := by decide
  have hdescent : baseEnd_206378 < baseStart_206378 := by decide
  rcases family_descends (prefixWord ++ tailWord_206378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206428 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_206428 : Nat := 118140960795 + 206428 * 2 ^ 59
def prefixEnd_206428 : Nat := 4983230072969 + 3 ^ 40 * 206428 * 2
def baseEnd_206428 : Nat := 105996784546423583200661

theorem tailTrace_206428 : CollatzResearch.WordTrace tailWord_206428 prefixEnd_206428 105996784546423583200661 := by
  unfold tailWord_206428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764523848077042970353969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5019365130769390627138625 3764523848077042970353969)
  ·
    refine ⟨2823392886057782227765477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3764523848077042970353969 2823392886057782227765477)
    ·
      refine ⟨529386166135834167706027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2823392886057782227765477 529386166135834167706027)
      ·
        refine ⟨794079249203751251559041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529386166135834167706027 794079249203751251559041)
        ·
          refine ⟨595559436902813438669281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794079249203751251559041 595559436902813438669281)
          ·
            refine ⟨446669577677110079001961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595559436902813438669281 446669577677110079001961)
            ·
              refine ⟨335002183257832559251471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446669577677110079001961 335002183257832559251471)
              ·
                refine ⟨502503274886748838877207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335002183257832559251471 502503274886748838877207)
                ·
                  refine ⟨753754912330123258315811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502503274886748838877207 753754912330123258315811)
                  ·
                    refine ⟨1130632368495184887473717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 753754912330123258315811 1130632368495184887473717)
                    ·
                      refine ⟨105996784546423583200661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1130632368495184887473717 105996784546423583200661)
                      ·
                        rfl

theorem cell23_206428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_206428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206428 prefixEnd_206428 := by exact prefixLift 206428
  have htrace : WordTrace (prefixWord ++ tailWord_206428) baseStart_206428 baseEnd_206428 := by
    simpa [prefixWord, tailWord_206428, baseEnd_206428] using wordTrace_append hprefix tailTrace_206428
  have hstable : (prefixWord ++ tailWord_206428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206428).length < 2 ^ (prefixWord ++ tailWord_206428).sum := by decide
  have hdescent : baseEnd_206428 < baseStart_206428 := by decide
  rcases family_descends (prefixWord ++ tailWord_206428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206442 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_206442 : Nat := 118140960795 + 206442 * 2 ^ 59
def prefixEnd_206442 : Nat := 4983230072969 + 3 ^ 40 * 206442 * 2
def baseEnd_206442 : Nat := 106003973275586528425597

theorem tailTrace_206442 : CollatzResearch.WordTrace tailWord_206442 prefixEnd_206442 106003973275586528425597 := by
  unfold tailWord_206442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882389579525841582929395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5019705545402244221145053 1882389579525841582929395)
  ·
    refine ⟨2823584369288762374394093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882389579525841582929395 2823584369288762374394093)
    ·
      refine ⟨1058844138483285890397785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2823584369288762374394093 1058844138483285890397785)
      ·
        refine ⟨794133103862464417798339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1058844138483285890397785 794133103862464417798339)
        ·
          refine ⟨1191199655793696626697509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794133103862464417798339 1191199655793696626697509)
          ·
            refine ⟨223349935461318117505783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1191199655793696626697509 223349935461318117505783)
            ·
              refine ⟨335024903191977176258675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223349935461318117505783 335024903191977176258675)
              ·
                refine ⟨502537354787965764388013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335024903191977176258675 502537354787965764388013)
                ·
                  refine ⟨188451508045487161645505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502537354787965764388013 188451508045487161645505)
                  ·
                    refine ⟨141338631034115371234129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188451508045487161645505 141338631034115371234129)
                    ·
                      refine ⟨106003973275586528425597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141338631034115371234129 106003973275586528425597)
                      ·
                        rfl

theorem cell23_206442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_206442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206442 prefixEnd_206442 := by exact prefixLift 206442
  have htrace : WordTrace (prefixWord ++ tailWord_206442) baseStart_206442 baseEnd_206442 := by
    simpa [prefixWord, tailWord_206442, baseEnd_206442] using wordTrace_append hprefix tailTrace_206442
  have hstable : (prefixWord ++ tailWord_206442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206442).length < 2 ^ (prefixWord ++ tailWord_206442).sum := by decide
  have hdescent : baseEnd_206442 < baseStart_206442 := by decide
  rcases family_descends (prefixWord ++ tailWord_206442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206444 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_206444 : Nat := 118140960795 + 206444 * 2 ^ 59
def prefixEnd_206444 : Nat := 4983230072969 + 3 ^ 40 * 206444 * 2
def baseEnd_206444 : Nat := 35335000078965173533529

theorem tailTrace_206444 : CollatzResearch.WordTrace tailWord_206444 prefixEnd_206444 35335000078965173533529 := by
  unfold tailWord_206444
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764815632048060336645193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5019754176064080448860257 3764815632048060336645193)
  ·
    refine ⟨2823611724036045252483895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3764815632048060336645193 2823611724036045252483895)
    ·
      refine ⟨4235417586054067878725843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823611724036045252483895 4235417586054067878725843)
      ·
        refine ⟨6353126379081101818088765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235417586054067878725843 6353126379081101818088765)
        ·
          refine ⟨2382422392155413181783287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6353126379081101818088765 2382422392155413181783287)
          ·
            refine ⟨3573633588233119772674931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382422392155413181783287 3573633588233119772674931)
            ·
              refine ⟨5360450382349679659012397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573633588233119772674931 5360450382349679659012397)
              ·
                refine ⟨2010168893381129872129649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5360450382349679659012397 2010168893381129872129649)
                ·
                  refine ⟨1507626670035847404097237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010168893381129872129649 1507626670035847404097237)
                  ·
                    refine ⟨35335000078965173533529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1507626670035847404097237 35335000078965173533529)
                    ·
                      rfl

theorem cell23_206444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_206444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206444 prefixEnd_206444 := by exact prefixLift 206444
  have htrace : WordTrace (prefixWord ++ tailWord_206444) baseStart_206444 baseEnd_206444 := by
    simpa [prefixWord, tailWord_206444, baseEnd_206444] using wordTrace_append hprefix tailTrace_206444
  have hstable : (prefixWord ++ tailWord_206444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206444).length < 2 ^ (prefixWord ++ tailWord_206444).sum := by decide
  have hdescent : baseEnd_206444 < baseStart_206444 := by decide
  rcases family_descends (prefixWord ++ tailWord_206444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206492 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_206492 : Nat := 118140960795 + 206492 * 2 ^ 59
def prefixEnd_206492 : Nat := 4983230072969 + 3 ^ 40 * 206492 * 2
def baseEnd_206492 : Nat := 106029647308311332800367

theorem tailTrace_206492 : CollatzResearch.WordTrace tailWord_206492 prefixEnd_206492 106029647308311332800367 := by
  unfold tailWord_206492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765690983961112435518865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5020921311948149914025153 3765690983961112435518865)
  ·
    refine ⟨2824268237970834326639149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3765690983961112435518865 2824268237970834326639149)
    ·
      refine ⟨1059100589239062872489681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2824268237970834326639149 1059100589239062872489681)
      ·
        refine ⟨794325441929297154367261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059100589239062872489681 794325441929297154367261)
        ·
          refine ⟨297872040723486432887723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794325441929297154367261 297872040723486432887723)
          ·
            refine ⟨446808061085229649331585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297872040723486432887723 446808061085229649331585)
            ·
              refine ⟨335106045813922236998689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446808061085229649331585 335106045813922236998689)
              ·
                refine ⟨251329534360441677749017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335106045813922236998689 251329534360441677749017)
                ·
                  refine ⟨188497150770331258311763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251329534360441677749017 188497150770331258311763)
                  ·
                    refine ⟨282745726155496887467645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188497150770331258311763 282745726155496887467645)
                    ·
                      refine ⟨106029647308311332800367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 282745726155496887467645 106029647308311332800367)
                      ·
                        rfl

theorem cell23_206492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_206492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206492 prefixEnd_206492 := by exact prefixLift 206492
  have htrace : WordTrace (prefixWord ++ tailWord_206492) baseStart_206492 baseEnd_206492 := by
    simpa [prefixWord, tailWord_206492, baseEnd_206492] using wordTrace_append hprefix tailTrace_206492
  have hstable : (prefixWord ++ tailWord_206492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206492).length < 2 ^ (prefixWord ++ tailWord_206492).sum := by decide
  have hdescent : baseEnd_206492 < baseStart_206492 := by decide
  rcases family_descends (prefixWord ++ tailWord_206492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206501 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_206501 : Nat := 118140960795 + 206501 * 2 ^ 59
def prefixEnd_206501 : Nat := 4983230072969 + 3 ^ 40 * 206501 * 2
def baseEnd_206501 : Nat := 106034268634201797587825

theorem tailTrace_206501 : CollatzResearch.WordTrace tailWord_206501 prefixEnd_206501 106034268634201797587825 := by
  unfold tailWord_206501
  simp only [CollatzResearch.WordTrace]
  refine ⟨7531710224889619408115357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5021140149926412938743571 7531710224889619408115357)
  ·
    refine ⟨2824391334333607278043259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7531710224889619408115357 2824391334333607278043259)
    ·
      refine ⟨4236587001500410917064889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824391334333607278043259 4236587001500410917064889)
      ·
        refine ⟨3177440251125308187798667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4236587001500410917064889 3177440251125308187798667)
        ·
          refine ⟨4766160376687962281698001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177440251125308187798667 4766160376687962281698001)
          ·
            refine ⟨3574620282515971711273501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4766160376687962281698001 3574620282515971711273501)
            ·
              refine ⟨1340482605943489391727563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3574620282515971711273501 1340482605943489391727563)
              ·
                refine ⟨2010723908915234087591345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340482605943489391727563 2010723908915234087591345)
                ·
                  refine ⟨1508042931686425565693509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010723908915234087591345 1508042931686425565693509)
                  ·
                    refine ⟨282758049691204793567533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508042931686425565693509 282758049691204793567533)
                    ·
                      refine ⟨106034268634201797587825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 282758049691204793567533 106034268634201797587825)
                      ·
                        rfl

theorem cell23_206501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_206501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206501 prefixEnd_206501 := by exact prefixLift 206501
  have htrace : WordTrace (prefixWord ++ tailWord_206501) baseStart_206501 baseEnd_206501 := by
    simpa [prefixWord, tailWord_206501, baseEnd_206501] using wordTrace_append hprefix tailTrace_206501
  have hstable : (prefixWord ++ tailWord_206501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206501).length < 2 ^ (prefixWord ++ tailWord_206501).sum := by decide
  have hdescent : baseEnd_206501 < baseStart_206501 := by decide
  rcases family_descends (prefixWord ++ tailWord_206501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206511 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_206511 : Nat := 118140960795 + 206511 * 2 ^ 59
def prefixEnd_206511 : Nat := 4983230072969 + 3 ^ 40 * 206511 * 2
def baseEnd_206511 : Nat := 106039403440746758462779

theorem tailTrace_206511 : CollatzResearch.WordTrace tailWord_206511 prefixEnd_206511 106039403440746758462779 := by
  unfold tailWord_206511
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532074954853391115979387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5021383303235594077319591 7532074954853391115979387)
  ·
    refine ⟨11298112432280086673969081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7532074954853391115979387 11298112432280086673969081)
    ·
      refine ⟨8473584324210065005476811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11298112432280086673969081 8473584324210065005476811)
      ·
        refine ⟨12710376486315097508215217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8473584324210065005476811 12710376486315097508215217)
        ·
          refine ⟨9532782364736323131161413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12710376486315097508215217 9532782364736323131161413)
          ·
            refine ⟨1787396693388060587092765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9532782364736323131161413 1787396693388060587092765)
            ·
              refine ⟨670273760020522720159787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1787396693388060587092765 670273760020522720159787)
              ·
                refine ⟨1005410640030784080239681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670273760020522720159787 1005410640030784080239681)
                ·
                  refine ⟨754057980023088060179761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1005410640030784080239681 754057980023088060179761)
                  ·
                    refine ⟨565543485017316045134821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 754057980023088060179761 565543485017316045134821)
                    ·
                      refine ⟨106039403440746758462779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 565543485017316045134821 106039403440746758462779)
                      ·
                        rfl

theorem cell23_206511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_206511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206511 prefixEnd_206511 := by exact prefixLift 206511
  have htrace : WordTrace (prefixWord ++ tailWord_206511) baseStart_206511 baseEnd_206511 := by
    simpa [prefixWord, tailWord_206511, baseEnd_206511] using wordTrace_append hprefix tailTrace_206511
  have hstable : (prefixWord ++ tailWord_206511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206511).length < 2 ^ (prefixWord ++ tailWord_206511).sum := by decide
  have hdescent : baseEnd_206511 < baseStart_206511 := by decide
  rcases family_descends (prefixWord ++ tailWord_206511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206515 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 2, 2, 2]
def baseStart_206515 : Nat := 118140960795 + 206515 * 2 ^ 59
def prefixEnd_206515 : Nat := 4983230072969 + 3 ^ 40 * 206515 * 2
def baseEnd_206515 : Nat := 106041457363364742812761

theorem tailTrace_206515 : CollatzResearch.WordTrace tailWord_206515 prefixEnd_206515 106041457363364742812761 := by
  unfold tailWord_206515
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532220846838899799124999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5021480564559266532749999 7532220846838899799124999)
  ·
    refine ⟨11298331270258349698687499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7532220846838899799124999 11298331270258349698687499)
    ·
      refine ⟨16947496905387524548031249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11298331270258349698687499 16947496905387524548031249)
      ·
        refine ⟨12710622679040643411023437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16947496905387524548031249 12710622679040643411023437)
        ·
          refine ⟨4766483504640241279133789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12710622679040643411023437 4766483504640241279133789)
          ·
            refine ⟨1787431314240090479675171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4766483504640241279133789 1787431314240090479675171)
            ·
              refine ⟨2681146971360135719512757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787431314240090479675171 2681146971360135719512757)
              ·
                refine ⟨251357528565012723704321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2681146971360135719512757 251357528565012723704321)
                ·
                  refine ⟨188518146423759542778241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251357528565012723704321 188518146423759542778241)
                  ·
                    refine ⟨141388609817819657083681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188518146423759542778241 141388609817819657083681)
                    ·
                      refine ⟨106041457363364742812761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141388609817819657083681 106041457363364742812761)
                      ·
                        rfl

theorem cell23_206515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 2, 2].length) (baseStart_206515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206515 prefixEnd_206515 := by exact prefixLift 206515
  have htrace : WordTrace (prefixWord ++ tailWord_206515) baseStart_206515 baseEnd_206515 := by
    simpa [prefixWord, tailWord_206515, baseEnd_206515] using wordTrace_append hprefix tailTrace_206515
  have hstable : (prefixWord ++ tailWord_206515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206515).length < 2 ^ (prefixWord ++ tailWord_206515).sum := by decide
  have hdescent : baseEnd_206515 < baseStart_206515 := by decide
  rcases family_descends (prefixWord ++ tailWord_206515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206551 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 4, 5]
def baseStart_206551 : Nat := 118140960795 + 206551 * 2 ^ 59
def prefixEnd_206551 : Nat := 4983230072969 + 3 ^ 40 * 206551 * 2
def baseEnd_206551 : Nat := 35353314222308867320865

theorem tailTrace_206551 : CollatzResearch.WordTrace tailWord_206551 prefixEnd_206551 35353314222308867320865 := by
  unfold tailWord_206551
  simp only [CollatzResearch.WordTrace]
  refine ⟨7533533874708477947435507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5022355916472318631623671 7533533874708477947435507)
  ·
    refine ⟨11300300812062716921153261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7533533874708477947435507 11300300812062716921153261)
    ·
      refine ⟨4237612804523518845432473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11300300812062716921153261 4237612804523518845432473)
      ·
        refine ⟨3178209603392639134074355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4237612804523518845432473 3178209603392639134074355)
        ·
          refine ⟨4767314405088958701111533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178209603392639134074355 4767314405088958701111533)
          ·
            refine ⟨1787742901908359512916825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4767314405088958701111533 1787742901908359512916825)
            ·
              refine ⟨1340807176431269634687619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787742901908359512916825 1340807176431269634687619)
              ·
                refine ⟨2011210764646904452031429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340807176431269634687619 2011210764646904452031429)
                ·
                  refine ⟨377102018371294584755893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011210764646904452031429 377102018371294584755893)
                  ·
                    refine ⟨35353314222308867320865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377102018371294584755893 35353314222308867320865)
                    ·
                      rfl

theorem cell23_206551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_206551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206551 prefixEnd_206551 := by exact prefixLift 206551
  have htrace : WordTrace (prefixWord ++ tailWord_206551) baseStart_206551 baseEnd_206551 := by
    simpa [prefixWord, tailWord_206551, baseEnd_206551] using wordTrace_append hprefix tailTrace_206551
  have hstable : (prefixWord ++ tailWord_206551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206551).length < 2 ^ (prefixWord ++ tailWord_206551).sum := by decide
  have hdescent : baseEnd_206551 < baseStart_206551 := by decide
  rcases family_descends (prefixWord ++ tailWord_206551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206571 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4]
def baseStart_206571 : Nat := 118140960795 + 206571 * 2 ^ 59
def prefixEnd_206571 : Nat := 4983230072969 + 3 ^ 40 * 206571 * 2
def baseEnd_206571 : Nat := 106070212280016523712503

theorem tailTrace_206571 : CollatzResearch.WordTrace tailWord_206571 prefixEnd_206571 106070212280016523712503 := by
  unfold tailWord_206571
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534263334636021363163567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5022842223090680908775711 7534263334636021363163567)
  ·
    refine ⟨11301395001954032044745351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7534263334636021363163567 11301395001954032044745351)
    ·
      refine ⟨16952092502931048067118027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11301395001954032044745351 16952092502931048067118027)
      ·
        refine ⟨25428138754396572100677041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16952092502931048067118027 25428138754396572100677041)
        ·
          refine ⟨19071104065797429075507781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25428138754396572100677041 19071104065797429075507781)
          ·
            refine ⟨3575832012337017951657709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19071104065797429075507781 3575832012337017951657709)
            ·
              refine ⟨1340937004626381731871641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3575832012337017951657709 1340937004626381731871641)
              ·
                refine ⟨1005702753469786298903731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340937004626381731871641 1005702753469786298903731)
                ·
                  refine ⟨1508554130204679448355597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005702753469786298903731 1508554130204679448355597)
                  ·
                    refine ⟨565707798826754793133349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508554130204679448355597 565707798826754793133349)
                    ·
                      refine ⟨106070212280016523712503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 565707798826754793133349 106070212280016523712503)
                      ·
                        rfl

theorem cell23_206571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_206571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206571 prefixEnd_206571 := by exact prefixLift 206571
  have htrace : WordTrace (prefixWord ++ tailWord_206571) baseStart_206571 baseEnd_206571 := by
    simpa [prefixWord, tailWord_206571, baseEnd_206571] using wordTrace_append hprefix tailTrace_206571
  have hstable : (prefixWord ++ tailWord_206571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206571).length < 2 ^ (prefixWord ++ tailWord_206571).sum := by decide
  have hdescent : baseEnd_206571 < baseStart_206571 := by decide
  rcases family_descends (prefixWord ++ tailWord_206571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206588 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_206588 : Nat := 118140960795 + 206588 * 2 ^ 59
def prefixEnd_206588 : Nat := 4983230072969 + 3 ^ 40 * 206588 * 2
def baseEnd_206588 : Nat := 106078941451142957199925

theorem tailTrace_206588 : CollatzResearch.WordTrace tailWord_206588 prefixEnd_206588 106078941451142957199925 := by
  unfold tailWord_206588
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767441687787216633266209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5023255583716288844354945 3767441687787216633266209)
  ·
    refine ⟨2825581265840412474949657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3767441687787216633266209 2825581265840412474949657)
    ·
      refine ⟨2119185949380309356212243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2825581265840412474949657 2119185949380309356212243)
      ·
        refine ⟨3178778924070464034318365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119185949380309356212243 3178778924070464034318365)
        ·
          refine ⟨1192042096526424012869387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3178778924070464034318365 1192042096526424012869387)
          ·
            refine ⟨1788063144789636019304081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192042096526424012869387 1788063144789636019304081)
            ·
              refine ⟨1341047358592227014478061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788063144789636019304081 1341047358592227014478061)
              ·
                refine ⟨502892759472085130429273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1341047358592227014478061 502892759472085130429273)
                ·
                  refine ⟨377169569604063847821955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502892759472085130429273 377169569604063847821955)
                  ·
                    refine ⟨565754354406095771732933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 377169569604063847821955 565754354406095771732933)
                    ·
                      refine ⟨106078941451142957199925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 565754354406095771732933 106078941451142957199925)
                      ·
                        rfl

theorem cell23_206588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_206588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206588 prefixEnd_206588 := by exact prefixLift 206588
  have htrace : WordTrace (prefixWord ++ tailWord_206588) baseStart_206588 baseEnd_206588 := by
    simpa [prefixWord, tailWord_206588, baseEnd_206588] using wordTrace_append hprefix tailTrace_206588
  have hstable : (prefixWord ++ tailWord_206588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206588).length < 2 ^ (prefixWord ++ tailWord_206588).sum := by decide
  have hdescent : baseEnd_206588 < baseStart_206588 := by decide
  rcases family_descends (prefixWord ++ tailWord_206588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206615 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 3, 4]
def baseStart_206615 : Nat := 118140960795 + 206615 * 2 ^ 59
def prefixEnd_206615 : Nat := 4983230072969 + 3 ^ 40 * 206615 * 2
def baseEnd_206615 : Nat := 35364268476271450520767

theorem tailTrace_206615 : CollatzResearch.WordTrace tailWord_206615 prefixEnd_206615 35364268476271450520767 := by
  unfold tailWord_206615
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535868146476616877765299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5023912097651077918510199 7535868146476616877765299)
  ·
    refine ⟨11303802219714925316647949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7535868146476616877765299 11303802219714925316647949)
    ·
      refine ⟨4238925832393096993742981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11303802219714925316647949 4238925832393096993742981)
      ·
        refine ⟨794798593573705686326809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4238925832393096993742981 794798593573705686326809)
        ·
          refine ⟨596098945180279264745107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794798593573705686326809 596098945180279264745107)
          ·
            refine ⟨894148417770418897117661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596098945180279264745107 894148417770418897117661)
            ·
              refine ⟨335305656663907086419123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 894148417770418897117661 335305656663907086419123)
              ·
                refine ⟨502958484995860629628685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335305656663907086419123 502958484995860629628685)
                ·
                  refine ⟨188609431873447736110757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502958484995860629628685 188609431873447736110757)
                  ·
                    refine ⟨35364268476271450520767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188609431873447736110757 35364268476271450520767)
                    ·
                      rfl

theorem cell23_206615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_206615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206615 prefixEnd_206615 := by exact prefixLift 206615
  have htrace : WordTrace (prefixWord ++ tailWord_206615) baseStart_206615 baseEnd_206615 := by
    simpa [prefixWord, tailWord_206615, baseEnd_206615] using wordTrace_append hprefix tailTrace_206615
  have hstable : (prefixWord ++ tailWord_206615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206615).length < 2 ^ (prefixWord ++ tailWord_206615).sum := by decide
  have hdescent : baseEnd_206615 < baseStart_206615 := by decide
  rcases family_descends (prefixWord ++ tailWord_206615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206662 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_206662 : Nat := 118140960795 + 206662 * 2 ^ 59
def prefixEnd_206662 : Nat := 4983230072969 + 3 ^ 40 * 206662 * 2
def baseEnd_206662 : Nat := 11790771002175074186065

theorem tailTrace_206662 : CollatzResearch.WordTrace tailWord_206662 prefixEnd_206662 11790771002175074186065 := by
  unfold tailWord_206662
  simp only [CollatzResearch.WordTrace]
  refine ⟨235549449290823247022695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5025054918204229269817493 235549449290823247022695)
  ·
    refine ⟨353324173936234870534043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235549449290823247022695 353324173936234870534043)
    ·
      refine ⟨529986260904352305801065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353324173936234870534043 529986260904352305801065)
      ·
        refine ⟨397489695678264229350799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529986260904352305801065 397489695678264229350799)
        ·
          refine ⟨596234543517396344026199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397489695678264229350799 596234543517396344026199)
          ·
            refine ⟨894351815276094516039299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596234543517396344026199 894351815276094516039299)
            ·
              refine ⟨1341527722914141774058949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894351815276094516039299 1341527722914141774058949)
              ·
                refine ⟨251536448046401582636053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1341527722914141774058949 251536448046401582636053)
                ·
                  refine ⟨11790771002175074186065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 251536448046401582636053 11790771002175074186065)
                  ·
                    rfl

theorem cell23_206662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_206662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206662 prefixEnd_206662 := by exact prefixLift 206662
  have htrace : WordTrace (prefixWord ++ tailWord_206662) baseStart_206662 baseEnd_206662 := by
    simpa [prefixWord, tailWord_206662, baseEnd_206662] using wordTrace_append hprefix tailTrace_206662
  have hstable : (prefixWord ++ tailWord_206662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206662).length < 2 ^ (prefixWord ++ tailWord_206662).sum := by decide
  have hdescent : baseEnd_206662 < baseStart_206662 := by decide
  rcases family_descends (prefixWord ++ tailWord_206662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206665 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 2, 3, 2]
def baseStart_206665 : Nat := 118140960795 + 206665 * 2 ^ 59
def prefixEnd_206665 : Nat := 4983230072969 + 3 ^ 40 * 206665 * 2
def baseEnd_206665 : Nat := 106118479461539155937071

theorem tailTrace_206665 : CollatzResearch.WordTrace tailWord_206665 prefixEnd_206665 106118479461539155937071 := by
  unfold tailWord_206665
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537691796295475417085449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5025127864196983611390299 7537691796295475417085449)
  ·
    refine ⟨5653268847221606562814087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7537691796295475417085449 5653268847221606562814087)
    ·
      refine ⟨8479903270832409844221131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653268847221606562814087 8479903270832409844221131)
      ·
        refine ⟨12719854906248614766331697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479903270832409844221131 12719854906248614766331697)
        ·
          refine ⟨9539891179686461074748773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719854906248614766331697 9539891179686461074748773)
          ·
            refine ⟨1788729596191211451515395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9539891179686461074748773 1788729596191211451515395)
            ·
              refine ⟨2683094394286817177273093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788729596191211451515395 2683094394286817177273093)
              ·
                refine ⟨503080198928778220738705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2683094394286817177273093 503080198928778220738705)
                ·
                  refine ⟨377310149196583665554029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503080198928778220738705 377310149196583665554029)
                  ·
                    refine ⟨141491305948718874582761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377310149196583665554029 141491305948718874582761)
                    ·
                      refine ⟨106118479461539155937071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141491305948718874582761 106118479461539155937071)
                      ·
                        rfl

theorem cell23_206665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 3, 2].length) (baseStart_206665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206665 prefixEnd_206665 := by exact prefixLift 206665
  have htrace : WordTrace (prefixWord ++ tailWord_206665) baseStart_206665 baseEnd_206665 := by
    simpa [prefixWord, tailWord_206665, baseEnd_206665] using wordTrace_append hprefix tailTrace_206665
  have hstable : (prefixWord ++ tailWord_206665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206665).length < 2 ^ (prefixWord ++ tailWord_206665).sum := by decide
  have hdescent : baseEnd_206665 < baseStart_206665 := by decide
  rcases family_descends (prefixWord ++ tailWord_206665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206688 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 1, 6]
def baseStart_206688 : Nat := 118140960795 + 206688 * 2 ^ 59
def prefixEnd_206688 : Nat := 4983230072969 + 3 ^ 40 * 206688 * 2
def baseEnd_206688 : Nat := 35376763172197521983155

theorem tailTrace_206688 : CollatzResearch.WordTrace tailWord_206688 prefixEnd_206688 35376763172197521983155 := by
  unfold tailWord_206688
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769265337606075172586359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5025687116808100230115145 3769265337606075172586359)
  ·
    refine ⟨5653898006409112758879539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3769265337606075172586359 5653898006409112758879539)
    ·
      refine ⟨8480847009613669138319309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653898006409112758879539 8480847009613669138319309)
      ·
        refine ⟨3180317628605125926869741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8480847009613669138319309 3180317628605125926869741)
        ·
          refine ⟨1192619110726922222576153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3180317628605125926869741 1192619110726922222576153)
          ·
            refine ⟨894464333045191666932115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192619110726922222576153 894464333045191666932115)
            ·
              refine ⟨1341696499567787500398173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894464333045191666932115 1341696499567787500398173)
              ·
                refine ⟨503136187337920312649315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1341696499567787500398173 503136187337920312649315)
                ·
                  refine ⟨754704281006880468973973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503136187337920312649315 754704281006880468973973)
                  ·
                    refine ⟨35376763172197521983155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 754704281006880468973973 35376763172197521983155)
                    ·
                      rfl

theorem cell23_206688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_206688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206688 prefixEnd_206688 := by exact prefixLift 206688
  have htrace : WordTrace (prefixWord ++ tailWord_206688) baseStart_206688 baseEnd_206688 := by
    simpa [prefixWord, tailWord_206688, baseEnd_206688] using wordTrace_append hprefix tailTrace_206688
  have hstable : (prefixWord ++ tailWord_206688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206688).length < 2 ^ (prefixWord ++ tailWord_206688).sum := by decide
  have hdescent : baseEnd_206688 < baseStart_206688 := by decide
  rcases family_descends (prefixWord ++ tailWord_206688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206695 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_206695 : Nat := 118140960795 + 206695 * 2 ^ 59
def prefixEnd_206695 : Nat := 4983230072969 + 3 ^ 40 * 206695 * 2
def baseEnd_206695 : Nat := 106133883881174038561933

theorem tailTrace_206695 : CollatzResearch.WordTrace tailWord_206695 prefixEnd_206695 106133883881174038561933 := by
  unfold tailWord_206695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7538785986186790540677539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5025857324124527027118359 7538785986186790540677539)
  ·
    refine ⟨11308178979280185811016309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7538785986186790540677539 11308178979280185811016309)
    ·
      refine ⟨1060141779307517419782779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11308178979280185811016309 1060141779307517419782779)
      ·
        refine ⟨1590212668961276129674169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060141779307517419782779 1590212668961276129674169)
        ·
          refine ⟨1192659501720957097255627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1590212668961276129674169 1192659501720957097255627)
          ·
            refine ⟨1788989252581435645883441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192659501720957097255627 1788989252581435645883441)
            ·
              refine ⟨1341741939436076734412581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788989252581435645883441 1341741939436076734412581)
              ·
                refine ⟨251576613644264387702359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1341741939436076734412581 251576613644264387702359)
                ·
                  refine ⟨377364920466396581553539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251576613644264387702359 377364920466396581553539)
                  ·
                    refine ⟨566047380699594872330309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 377364920466396581553539 566047380699594872330309)
                    ·
                      refine ⟨106133883881174038561933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 566047380699594872330309 106133883881174038561933)
                      ·
                        rfl

theorem cell23_206695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_206695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206695 prefixEnd_206695 := by exact prefixLift 206695
  have htrace : WordTrace (prefixWord ++ tailWord_206695) baseStart_206695 baseEnd_206695 := by
    simpa [prefixWord, tailWord_206695, baseEnd_206695] using wordTrace_append hprefix tailTrace_206695
  have hstable : (prefixWord ++ tailWord_206695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206695).length < 2 ^ (prefixWord ++ tailWord_206695).sum := by decide
  have hdescent : baseEnd_206695 < baseStart_206695 := by decide
  rcases family_descends (prefixWord ++ tailWord_206695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206729 : List Nat := [1, 2, 1, 1, 5, 1, 1, 6, 1, 2, 2]
def baseStart_206729 : Nat := 118140960795 + 206729 * 2 ^ 59
def prefixEnd_206729 : Nat := 4983230072969 + 3 ^ 40 * 206729 * 2
def baseEnd_206729 : Nat := 106151342223426905536777

theorem tailTrace_206729 : CollatzResearch.WordTrace tailWord_206729 prefixEnd_206729 106151342223426905536777 := by
  unfold tailWord_206729
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540026068063614347415241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5026684045375742898276827 7540026068063614347415241)
  ·
    refine ⟨5655019551047710760561431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7540026068063614347415241 5655019551047710760561431)
    ·
      refine ⟨8482529326571566140842147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5655019551047710760561431 8482529326571566140842147)
      ·
        refine ⟨12723793989857349211263221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8482529326571566140842147 12723793989857349211263221)
        ·
          refine ⟨1192855686549126488555927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12723793989857349211263221 1192855686549126488555927)
          ·
            refine ⟨1789283529823689732833891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192855686549126488555927 1789283529823689732833891)
            ·
              refine ⟨2683925294735534599250837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789283529823689732833891 2683925294735534599250837)
              ·
                refine ⟨125808998190728184339883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2683925294735534599250837 125808998190728184339883)
                ·
                  refine ⟨188713497286092276509825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125808998190728184339883 188713497286092276509825)
                  ·
                    refine ⟨141535122964569207382369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188713497286092276509825 141535122964569207382369)
                    ·
                      refine ⟨106151342223426905536777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141535122964569207382369 106151342223426905536777)
                      ·
                        rfl

theorem cell23_206729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 2, 2].length) (baseStart_206729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206729 prefixEnd_206729 := by exact prefixLift 206729
  have htrace : WordTrace (prefixWord ++ tailWord_206729) baseStart_206729 baseEnd_206729 := by
    simpa [prefixWord, tailWord_206729, baseEnd_206729] using wordTrace_append hprefix tailTrace_206729
  have hstable : (prefixWord ++ tailWord_206729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206729).length < 2 ^ (prefixWord ++ tailWord_206729).sum := by decide
  have hdescent : baseEnd_206729 < baseStart_206729 := by decide
  rcases family_descends (prefixWord ++ tailWord_206729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206745 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 3]
def baseStart_206745 : Nat := 118140960795 + 206745 * 2 ^ 59
def prefixEnd_206745 : Nat := 4983230072969 + 3 ^ 40 * 206745 * 2
def baseEnd_206745 : Nat := 106159557913898842936703

theorem tailTrace_206745 : CollatzResearch.WordTrace tailWord_206745 prefixEnd_206745 106159557913898842936703 := by
  unfold tailWord_206745
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540609636005649079997689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5027073090670432719998459 7540609636005649079997689)
  ·
    refine ⟨5655457227004236809998267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7540609636005649079997689 5655457227004236809998267)
    ·
      refine ⟨8483185840506355214997401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5655457227004236809998267 8483185840506355214997401)
      ·
        refine ⟨6362389380379766411248051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8483185840506355214997401 6362389380379766411248051)
        ·
          refine ⟨9543584070569649616872077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6362389380379766411248051 9543584070569649616872077)
          ·
            refine ⟨3578844026463618606327029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9543584070569649616872077 3578844026463618606327029)
            ·
              refine ⟨335516627480964244343159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3578844026463618606327029 335516627480964244343159)
              ·
                refine ⟨503274941221446366514739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335516627480964244343159 503274941221446366514739)
                ·
                  refine ⟨754912411832169549772109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503274941221446366514739 754912411832169549772109)
                  ·
                    refine ⟨283092154437063581164541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754912411832169549772109 283092154437063581164541)
                    ·
                      refine ⟨106159557913898842936703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283092154437063581164541 106159557913898842936703)
                      ·
                        rfl

theorem cell23_206745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_206745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206745 prefixEnd_206745 := by exact prefixLift 206745
  have htrace : WordTrace (prefixWord ++ tailWord_206745) baseStart_206745 baseEnd_206745 := by
    simpa [prefixWord, tailWord_206745, baseEnd_206745] using wordTrace_append hprefix tailTrace_206745
  have hstable : (prefixWord ++ tailWord_206745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206745).length < 2 ^ (prefixWord ++ tailWord_206745).sum := by decide
  have hdescent : baseEnd_206745 < baseStart_206745 := by decide
  rcases family_descends (prefixWord ++ tailWord_206745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206766 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_206766 : Nat := 118140960795 + 206766 * 2 ^ 59
def prefixEnd_206766 : Nat := 4983230072969 + 3 ^ 40 * 206766 * 2
def baseEnd_206766 : Nat := 106170341007643260774107

theorem tailTrace_206766 : CollatzResearch.WordTrace tailWord_206766 prefixEnd_206766 106170341007643260774107 := by
  unfold tailWord_206766
  simp only [CollatzResearch.WordTrace]
  refine ⟨942671946116196208314019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5027583712619713111008101 942671946116196208314019)
  ·
    refine ⟨1414007919174294312471029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942671946116196208314019 1414007919174294312471029)
    ·
      refine ⟨132563242422590091794159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1414007919174294312471029 132563242422590091794159)
      ·
        refine ⟨198844863633885137691239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132563242422590091794159 198844863633885137691239)
        ·
          refine ⟨298267295450827706536859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198844863633885137691239 298267295450827706536859)
          ·
            refine ⟨447400943176241559805289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298267295450827706536859 447400943176241559805289)
            ·
              refine ⟨335550707382181169853967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447400943176241559805289 335550707382181169853967)
              ·
                refine ⟨503326061073271754780951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335550707382181169853967 503326061073271754780951)
                ·
                  refine ⟨754989091609907632171427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503326061073271754780951 754989091609907632171427)
                  ·
                    refine ⟨1132483637414861448257141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754989091609907632171427 1132483637414861448257141)
                    ·
                      refine ⟨106170341007643260774107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1132483637414861448257141 106170341007643260774107)
                      ·
                        rfl

theorem cell23_206766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_206766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206766 prefixEnd_206766 := by exact prefixLift 206766
  have htrace : WordTrace (prefixWord ++ tailWord_206766) baseStart_206766 baseEnd_206766 := by
    simpa [prefixWord, tailWord_206766, baseEnd_206766] using wordTrace_append hprefix tailTrace_206766
  have hstable : (prefixWord ++ tailWord_206766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206766).length < 2 ^ (prefixWord ++ tailWord_206766).sum := by decide
  have hdescent : baseEnd_206766 < baseStart_206766 := by decide
  rcases family_descends (prefixWord ++ tailWord_206766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206778 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_206778 : Nat := 118140960795 + 206778 * 2 ^ 59
def prefixEnd_206778 : Nat := 4983230072969 + 3 ^ 40 * 206778 * 2
def baseEnd_206778 : Nat := 35392167591832404608017

theorem tailTrace_206778 : CollatzResearch.WordTrace tailWord_206778 prefixEnd_206778 35392167591832404608017 := by
  unfold tailWord_206778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885453311221523928987247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5027875496590730477299325 1885453311221523928987247)
  ·
    refine ⟨2828179966832285893480871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1885453311221523928987247 2828179966832285893480871)
    ·
      refine ⟨4242269950248428840221307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828179966832285893480871 4242269950248428840221307)
      ·
        refine ⟨6363404925372643260331961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4242269950248428840221307 6363404925372643260331961)
        ·
          refine ⟨4772553694029482445248971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6363404925372643260331961 4772553694029482445248971)
          ·
            refine ⟨7158830541044223667873457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772553694029482445248971 7158830541044223667873457)
            ·
              refine ⟨5369122905783167750905093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7158830541044223667873457 5369122905783167750905093)
              ·
                refine ⟨1006710544834343953294705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5369122905783167750905093 1006710544834343953294705)
                ·
                  refine ⟨755032908625757964971029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006710544834343953294705 755032908625757964971029)
                  ·
                    refine ⟨35392167591832404608017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 755032908625757964971029 35392167591832404608017)
                    ·
                      rfl

theorem cell23_206778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_206778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206778 prefixEnd_206778 := by exact prefixLift 206778
  have htrace : WordTrace (prefixWord ++ tailWord_206778) baseStart_206778 baseEnd_206778 := by
    simpa [prefixWord, tailWord_206778, baseEnd_206778] using wordTrace_append hprefix tailTrace_206778
  have hstable : (prefixWord ++ tailWord_206778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206778).length < 2 ^ (prefixWord ++ tailWord_206778).sum := by decide
  have hdescent : baseEnd_206778 < baseStart_206778 := by decide
  rcases family_descends (prefixWord ++ tailWord_206778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206780 : List Nat := [2, 2, 2, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_206780 : Nat := 118140960795 + 206780 * 2 ^ 59
def prefixEnd_206780 : Nat := 4983230072969 + 3 ^ 40 * 206780 * 2
def baseEnd_206780 : Nat := 106177529736806205999043

theorem tailTrace_206780 : CollatzResearch.WordTrace tailWord_206780 prefixEnd_206780 106177529736806205999043 := by
  unfold tailWord_206780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3770943095439425028760897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5027924127252566705014529 3770943095439425028760897)
  ·
    refine ⟨2828207321579568771570673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3770943095439425028760897 2828207321579568771570673)
    ·
      refine ⟨2121155491184676578678005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2828207321579568771570673 2121155491184676578678005)
      ·
        refine ⟨198858327298563429251063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2121155491184676578678005 198858327298563429251063)
        ·
          refine ⟨298287490947845143876595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198858327298563429251063 298287490947845143876595)
          ·
            refine ⟨447431236421767715814893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298287490947845143876595 447431236421767715814893)
            ·
              refine ⟨167786713658162893430585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447431236421767715814893 167786713658162893430585)
              ·
                refine ⟨125840035243622170072939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167786713658162893430585 125840035243622170072939)
                ·
                  refine ⟨188760052865433255109409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125840035243622170072939 188760052865433255109409)
                  ·
                    refine ⟨141570039649074941332057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188760052865433255109409 141570039649074941332057)
                    ·
                      refine ⟨106177529736806205999043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141570039649074941332057 106177529736806205999043)
                      ·
                        rfl

theorem cell23_206780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_206780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206780 prefixEnd_206780 := by exact prefixLift 206780
  have htrace : WordTrace (prefixWord ++ tailWord_206780) baseStart_206780 baseEnd_206780 := by
    simpa [prefixWord, tailWord_206780, baseEnd_206780] using wordTrace_append hprefix tailTrace_206780
  have hstable : (prefixWord ++ tailWord_206780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206780).length < 2 ^ (prefixWord ++ tailWord_206780).sum := by decide
  have hdescent : baseEnd_206780 < baseStart_206780 := by decide
  rcases family_descends (prefixWord ++ tailWord_206780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206796 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 2, 1, 3]
def baseStart_206796 : Nat := 118140960795 + 206796 * 2 ^ 59
def prefixEnd_206796 : Nat := 4983230072969 + 3 ^ 40 * 206796 * 2
def baseEnd_206796 : Nat := 106185745427278143398969

theorem tailTrace_206796 : CollatzResearch.WordTrace tailWord_206796 prefixEnd_206796 106185745427278143398969 := by
  unfold tailWord_206796
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771234879410442395052121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5028313172547256526736161 3771234879410442395052121)
  ·
    refine ⟨2828426159557831796289091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3771234879410442395052121 2828426159557831796289091)
    ·
      refine ⟨4242639239336747694433637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828426159557831796289091 4242639239336747694433637)
      ·
        refine ⟨795494857375640192706307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4242639239336747694433637 795494857375640192706307)
        ·
          refine ⟨1193242286063460289059461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795494857375640192706307 1193242286063460289059461)
          ·
            refine ⟨223732928636898804198649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1193242286063460289059461 223732928636898804198649)
            ·
              refine ⟨167799696477674103148987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223732928636898804198649 167799696477674103148987)
              ·
                refine ⟨251699544716511154723481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167799696477674103148987 251699544716511154723481)
                ·
                  refine ⟨188774658537383366042611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251699544716511154723481 188774658537383366042611)
                  ·
                    refine ⟨283161987806075049063917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188774658537383366042611 283161987806075049063917)
                    ·
                      refine ⟨106185745427278143398969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283161987806075049063917 106185745427278143398969)
                      ·
                        rfl

theorem cell23_206796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_206796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206796 prefixEnd_206796 := by exact prefixLift 206796
  have htrace : WordTrace (prefixWord ++ tailWord_206796) baseStart_206796 baseEnd_206796 := by
    simpa [prefixWord, tailWord_206796, baseEnd_206796] using wordTrace_append hprefix tailTrace_206796
  have hstable : (prefixWord ++ tailWord_206796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206796).length < 2 ^ (prefixWord ++ tailWord_206796).sum := by decide
  have hdescent : baseEnd_206796 < baseStart_206796 := by decide
  rcases family_descends (prefixWord ++ tailWord_206796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206805 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_206805 : Nat := 118140960795 + 206805 * 2 ^ 59
def prefixEnd_206805 : Nat := 4983230072969 + 3 ^ 40 * 206805 * 2
def baseEnd_206805 : Nat := 106190366753168608186427

theorem tailTrace_206805 : CollatzResearch.WordTrace tailWord_206805 prefixEnd_206805 106190366753168608186427 := by
  unfold tailWord_206805
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542798015788279327181869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5028532010525519551454579 7542798015788279327181869)
  ·
    refine ⟨2828549255920604747693201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7542798015788279327181869 2828549255920604747693201)
    ·
      refine ⟨2121411941940453560769901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2828549255920604747693201 2121411941940453560769901)
      ·
        refine ⟨795529478227670085288713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2121411941940453560769901 795529478227670085288713)
        ·
          refine ⟨596647108670752563966535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795529478227670085288713 596647108670752563966535)
          ·
            refine ⟨894970663006128845949803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596647108670752563966535 894970663006128845949803)
            ·
              refine ⟨1342455994509193268924705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894970663006128845949803 1342455994509193268924705)
              ·
                refine ⟨1006841995881894951693529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342455994509193268924705 1006841995881894951693529)
                ·
                  refine ⟨755131496911421213770147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006841995881894951693529 755131496911421213770147)
                  ·
                    refine ⟨1132697245367131820655221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 755131496911421213770147 1132697245367131820655221)
                    ·
                      refine ⟨106190366753168608186427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1132697245367131820655221 106190366753168608186427)
                      ·
                        rfl

theorem cell23_206805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_206805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206805 prefixEnd_206805 := by exact prefixLift 206805
  have htrace : WordTrace (prefixWord ++ tailWord_206805) baseStart_206805 baseEnd_206805 := by
    simpa [prefixWord, tailWord_206805, baseEnd_206805] using wordTrace_append hprefix tailTrace_206805
  have hstable : (prefixWord ++ tailWord_206805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206805).length < 2 ^ (prefixWord ++ tailWord_206805).sum := by decide
  have hdescent : baseEnd_206805 < baseStart_206805 := by decide
  rcases family_descends (prefixWord ++ tailWord_206805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206806 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_206806 : Nat := 118140960795 + 206806 * 2 ^ 59
def prefixEnd_206806 : Nat := 4983230072969 + 3 ^ 40 * 206806 * 2
def baseEnd_206806 : Nat := 106190880233823104273923

theorem tailTrace_206806 : CollatzResearch.WordTrace tailWord_206806 prefixEnd_206806 106190880233823104273923 := by
  unfold tailWord_206806
  simp only [CollatzResearch.WordTrace]
  refine ⟨471427155549041031123017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5028556325856437665312181 471427155549041031123017)
  ·
    refine ⟨353570366661780773342263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 471427155549041031123017 353570366661780773342263)
    ·
      refine ⟨530355549992671160013395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353570366661780773342263 530355549992671160013395)
      ·
        refine ⟨795533324989006740020093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530355549992671160013395 795533324989006740020093)
        ·
          refine ⟨298324996870877527507535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795533324989006740020093 298324996870877527507535)
          ·
            refine ⟨447487495306316291261303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298324996870877527507535 447487495306316291261303)
            ·
              refine ⟨671231242959474436891955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447487495306316291261303 671231242959474436891955)
              ·
                refine ⟨1006846864439211655337933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671231242959474436891955 1006846864439211655337933)
                ·
                  refine ⟨377567574164704370751725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006846864439211655337933 377567574164704370751725)
                  ·
                    refine ⟨141587840311764139031897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377567574164704370751725 141587840311764139031897)
                    ·
                      refine ⟨106190880233823104273923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141587840311764139031897 106190880233823104273923)
                      ·
                        rfl

theorem cell23_206806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_206806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206806 prefixEnd_206806 := by exact prefixLift 206806
  have htrace : WordTrace (prefixWord ++ tailWord_206806) baseStart_206806 baseEnd_206806 := by
    simpa [prefixWord, tailWord_206806, baseEnd_206806] using wordTrace_append hprefix tailTrace_206806
  have hstable : (prefixWord ++ tailWord_206806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206806).length < 2 ^ (prefixWord ++ tailWord_206806).sum := by decide
  have hdescent : baseEnd_206806 < baseStart_206806 := by decide
  rcases family_descends (prefixWord ++ tailWord_206806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206808 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 9]
def baseStart_206808 : Nat := 118140960795 + 206808 * 2 ^ 59
def prefixEnd_206808 : Nat := 4983230072969 + 3 ^ 40 * 206808 * 2
def baseEnd_206808 : Nat := 11799100799459121827657

theorem tailTrace_206808 : CollatzResearch.WordTrace tailWord_206808 prefixEnd_206808 11799100799459121827657 := by
  unfold tailWord_206808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771453717388705419770539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5028604956518273893027385 3771453717388705419770539)
  ·
    refine ⟨5657180576083058129655809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3771453717388705419770539 5657180576083058129655809)
    ·
      refine ⟨4242885432062293597241857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5657180576083058129655809 4242885432062293597241857)
      ·
        refine ⟨3182164074046720197931393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4242885432062293597241857 3182164074046720197931393)
        ·
          refine ⟨2386623055535040148448545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182164074046720197931393 2386623055535040148448545)
          ·
            refine ⟨1789967291651280111336409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2386623055535040148448545 1789967291651280111336409)
            ·
              refine ⟨1342475468738460083502307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789967291651280111336409 1342475468738460083502307)
              ·
                refine ⟨2013713203107690125253461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342475468738460083502307 2013713203107690125253461)
                ·
                  refine ⟨11799100799459121827657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2013713203107690125253461 11799100799459121827657)
                  ·
                    rfl

theorem cell23_206808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 9].length) (baseStart_206808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206808 prefixEnd_206808 := by exact prefixLift 206808
  have htrace : WordTrace (prefixWord ++ tailWord_206808) baseStart_206808 baseEnd_206808 := by
    simpa [prefixWord, tailWord_206808, baseEnd_206808] using wordTrace_append hprefix tailTrace_206808
  have hstable : (prefixWord ++ tailWord_206808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206808).length < 2 ^ (prefixWord ++ tailWord_206808).sum := by decide
  have hdescent : baseEnd_206808 < baseStart_206808 := by decide
  rcases family_descends (prefixWord ++ tailWord_206808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206848 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_206848 : Nat := 118140960795 + 206848 * 2 ^ 59
def prefixEnd_206848 : Nat := 4983230072969 + 3 ^ 40 * 206848 * 2
def baseEnd_206848 : Nat := 106212446421311939948729

theorem tailTrace_206848 : CollatzResearch.WordTrace tailWord_206848 prefixEnd_206848 106212446421311939948729 := by
  unfold tailWord_206848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3772183177316248835498599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5029577569754998447331465 3772183177316248835498599)
  ·
    refine ⟨5658274765974373253247899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3772183177316248835498599 5658274765974373253247899)
    ·
      refine ⟨8487412148961559879871849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5658274765974373253247899 8487412148961559879871849)
      ·
        refine ⟨6365559111721169909903887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8487412148961559879871849 6365559111721169909903887)
        ·
          refine ⟨9548338667581754864855831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365559111721169909903887 9548338667581754864855831)
          ·
            refine ⟨14322508001372632297283747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9548338667581754864855831 14322508001372632297283747)
            ·
              refine ⟨21483762002058948445925621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14322508001372632297283747 21483762002058948445925621)
              ·
                refine ⟨2014102687693026416805527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21483762002058948445925621 2014102687693026416805527)
                ·
                  refine ⟨3021154031539539625208291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014102687693026416805527 3021154031539539625208291)
                  ·
                    refine ⟨4531731047309309437812437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3021154031539539625208291 4531731047309309437812437)
                    ·
                      refine ⟨106212446421311939948729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4531731047309309437812437 106212446421311939948729)
                      ·
                        rfl

theorem cell23_206848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_206848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206848 prefixEnd_206848 := by exact prefixLift 206848
  have htrace : WordTrace (prefixWord ++ tailWord_206848) baseStart_206848 baseEnd_206848 := by
    simpa [prefixWord, tailWord_206848, baseEnd_206848] using wordTrace_append hprefix tailTrace_206848
  have hstable : (prefixWord ++ tailWord_206848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206848).length < 2 ^ (prefixWord ++ tailWord_206848).sum := by decide
  have hdescent : baseEnd_206848 < baseStart_206848 := by decide
  rcases family_descends (prefixWord ++ tailWord_206848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206862 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_206862 : Nat := 118140960795 + 206862 * 2 ^ 59
def prefixEnd_206862 : Nat := 4983230072969 + 3 ^ 40 * 206862 * 2
def baseEnd_206862 : Nat := 106219635150474885173665

theorem tailTrace_206862 : CollatzResearch.WordTrace tailWord_206862 prefixEnd_206862 106219635150474885173665 := by
  unfold tailWord_206862
  simp only [CollatzResearch.WordTrace]
  refine ⟨943109622072722257750855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5029917984387852041337893 943109622072722257750855)
  ·
    refine ⟨1414664433109083386626283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943109622072722257750855 1414664433109083386626283)
    ·
      refine ⟨2121996649663625079939425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414664433109083386626283 2121996649663625079939425)
      ·
        refine ⟨1591497487247718809954569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2121996649663625079939425 1591497487247718809954569)
        ·
          refine ⟨1193623115435789107465927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591497487247718809954569 1193623115435789107465927)
          ·
            refine ⟨1790434673153683661198891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193623115435789107465927 1790434673153683661198891)
            ·
              refine ⟨2685652009730525491798337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790434673153683661198891 2685652009730525491798337)
              ·
                refine ⟨2014239007297894118848753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2685652009730525491798337 2014239007297894118848753)
                ·
                  refine ⟨1510679255473420589136565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2014239007297894118848753 1510679255473420589136565)
                  ·
                    refine ⟨141626180200633180231553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1510679255473420589136565 141626180200633180231553)
                    ·
                      refine ⟨106219635150474885173665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141626180200633180231553 106219635150474885173665)
                      ·
                        rfl

theorem cell23_206862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_206862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206862 prefixEnd_206862 := by exact prefixLift 206862
  have htrace : WordTrace (prefixWord ++ tailWord_206862) baseStart_206862 baseEnd_206862 := by
    simpa [prefixWord, tailWord_206862, baseEnd_206862] using wordTrace_append hprefix tailTrace_206862
  have hstable : (prefixWord ++ tailWord_206862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206862).length < 2 ^ (prefixWord ++ tailWord_206862).sum := by decide
  have hdescent : baseEnd_206862 < baseStart_206862 := by decide
  rcases family_descends (prefixWord ++ tailWord_206862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206875 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 4]
def baseStart_206875 : Nat := 118140960795 + 206875 * 2 ^ 59
def prefixEnd_206875 : Nat := 4983230072969 + 3 ^ 40 * 206875 * 2
def baseEnd_206875 : Nat := 106226310398983334311105

theorem tailTrace_206875 : CollatzResearch.WordTrace tailWord_206875 prefixEnd_206875 106226310398983334311105 := by
  unfold tailWord_206875
  simp only [CollatzResearch.WordTrace]
  refine ⟨7545351125534681282230079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5030234083689787521486719 7545351125534681282230079)
  ·
    refine ⟨11318026688302021923345119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7545351125534681282230079 11318026688302021923345119)
    ·
      refine ⟨16977040032453032885017679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11318026688302021923345119 16977040032453032885017679)
      ·
        refine ⟨25465560048679549327526519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16977040032453032885017679 25465560048679549327526519)
        ·
          refine ⟨38198340073019323991289779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25465560048679549327526519 38198340073019323991289779)
          ·
            refine ⟨57297510109528985986934669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38198340073019323991289779 57297510109528985986934669)
            ·
              refine ⟨21486566291073369745100501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57297510109528985986934669 21486566291073369745100501)
              ·
                refine ⟨503591397447032103400793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21486566291073369745100501 503591397447032103400793)
                ·
                  refine ⟨377693548085274077550595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503591397447032103400793 377693548085274077550595)
                  ·
                    refine ⟨566540322127911116325893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 377693548085274077550595 566540322127911116325893)
                    ·
                      refine ⟨106226310398983334311105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 566540322127911116325893 106226310398983334311105)
                      ·
                        rfl

theorem cell23_206875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 4].length) (baseStart_206875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206875 prefixEnd_206875 := by exact prefixLift 206875
  have htrace : WordTrace (prefixWord ++ tailWord_206875) baseStart_206875 baseEnd_206875 := by
    simpa [prefixWord, tailWord_206875, baseEnd_206875] using wordTrace_append hprefix tailTrace_206875
  have hstable : (prefixWord ++ tailWord_206875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206875).length < 2 ^ (prefixWord ++ tailWord_206875).sum := by decide
  have hdescent : baseEnd_206875 < baseStart_206875 := by decide
  rcases family_descends (prefixWord ++ tailWord_206875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206936 : List Nat := [2, 1, 2, 2, 1, 6, 1, 3, 1, 4]
def baseStart_206936 : Nat := 118140960795 + 206936 * 2 ^ 59
def prefixEnd_206936 : Nat := 4983230072969 + 3 ^ 40 * 206936 * 2
def baseEnd_206936 : Nat := 35419210906302531882775

theorem tailTrace_206936 : CollatzResearch.WordTrace tailWord_206936 prefixEnd_206936 35419210906302531882775 := by
  unfold tailWord_206936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773787989156844350100331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5031717318875792466800441 3773787989156844350100331)
  ·
    refine ⟨5660681983735266525150497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3773787989156844350100331 5660681983735266525150497)
    ·
      refine ⟨4245511487801449893862873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5660681983735266525150497 4245511487801449893862873)
      ·
        refine ⟨3184133615851087420397155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4245511487801449893862873 3184133615851087420397155)
        ·
          refine ⟨4776200423776631130595733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184133615851087420397155 4776200423776631130595733)
          ·
            refine ⟨223884394864529584246675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4776200423776631130595733 223884394864529584246675)
            ·
              refine ⟨335826592296794376370013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223884394864529584246675 335826592296794376370013)
              ·
                refine ⟨125934972111297891138755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335826592296794376370013 125934972111297891138755)
                ·
                  refine ⟨188902458166946836708133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125934972111297891138755 188902458166946836708133)
                  ·
                    refine ⟨35419210906302531882775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188902458166946836708133 35419210906302531882775)
                    ·
                      rfl

theorem cell23_206936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_206936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206936 prefixEnd_206936 := by exact prefixLift 206936
  have htrace : WordTrace (prefixWord ++ tailWord_206936) baseStart_206936 baseEnd_206936 := by
    simpa [prefixWord, tailWord_206936, baseEnd_206936] using wordTrace_append hprefix tailTrace_206936
  have hstable : (prefixWord ++ tailWord_206936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206936).length < 2 ^ (prefixWord ++ tailWord_206936).sum := by decide
  have hdescent : baseEnd_206936 < baseStart_206936 := by decide
  rcases family_descends (prefixWord ++ tailWord_206936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206945 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 5, 5]
def baseStart_206945 : Nat := 118140960795 + 206945 * 2 ^ 59
def prefixEnd_206945 : Nat := 4983230072969 + 3 ^ 40 * 206945 * 2
def baseEnd_206945 : Nat := 35420751348266020145261

theorem tailTrace_206945 : CollatzResearch.WordTrace tailWord_206945 prefixEnd_206945 35420751348266020145261 := by
  unfold tailWord_206945
  simp only [CollatzResearch.WordTrace]
  refine ⟨7547904235281083237278289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5031936156854055491518859 7547904235281083237278289)
  ·
    refine ⟨5660928176460812427958717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7547904235281083237278289 5660928176460812427958717)
    ·
      refine ⟨2122848066172804660484519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5660928176460812427958717 2122848066172804660484519)
      ·
        refine ⟨3184272099259206990726779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122848066172804660484519 3184272099259206990726779)
        ·
          refine ⟨4776408148888810486090169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184272099259206990726779 4776408148888810486090169)
          ·
            refine ⟨3582306111666607864567627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4776408148888810486090169 3582306111666607864567627)
            ·
              refine ⟨5373459167499911796851441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582306111666607864567627 5373459167499911796851441)
              ·
                refine ⟨4030094375624933847638581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5373459167499911796851441 4030094375624933847638581)
                ·
                  refine ⟨377821347714837548216117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4030094375624933847638581 377821347714837548216117)
                  ·
                    refine ⟨35420751348266020145261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377821347714837548216117 35420751348266020145261)
                    ·
                      rfl

theorem cell23_206945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_206945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206945 prefixEnd_206945 := by exact prefixLift 206945
  have htrace : WordTrace (prefixWord ++ tailWord_206945) baseStart_206945 baseEnd_206945 := by
    simpa [prefixWord, tailWord_206945, baseEnd_206945] using wordTrace_append hprefix tailTrace_206945
  have hstable : (prefixWord ++ tailWord_206945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206945).length < 2 ^ (prefixWord ++ tailWord_206945).sum := by decide
  have hdescent : baseEnd_206945 < baseStart_206945 := by decide
  rcases family_descends (prefixWord ++ tailWord_206945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206946 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_206946 : Nat := 118140960795 + 206946 * 2 ^ 59
def prefixEnd_206946 : Nat := 4983230072969 + 3 ^ 40 * 206946 * 2
def baseEnd_206946 : Nat := 106262767525452556523279

theorem tailTrace_206946 : CollatzResearch.WordTrace tailWord_206946 prefixEnd_206946 106262767525452556523279 := by
  unfold tailWord_206946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886985177069365102016173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5031960472184973605376461 1886985177069365102016173)
  ·
    refine ⟨707619441401011913256065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1886985177069365102016173 707619441401011913256065)
    ·
      refine ⟨530714581050758934942049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 707619441401011913256065 530714581050758934942049)
      ·
        refine ⟨398035935788069201206537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530714581050758934942049 398035935788069201206537)
        ·
          refine ⟨298526951841051900904903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398035935788069201206537 298526951841051900904903)
          ·
            refine ⟨447790427761577851357355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298526951841051900904903 447790427761577851357355)
            ·
              refine ⟨671685641642366777036033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447790427761577851357355 671685641642366777036033)
              ·
                refine ⟨503764231231775082777025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671685641642366777036033 503764231231775082777025)
                ·
                  refine ⟨377823173423831312082769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503764231231775082777025 377823173423831312082769)
                  ·
                    refine ⟨283367380067873484062077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 377823173423831312082769 283367380067873484062077)
                    ·
                      refine ⟨106262767525452556523279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283367380067873484062077 106262767525452556523279)
                      ·
                        rfl

theorem cell23_206946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_206946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206946 prefixEnd_206946 := by exact prefixLift 206946
  have htrace : WordTrace (prefixWord ++ tailWord_206946) baseStart_206946 baseEnd_206946 := by
    simpa [prefixWord, tailWord_206946, baseEnd_206946] using wordTrace_append hprefix tailTrace_206946
  have hstable : (prefixWord ++ tailWord_206946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206946).length < 2 ^ (prefixWord ++ tailWord_206946).sum := by decide
  have hdescent : baseEnd_206946 < baseStart_206946 := by decide
  rcases family_descends (prefixWord ++ tailWord_206946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206959 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 3]
def baseStart_206959 : Nat := 118140960795 + 206959 * 2 ^ 59
def prefixEnd_206959 : Nat := 4983230072969 + 3 ^ 40 * 206959 * 2
def baseEnd_206959 : Nat := 106269442773961005660719

theorem tailTrace_206959 : CollatzResearch.WordTrace tailWord_206959 prefixEnd_206959 106269442773961005660719 := by
  unfold tailWord_206959
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548414857230363628287931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5032276571486909085525287 7548414857230363628287931)
  ·
    refine ⟨11322622285845545442431897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7548414857230363628287931 11322622285845545442431897)
    ·
      refine ⟨8491966714384159081823923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11322622285845545442431897 8491966714384159081823923)
      ·
        refine ⟨12737950071576238622735885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491966714384159081823923 12737950071576238622735885)
        ·
          refine ⟨4776731276841089483525957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12737950071576238622735885 4776731276841089483525957)
          ·
            refine ⟨895637114407704278161117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4776731276841089483525957 895637114407704278161117)
            ·
              refine ⟨335863917902889104310419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895637114407704278161117 335863917902889104310419)
              ·
                refine ⟨503795876854333656465629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335863917902889104310419 503795876854333656465629)
                ·
                  refine ⟨188923453820375121174611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503795876854333656465629 188923453820375121174611)
                  ·
                    refine ⟨283385180730562681761917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188923453820375121174611 283385180730562681761917)
                    ·
                      refine ⟨106269442773961005660719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283385180730562681761917 106269442773961005660719)
                      ·
                        rfl

theorem cell23_206959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 3].length) (baseStart_206959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206959 prefixEnd_206959 := by exact prefixLift 206959
  have htrace : WordTrace (prefixWord ++ tailWord_206959) baseStart_206959 baseEnd_206959 := by
    simpa [prefixWord, tailWord_206959, baseEnd_206959] using wordTrace_append hprefix tailTrace_206959
  have hstable : (prefixWord ++ tailWord_206959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206959).length < 2 ^ (prefixWord ++ tailWord_206959).sum := by decide
  have hdescent : baseEnd_206959 < baseStart_206959 := by decide
  rcases family_descends (prefixWord ++ tailWord_206959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206966 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_206966 : Nat := 118140960795 + 206966 * 2 ^ 59
def prefixEnd_206966 : Nat := 4983230072969 + 3 ^ 40 * 206966 * 2
def baseEnd_206966 : Nat := 11808115237615830919243

theorem tailTrace_206966 : CollatzResearch.WordTrace tailWord_206966 prefixEnd_206966 11808115237615830919243 := by
  unfold tailWord_206966
  simp only [CollatzResearch.WordTrace]
  refine ⟨471791885512812738987047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5032446778803335882528501 471791885512812738987047)
  ·
    refine ⟨707687828269219108480571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 471791885512812738987047 707687828269219108480571)
    ·
      refine ⟨1061531742403828662720857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707687828269219108480571 1061531742403828662720857)
      ·
        refine ⟨796148806802871497040643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061531742403828662720857 796148806802871497040643)
        ·
          refine ⟨1194223210204307245560965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796148806802871497040643 1194223210204307245560965)
          ·
            refine ⟨223916851913307608542681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1194223210204307245560965 223916851913307608542681)
            ·
              refine ⟨167937638934980706407011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223916851913307608542681 167937638934980706407011)
              ·
                refine ⟨251906458402471059610517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167937638934980706407011 251906458402471059610517)
                ·
                  refine ⟨11808115237615830919243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 251906458402471059610517 11808115237615830919243)
                  ·
                    rfl

theorem cell23_206966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_206966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206966 prefixEnd_206966 := by exact prefixLift 206966
  have htrace : WordTrace (prefixWord ++ tailWord_206966) baseStart_206966 baseEnd_206966 := by
    simpa [prefixWord, tailWord_206966, baseEnd_206966] using wordTrace_append hprefix tailTrace_206966
  have hstable : (prefixWord ++ tailWord_206966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206966).length < 2 ^ (prefixWord ++ tailWord_206966).sum := by decide
  have hdescent : baseEnd_206966 < baseStart_206966 := by decide
  rcases family_descends (prefixWord ++ tailWord_206966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206979 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 1, 5]
def baseStart_206979 : Nat := 118140960795 + 206979 * 2 ^ 59
def prefixEnd_206979 : Nat := 4983230072969 + 3 ^ 40 * 206979 * 2
def baseEnd_206979 : Nat := 35426570795683642470209

theorem tailTrace_206979 : CollatzResearch.WordTrace tailWord_206979 prefixEnd_206979 35426570795683642470209 := by
  unfold tailWord_206979
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549144317157907044015991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5032762878105271362677327 7549144317157907044015991)
  ·
    refine ⟨11323716475736860566023987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7549144317157907044015991 11323716475736860566023987)
    ·
      refine ⟨16985574713605290849035981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11323716475736860566023987 16985574713605290849035981)
      ·
        refine ⟨6369590517601984068388493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16985574713605290849035981 6369590517601984068388493)
        ·
          refine ⟨2388596444100744025645685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6369590517601984068388493 2388596444100744025645685)
          ·
            refine ⟨223930916634444752404283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2388596444100744025645685 223930916634444752404283)
            ·
              refine ⟨335896374951667128606425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223930916634444752404283 335896374951667128606425)
              ·
                refine ⟨251922281213750346454819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335896374951667128606425 251922281213750346454819)
                ·
                  refine ⟨377883421820625519682229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251922281213750346454819 377883421820625519682229)
                  ·
                    refine ⟨35426570795683642470209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377883421820625519682229 35426570795683642470209)
                    ·
                      rfl

theorem cell23_206979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 5].length) (baseStart_206979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206979 prefixEnd_206979 := by exact prefixLift 206979
  have htrace : WordTrace (prefixWord ++ tailWord_206979) baseStart_206979 baseEnd_206979 := by
    simpa [prefixWord, tailWord_206979, baseEnd_206979] using wordTrace_append hprefix tailTrace_206979
  have hstable : (prefixWord ++ tailWord_206979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206979).length < 2 ^ (prefixWord ++ tailWord_206979).sum := by decide
  have hdescent : baseEnd_206979 < baseStart_206979 := by decide
  rcases family_descends (prefixWord ++ tailWord_206979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206986 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_206986 : Nat := 118140960795 + 206986 * 2 ^ 59
def prefixEnd_206986 : Nat := 4983230072969 + 3 ^ 40 * 206986 * 2
def baseEnd_206986 : Nat := 106283306751632400023095

theorem tailTrace_206986 : CollatzResearch.WordTrace tailWord_206986 prefixEnd_206986 106283306751632400023095 := by
  unfold tailWord_206986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887349907033136809880203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5032933085421698159680541 1887349907033136809880203)
  ·
    refine ⟨2831024860549705214820305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887349907033136809880203 2831024860549705214820305)
    ·
      refine ⟨2123268645412278911115229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2831024860549705214820305 2123268645412278911115229)
      ·
        refine ⟨796225742029604591668211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2123268645412278911115229 796225742029604591668211)
        ·
          refine ⟨1194338613044406887502317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796225742029604591668211 1194338613044406887502317)
          ·
            refine ⟨447876979891652582813369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1194338613044406887502317 447876979891652582813369)
            ·
              refine ⟨335907734918739437110027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447876979891652582813369 335907734918739437110027)
              ·
                refine ⟨503861602378109155665041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335907734918739437110027 503861602378109155665041)
                ·
                  refine ⟨377896201783581866748781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503861602378109155665041 377896201783581866748781)
                  ·
                    refine ⟨141711075668843200030793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377896201783581866748781 141711075668843200030793)
                    ·
                      refine ⟨106283306751632400023095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141711075668843200030793 106283306751632400023095)
                      ·
                        rfl

theorem cell23_206986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_206986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_206986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_206986 prefixEnd_206986 := by exact prefixLift 206986
  have htrace : WordTrace (prefixWord ++ tailWord_206986) baseStart_206986 baseEnd_206986 := by
    simpa [prefixWord, tailWord_206986, baseEnd_206986] using wordTrace_append hprefix tailTrace_206986
  have hstable : (prefixWord ++ tailWord_206986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206986).length < 2 ^ (prefixWord ++ tailWord_206986).sum := by decide
  have hdescent : baseEnd_206986 < baseStart_206986 := by decide
  rcases family_descends (prefixWord ++ tailWord_206986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207005 : List Nat := [1, 4, 2, 1, 1, 14]
def baseStart_207005 : Nat := 118140960795 + 207005 * 2 ^ 59
def prefixEnd_207005 : Nat := 4983230072969 + 3 ^ 40 * 207005 * 2
def baseEnd_207005 : Nat := 437420011868591875249

theorem tailTrace_207005 : CollatzResearch.WordTrace tailWord_207005 prefixEnd_207005 437420011868591875249 := by
  unfold tailWord_207005
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550092615063713484462469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5033395076709142322974979 7550092615063713484462469)
  ·
    refine ⟨1415642365324446278336713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7550092615063713484462469 1415642365324446278336713)
    ·
      refine ⟨1061731773993334708752535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1415642365324446278336713 1061731773993334708752535)
      ·
        refine ⟨1592597660990002063128803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061731773993334708752535 1592597660990002063128803)
        ·
          refine ⟨2388896491485003094693205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592597660990002063128803 2388896491485003094693205)
          ·
            refine ⟨437420011868591875249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 2388896491485003094693205 437420011868591875249)
            ·
              rfl

theorem cell23_207005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 14].length) (baseStart_207005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207005 prefixEnd_207005 := by exact prefixLift 207005
  have htrace : WordTrace (prefixWord ++ tailWord_207005) baseStart_207005 baseEnd_207005 := by
    simpa [prefixWord, tailWord_207005, baseEnd_207005] using wordTrace_append hprefix tailTrace_207005
  have hstable : (prefixWord ++ tailWord_207005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207005).length < 2 ^ (prefixWord ++ tailWord_207005).sum := by decide
  have hdescent : baseEnd_207005 < baseStart_207005 := by decide
  rcases family_descends (prefixWord ++ tailWord_207005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207009 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 2, 4]
def baseStart_207009 : Nat := 118140960795 + 207009 * 2 ^ 59
def prefixEnd_207009 : Nat := 4983230072969 + 3 ^ 40 * 207009 * 2
def baseEnd_207009 : Nat := 35431705602228603345163

theorem tailTrace_207009 : CollatzResearch.WordTrace tailWord_207009 prefixEnd_207009 35431705602228603345163 := by
  unfold tailWord_207009
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550238507049222167608081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5033492338032814778405387 7550238507049222167608081)
  ·
    refine ⟨5662678880286916625706061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7550238507049222167608081 5662678880286916625706061)
    ·
      refine ⟨2123504580107593734639773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5662678880286916625706061 2123504580107593734639773)
      ·
        refine ⟨796314217540347650489915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2123504580107593734639773 796314217540347650489915)
        ·
          refine ⟨1194471326310521475734873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796314217540347650489915 1194471326310521475734873)
          ·
            refine ⟨895853494732891106801155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194471326310521475734873 895853494732891106801155)
            ·
              refine ⟨1343780242099336660201733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895853494732891106801155 1343780242099336660201733)
              ·
                refine ⟨251958795393625623787825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1343780242099336660201733 251958795393625623787825)
                ·
                  refine ⟨188969096545219217840869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251958795393625623787825 188969096545219217840869)
                  ·
                    refine ⟨35431705602228603345163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188969096545219217840869 35431705602228603345163)
                    ·
                      rfl

theorem cell23_207009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_207009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207009 prefixEnd_207009 := by exact prefixLift 207009
  have htrace : WordTrace (prefixWord ++ tailWord_207009) baseStart_207009 baseEnd_207009 := by
    simpa [prefixWord, tailWord_207009, baseEnd_207009] using wordTrace_append hprefix tailTrace_207009
  have hstable : (prefixWord ++ tailWord_207009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207009).length < 2 ^ (prefixWord ++ tailWord_207009).sum := by decide
  have hdescent : baseEnd_207009 < baseStart_207009 := by decide
  rcases family_descends (prefixWord ++ tailWord_207009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207010 : List Nat := [3, 3, 1, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_207010 : Nat := 118140960795 + 207010 * 2 ^ 59
def prefixEnd_207010 : Nat := 4983230072969 + 3 ^ 40 * 207010 * 2
def baseEnd_207010 : Nat := 106295630287340306122985

theorem tailTrace_207010 : CollatzResearch.WordTrace tailWord_207010 prefixEnd_207010 106295630287340306122985 := by
  unfold tailWord_207010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887568745011399834598621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5033516653363732892262989 1887568745011399834598621)
  ·
    refine ⟨707838279379274937974483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1887568745011399834598621 707838279379274937974483)
    ·
      refine ⟨1061757419068912406961725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707838279379274937974483 1061757419068912406961725)
      ·
        refine ⟨398159032150842152610647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1061757419068912406961725 398159032150842152610647)
        ·
          refine ⟨597238548226263228915971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398159032150842152610647 597238548226263228915971)
          ·
            refine ⟨895857822339394843373957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597238548226263228915971 895857822339394843373957)
            ·
              refine ⟨167973341688636533132617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 895857822339394843373957 167973341688636533132617)
              ·
                refine ⟨125980006266477399849463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167973341688636533132617 125980006266477399849463)
                ·
                  refine ⟨188970009399716099774195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125980006266477399849463 188970009399716099774195)
                  ·
                    refine ⟨283455014099574149661293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188970009399716099774195 283455014099574149661293)
                    ·
                      refine ⟨106295630287340306122985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283455014099574149661293 106295630287340306122985)
                      ·
                        rfl

theorem cell23_207010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_207010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207010 prefixEnd_207010 := by exact prefixLift 207010
  have htrace : WordTrace (prefixWord ++ tailWord_207010) baseStart_207010 baseEnd_207010 := by
    simpa [prefixWord, tailWord_207010, baseEnd_207010] using wordTrace_append hprefix tailTrace_207010
  have hstable : (prefixWord ++ tailWord_207010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207010).length < 2 ^ (prefixWord ++ tailWord_207010).sum := by decide
  have hdescent : baseEnd_207010 < baseStart_207010 := by decide
  rcases family_descends (prefixWord ++ tailWord_207010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207035 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 2, 7]
def baseStart_207035 : Nat := 118140960795 + 207035 * 2 ^ 59
def prefixEnd_207035 : Nat := 4983230072969 + 3 ^ 40 * 207035 * 2
def baseEnd_207035 : Nat := 35436155767900902770123

theorem tailTrace_207035 : CollatzResearch.WordTrace tailWord_207035 prefixEnd_207035 35436155767900902770123 := by
  unfold tailWord_207035
  simp only [CollatzResearch.WordTrace]
  refine ⟨7551186804955028608054559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5034124536636685738703039 7551186804955028608054559)
  ·
    refine ⟨11326780207432542912081839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7551186804955028608054559 11326780207432542912081839)
    ·
      refine ⟨16990170311148814368122759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11326780207432542912081839 16990170311148814368122759)
      ·
        refine ⟨25485255466723221552184139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990170311148814368122759 25485255466723221552184139)
        ·
          refine ⟨38227883200084832328276209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25485255466723221552184139 38227883200084832328276209)
          ·
            refine ⟨28670912400063624246207157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38227883200084832328276209 28670912400063624246207157)
            ·
              refine ⟨2687898037505964773081921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28670912400063624246207157 2687898037505964773081921)
              ·
                refine ⟨2015923528129473579811441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687898037505964773081921 2015923528129473579811441)
                ·
                  refine ⟨1511942646097105184858581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2015923528129473579811441 1511942646097105184858581)
                  ·
                    refine ⟨35436155767900902770123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1511942646097105184858581 35436155767900902770123)
                    ·
                      rfl

theorem cell23_207035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_207035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207035 prefixEnd_207035 := by exact prefixLift 207035
  have htrace : WordTrace (prefixWord ++ tailWord_207035) baseStart_207035 baseEnd_207035 := by
    simpa [prefixWord, tailWord_207035, baseEnd_207035] using wordTrace_append hprefix tailTrace_207035
  have hstable : (prefixWord ++ tailWord_207035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207035).length < 2 ^ (prefixWord ++ tailWord_207035).sum := by decide
  have hdescent : baseEnd_207035 < baseStart_207035 := by decide
  rcases family_descends (prefixWord ++ tailWord_207035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207066 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_207066 : Nat := 118140960795 + 207066 * 2 ^ 59
def prefixEnd_207066 : Nat := 4983230072969 + 3 ^ 40 * 207066 * 2
def baseEnd_207066 : Nat := 106324385203992087022727

theorem tailTrace_207066 : CollatzResearch.WordTrace tailWord_207066 prefixEnd_207066 106324385203992087022727 := by
  unfold tailWord_207066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888079366960680225608263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5034878311895147268288701 1888079366960680225608263)
  ·
    refine ⟨2832119050441020338412395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888079366960680225608263 2832119050441020338412395)
    ·
      refine ⟨4248178575661530507618593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832119050441020338412395 4248178575661530507618593)
      ·
        refine ⟨3186133931746147880713945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4248178575661530507618593 3186133931746147880713945)
        ·
          refine ⟨2389600448809610910535459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3186133931746147880713945 2389600448809610910535459)
          ·
            refine ⟨3584400673214416365803189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389600448809610910535459 3584400673214416365803189)
            ·
              refine ⟨336037563113851534294049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3584400673214416365803189 336037563113851534294049)
              ·
                refine ⟨252028172335388650720537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336037563113851534294049 252028172335388650720537)
                ·
                  refine ⟨189021129251541488040403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252028172335388650720537 189021129251541488040403)
                  ·
                    refine ⟨283531693877312232060605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189021129251541488040403 283531693877312232060605)
                    ·
                      refine ⟨106324385203992087022727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283531693877312232060605 106324385203992087022727)
                      ·
                        rfl

theorem cell23_207066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_207066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207066 prefixEnd_207066 := by exact prefixLift 207066
  have htrace : WordTrace (prefixWord ++ tailWord_207066) baseStart_207066 baseEnd_207066 := by
    simpa [prefixWord, tailWord_207066, baseEnd_207066] using wordTrace_append hprefix tailTrace_207066
  have hstable : (prefixWord ++ tailWord_207066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207066).length < 2 ^ (prefixWord ++ tailWord_207066).sum := by decide
  have hdescent : baseEnd_207066 < baseStart_207066 := by decide
  rcases family_descends (prefixWord ++ tailWord_207066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207082 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_207082 : Nat := 118140960795 + 207082 * 2 ^ 59
def prefixEnd_207082 : Nat := 4983230072969 + 3 ^ 40 * 207082 * 2
def baseEnd_207082 : Nat := 35444200298154674807551

theorem tailTrace_207082 : CollatzResearch.WordTrace tailWord_207082 prefixEnd_207082 35444200298154674807551 := by
  unfold tailWord_207082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888225258946188908753875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5035267357189837090010333 1888225258946188908753875)
  ·
    refine ⟨2832337888419283363130813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888225258946188908753875 2832337888419283363130813)
    ·
      refine ⟨1062126708157231261174055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2832337888419283363130813 1062126708157231261174055)
      ·
        refine ⟨1593190062235846891761083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062126708157231261174055 1593190062235846891761083)
        ·
          refine ⟨2389785093353770337641625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593190062235846891761083 2389785093353770337641625)
          ·
            refine ⟨1792338820015327753231219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2389785093353770337641625 1792338820015327753231219)
            ·
              refine ⟨2688508230022991629846829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792338820015327753231219 2688508230022991629846829)
              ·
                refine ⟨1008190586258621861192561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2688508230022991629846829 1008190586258621861192561)
                ·
                  refine ⟨756142939693966395894421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1008190586258621861192561 756142939693966395894421)
                  ·
                    refine ⟨35444200298154674807551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 756142939693966395894421 35444200298154674807551)
                    ·
                      rfl

theorem cell23_207082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_207082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207082 prefixEnd_207082 := by exact prefixLift 207082
  have htrace : WordTrace (prefixWord ++ tailWord_207082) baseStart_207082 baseEnd_207082 := by
    simpa [prefixWord, tailWord_207082, baseEnd_207082] using wordTrace_append hprefix tailTrace_207082
  have hstable : (prefixWord ++ tailWord_207082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207082).length < 2 ^ (prefixWord ++ tailWord_207082).sum := by decide
  have hdescent : baseEnd_207082 < baseStart_207082 := by decide
  rcases family_descends (prefixWord ++ tailWord_207082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207140 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_207140 : Nat := 118140960795 + 207140 * 2 ^ 59
def prefixEnd_207140 : Nat := 4983230072969 + 3 ^ 40 * 207140 * 2
def baseEnd_207140 : Nat := 106362382772424797497387

theorem tailTrace_207140 : CollatzResearch.WordTrace tailWord_207140 prefixEnd_207140 106362382772424797497387 := by
  unfold tailWord_207140
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777508234787315770313437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5036677646383087693751249 3777508234787315770313437)
  ·
    refine ⟨1416565588045243413867539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3777508234787315770313437 1416565588045243413867539)
    ·
      refine ⟨2124848382067865120801309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1416565588045243413867539 2124848382067865120801309)
      ·
        refine ⟨796818143275449420300491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2124848382067865120801309 796818143275449420300491)
        ·
          refine ⟨1195227214913174130450737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796818143275449420300491 1195227214913174130450737)
          ·
            refine ⟨896420411184880597838053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1195227214913174130450737 896420411184880597838053)
            ·
              refine ⟨168078827097165112094635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 896420411184880597838053 168078827097165112094635)
              ·
                refine ⟨252118240645747668141953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168078827097165112094635 252118240645747668141953)
                ·
                  refine ⟨189088680484310751106465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252118240645747668141953 189088680484310751106465)
                  ·
                    refine ⟨141816510363233063329849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189088680484310751106465 141816510363233063329849)
                    ·
                      refine ⟨106362382772424797497387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141816510363233063329849 106362382772424797497387)
                      ·
                        rfl

theorem cell23_207140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_207140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207140 prefixEnd_207140 := by exact prefixLift 207140
  have htrace : WordTrace (prefixWord ++ tailWord_207140) baseStart_207140 baseEnd_207140 := by
    simpa [prefixWord, tailWord_207140, baseEnd_207140] using wordTrace_append hprefix tailTrace_207140
  have hstable : (prefixWord ++ tailWord_207140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207140).length < 2 ^ (prefixWord ++ tailWord_207140).sum := by decide
  have hdescent : baseEnd_207140 < baseStart_207140 := by decide
  rcases family_descends (prefixWord ++ tailWord_207140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207192 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_207192 : Nat := 118140960795 + 207192 * 2 ^ 59
def prefixEnd_207192 : Nat := 4983230072969 + 3 ^ 40 * 207192 * 2
def baseEnd_207192 : Nat := 106389083766458594047147

theorem tailTrace_207192 : CollatzResearch.WordTrace tailWord_207192 prefixEnd_207192 106389083766458594047147 := by
  unfold tailWord_207192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778456532693122210759915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5037942043590829614346553 3778456532693122210759915)
  ·
    refine ⟨5667684799039683316139873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3778456532693122210759915 5667684799039683316139873)
    ·
      refine ⟨4250763599279762487104905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5667684799039683316139873 4250763599279762487104905)
      ·
        refine ⟨3188072699459821865328679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4250763599279762487104905 3188072699459821865328679)
        ·
          refine ⟨4782109049189732797993019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188072699459821865328679 4782109049189732797993019)
          ·
            refine ⟨7173163573784599196989529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782109049189732797993019 7173163573784599196989529)
            ·
              refine ⟨5379872680338449397742147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173163573784599196989529 5379872680338449397742147)
              ·
                refine ⟨8069809020507674096613221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379872680338449397742147 8069809020507674096613221)
                ·
                  refine ⟨1513089191345188893114979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8069809020507674096613221 1513089191345188893114979)
                  ·
                    refine ⟨2269633787017783339672469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1513089191345188893114979 2269633787017783339672469)
                    ·
                      refine ⟨106389083766458594047147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2269633787017783339672469 106389083766458594047147)
                      ·
                        rfl

theorem cell23_207192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_207192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207192 prefixEnd_207192 := by exact prefixLift 207192
  have htrace : WordTrace (prefixWord ++ tailWord_207192) baseStart_207192 baseEnd_207192 := by
    simpa [prefixWord, tailWord_207192, baseEnd_207192] using wordTrace_append hprefix tailTrace_207192
  have hstable : (prefixWord ++ tailWord_207192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207192).length < 2 ^ (prefixWord ++ tailWord_207192).sum := by decide
  have hdescent : baseEnd_207192 < baseStart_207192 := by decide
  rcases family_descends (prefixWord ++ tailWord_207192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207199 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 3]
def baseStart_207199 : Nat := 118140960795 + 207199 * 2 ^ 59
def prefixEnd_207199 : Nat := 4983230072969 + 3 ^ 40 * 207199 * 2
def baseEnd_207199 : Nat := 106392678131040066659615

theorem tailTrace_207199 : CollatzResearch.WordTrace tailWord_207199 prefixEnd_207199 106392678131040066659615 := by
  unfold tailWord_207199
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557168376360884617024651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5038112250907256411349767 7557168376360884617024651)
  ·
    refine ⟨11335752564541326925536977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7557168376360884617024651 11335752564541326925536977)
    ·
      refine ⟨8501814423405995194152733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11335752564541326925536977 8501814423405995194152733)
      ·
        refine ⟨3188180408777248197807275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8501814423405995194152733 3188180408777248197807275)
        ·
          refine ⟨4782270613165872296710913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188180408777248197807275 4782270613165872296710913)
          ·
            refine ⟨3586702959874404222533185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4782270613165872296710913 3586702959874404222533185)
            ·
              refine ⟨2690027219905803166899889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586702959874404222533185 2690027219905803166899889)
              ·
                refine ⟨2017520414929352375174917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690027219905803166899889 2017520414929352375174917)
                ·
                  refine ⟨378285077799253570345297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017520414929352375174917 378285077799253570345297)
                  ·
                    refine ⟨283713808349440177758973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 378285077799253570345297 283713808349440177758973)
                    ·
                      refine ⟨106392678131040066659615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283713808349440177758973 106392678131040066659615)
                      ·
                        rfl

theorem cell23_207199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_207199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207199 prefixEnd_207199 := by exact prefixLift 207199
  have htrace : WordTrace (prefixWord ++ tailWord_207199) baseStart_207199 baseEnd_207199 := by
    simpa [prefixWord, tailWord_207199, baseEnd_207199] using wordTrace_append hprefix tailTrace_207199
  have hstable : (prefixWord ++ tailWord_207199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207199).length < 2 ^ (prefixWord ++ tailWord_207199).sum := by decide
  have hdescent : baseEnd_207199 < baseStart_207199 := by decide
  rcases family_descends (prefixWord ++ tailWord_207199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207216 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3]
def baseStart_207216 : Nat := 118140960795 + 207216 * 2 ^ 59
def prefixEnd_207216 : Nat := 4983230072969 + 3 ^ 40 * 207216 * 2
def baseEnd_207216 : Nat := 106401407302166500147037

theorem tailTrace_207216 : CollatzResearch.WordTrace tailWord_207216 prefixEnd_207216 106401407302166500147037 := by
  unfold tailWord_207216
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778894208649648260196751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5038525611532864346929001 3778894208649648260196751)
  ·
    refine ⟨5668341312974472390295127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3778894208649648260196751 5668341312974472390295127)
    ·
      refine ⟨8502511969461708585442691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5668341312974472390295127 8502511969461708585442691)
      ·
        refine ⟨12753767954192562878164037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8502511969461708585442691 12753767954192562878164037)
        ·
          refine ⟨2391331491411105539655757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12753767954192562878164037 2391331491411105539655757)
          ·
            refine ⟨896749309279164577370909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2391331491411105539655757 896749309279164577370909)
            ·
              refine ⟨336280990979686716514091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 896749309279164577370909 336280990979686716514091)
              ·
                refine ⟨504421486469530074771137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336280990979686716514091 504421486469530074771137)
                ·
                  refine ⟨378316114852147556078353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504421486469530074771137 378316114852147556078353)
                  ·
                    refine ⟨283737086139110667058765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 378316114852147556078353 283737086139110667058765)
                    ·
                      refine ⟨106401407302166500147037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283737086139110667058765 106401407302166500147037)
                      ·
                        rfl

theorem cell23_207216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_207216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207216 prefixEnd_207216 := by exact prefixLift 207216
  have htrace : WordTrace (prefixWord ++ tailWord_207216) baseStart_207216 baseEnd_207216 := by
    simpa [prefixWord, tailWord_207216, baseEnd_207216] using wordTrace_append hprefix tailTrace_207216
  have hstable : (prefixWord ++ tailWord_207216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207216).length < 2 ^ (prefixWord ++ tailWord_207216).sum := by decide
  have hdescent : baseEnd_207216 < baseStart_207216 := by decide
  rcases family_descends (prefixWord ++ tailWord_207216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207296 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 2, 4]
def baseStart_207296 : Nat := 118140960795 + 207296 * 2 ^ 59
def prefixEnd_207296 : Nat := 4983230072969 + 3 ^ 40 * 207296 * 2
def baseEnd_207296 : Nat := 35480828584842062382223

theorem tailTrace_207296 : CollatzResearch.WordTrace tailWord_207296 prefixEnd_207296 35480828584842062382223 := by
  unfold tailWord_207296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780353128504735091652871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5040470838006313455537161 3780353128504735091652871)
  ·
    refine ⟨5670529692757102637479307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3780353128504735091652871 5670529692757102637479307)
    ·
      refine ⟨8505794539135653956218961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670529692757102637479307 8505794539135653956218961)
      ·
        refine ⟨6379345904351740467164221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8505794539135653956218961 6379345904351740467164221)
        ·
          refine ⟨2392254714131902675186583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6379345904351740467164221 2392254714131902675186583)
          ·
            refine ⟨3588382071197854012779875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392254714131902675186583 3588382071197854012779875)
            ·
              refine ⟨5382573106796781019169813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588382071197854012779875 5382573106796781019169813)
              ·
                refine ⟨252308114381099110273585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5382573106796781019169813 252308114381099110273585)
                ·
                  refine ⟨189231085785824332705189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252308114381099110273585 189231085785824332705189)
                  ·
                    refine ⟨35480828584842062382223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189231085785824332705189 35480828584842062382223)
                    ·
                      rfl

theorem cell23_207296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_207296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207296 prefixEnd_207296 := by exact prefixLift 207296
  have htrace : WordTrace (prefixWord ++ tailWord_207296) baseStart_207296 baseEnd_207296 := by
    simpa [prefixWord, tailWord_207296, baseEnd_207296] using wordTrace_append hprefix tailTrace_207296
  have hstable : (prefixWord ++ tailWord_207296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207296).length < 2 ^ (prefixWord ++ tailWord_207296).sum := by decide
  have hdescent : baseEnd_207296 < baseStart_207296 := by decide
  rcases family_descends (prefixWord ++ tailWord_207296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207306 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_207306 : Nat := 118140960795 + 207306 * 2 ^ 59
def prefixEnd_207306 : Nat := 4983230072969 + 3 ^ 40 * 207306 * 2
def baseEnd_207306 : Nat := 106447620561071148021623

theorem tailTrace_207306 : CollatzResearch.WordTrace tailWord_207306 prefixEnd_207306 106447620561071148021623 := by
  unfold tailWord_207306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890267746743310472792443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5040713991315494594113181 1890267746743310472792443)
  ·
    refine ⟨2835401620114965709188665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1890267746743310472792443 2835401620114965709188665)
    ·
      refine ⟨2126551215086224281891499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2835401620114965709188665 2126551215086224281891499)
      ·
        refine ⟨3189826822629336422837249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126551215086224281891499 3189826822629336422837249)
        ·
          refine ⟨2392370116972002317127937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189826822629336422837249 2392370116972002317127937)
          ·
            refine ⟨1794277587729001737845953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392370116972002317127937 1794277587729001737845953)
            ·
              refine ⟨1345708190796751303384465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794277587729001737845953 1345708190796751303384465)
              ·
                refine ⟨1009281143097563477538349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345708190796751303384465 1009281143097563477538349)
                ·
                  refine ⟨378480428661586304076881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009281143097563477538349 378480428661586304076881)
                  ·
                    refine ⟨283860321496189728057661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 378480428661586304076881 283860321496189728057661)
                    ·
                      refine ⟨106447620561071148021623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283860321496189728057661 106447620561071148021623)
                      ·
                        rfl

theorem cell23_207306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_207306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207306 prefixEnd_207306 := by exact prefixLift 207306
  have htrace : WordTrace (prefixWord ++ tailWord_207306) baseStart_207306 baseEnd_207306 := by
    simpa [prefixWord, tailWord_207306, baseEnd_207306] using wordTrace_append hprefix tailTrace_207306
  have hstable : (prefixWord ++ tailWord_207306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207306).length < 2 ^ (prefixWord ++ tailWord_207306).sum := by decide
  have hdescent : baseEnd_207306 < baseStart_207306 := by decide
  rcases family_descends (prefixWord ++ tailWord_207306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207316 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_207316 : Nat := 118140960795 + 207316 * 2 ^ 59
def prefixEnd_207316 : Nat := 4983230072969 + 3 ^ 40 * 207316 * 2
def baseEnd_207316 : Nat := 106452755367616108896577

theorem tailTrace_207316 : CollatzResearch.WordTrace tailWord_207316 prefixEnd_207316 106452755367616108896577 := by
  unfold tailWord_207316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780717858468506799516901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5040957144624675732689201 3780717858468506799516901)
  ·
    refine ⟨708884598462845024909419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3780717858468506799516901 708884598462845024909419)
    ·
      refine ⟨1063326897694267537364129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 708884598462845024909419 1063326897694267537364129)
      ·
        refine ⟨797495173270700653023097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1063326897694267537364129 797495173270700653023097)
        ·
          refine ⟨598121379953025489767323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797495173270700653023097 598121379953025489767323)
          ·
            refine ⟨897182069929538234650985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598121379953025489767323 897182069929538234650985)
            ·
              refine ⟨672886552447153675988239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897182069929538234650985 672886552447153675988239)
              ·
                refine ⟨1009329828670730513982359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672886552447153675988239 1009329828670730513982359)
                ·
                  refine ⟨1513994743006095770973539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009329828670730513982359 1513994743006095770973539)
                  ·
                    refine ⟨2270992114509143656460309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1513994743006095770973539 2270992114509143656460309)
                    ·
                      refine ⟨106452755367616108896577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2270992114509143656460309 106452755367616108896577)
                      ·
                        rfl

theorem cell23_207316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_207316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207316 prefixEnd_207316 := by exact prefixLift 207316
  have htrace : WordTrace (prefixWord ++ tailWord_207316) baseStart_207316 baseEnd_207316 := by
    simpa [prefixWord, tailWord_207316, baseEnd_207316] using wordTrace_append hprefix tailTrace_207316
  have hstable : (prefixWord ++ tailWord_207316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207316).length < 2 ^ (prefixWord ++ tailWord_207316).sum := by decide
  have hdescent : baseEnd_207316 < baseStart_207316 := by decide
  rcases family_descends (prefixWord ++ tailWord_207316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207330 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_207330 : Nat := 118140960795 + 207330 * 2 ^ 59
def prefixEnd_207330 : Nat := 4983230072969 + 3 ^ 40 * 207330 * 2
def baseEnd_207330 : Nat := 35486648032259684707171

theorem tailTrace_207330 : CollatzResearch.WordTrace tailWord_207330 prefixEnd_207330 35486648032259684707171 := by
  unfold tailWord_207330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890486584721573497510861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5041297559257529326695629 1890486584721573497510861)
  ·
    refine ⟨708932469270590061566573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1890486584721573497510861 708932469270590061566573)
    ·
      refine ⟨265849675976471273087465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 708932469270590061566573 265849675976471273087465)
      ·
        refine ⟨199387256982353454815599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265849675976471273087465 199387256982353454815599)
        ·
          refine ⟨299080885473530182223399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199387256982353454815599 299080885473530182223399)
          ·
            refine ⟨448621328210295273335099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299080885473530182223399 448621328210295273335099)
            ·
              refine ⟨672931992315442910002649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448621328210295273335099 672931992315442910002649)
              ·
                refine ⟨504698994236582182501987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672931992315442910002649 504698994236582182501987)
                ·
                  refine ⟨757048491354873273752981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504698994236582182501987 757048491354873273752981)
                  ·
                    refine ⟨35486648032259684707171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 757048491354873273752981 35486648032259684707171)
                    ·
                      rfl

theorem cell23_207330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_207330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207330 prefixEnd_207330 := by exact prefixLift 207330
  have htrace : WordTrace (prefixWord ++ tailWord_207330) baseStart_207330 baseEnd_207330 := by
    simpa [prefixWord, tailWord_207330, baseEnd_207330] using wordTrace_append hprefix tailTrace_207330
  have hstable : (prefixWord ++ tailWord_207330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207330).length < 2 ^ (prefixWord ++ tailWord_207330).sum := by decide
  have hdescent : baseEnd_207330 < baseStart_207330 := by decide
  rcases family_descends (prefixWord ++ tailWord_207330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207333 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_207333 : Nat := 118140960795 + 207333 * 2 ^ 59
def prefixEnd_207333 : Nat := 4983230072969 + 3 ^ 40 * 207333 * 2
def baseEnd_207333 : Nat := 106461484538742542383999

theorem tailTrace_207333 : CollatzResearch.WordTrace tailWord_207333 prefixEnd_207333 106461484538742542383999 := by
  unfold tailWord_207333
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562055757875425502402653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5041370505250283668268435 7562055757875425502402653)
  ·
    refine ⟨2835770909203284563400995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7562055757875425502402653 2835770909203284563400995)
    ·
      refine ⟨4253656363804926845101493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2835770909203284563400995 4253656363804926845101493)
      ·
        refine ⟨398780284106711891728265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4253656363804926845101493 398780284106711891728265)
        ·
          refine ⟨299085213080033918796199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398780284106711891728265 299085213080033918796199)
          ·
            refine ⟨448627819620050878194299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299085213080033918796199 448627819620050878194299)
            ·
              refine ⟨672941729430076317291449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448627819620050878194299 672941729430076317291449)
              ·
                refine ⟨504706297072557237968587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672941729430076317291449 504706297072557237968587)
                ·
                  refine ⟨757059445608835856952881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504706297072557237968587 757059445608835856952881)
                  ·
                    refine ⟨567794584206626892714661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 757059445608835856952881 567794584206626892714661)
                    ·
                      refine ⟨106461484538742542383999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 567794584206626892714661 106461484538742542383999)
                      ·
                        rfl

theorem cell23_207333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_207333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207333 prefixEnd_207333 := by exact prefixLift 207333
  have htrace : WordTrace (prefixWord ++ tailWord_207333) baseStart_207333 baseEnd_207333 := by
    simpa [prefixWord, tailWord_207333, baseEnd_207333] using wordTrace_append hprefix tailTrace_207333
  have hstable : (prefixWord ++ tailWord_207333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207333).length < 2 ^ (prefixWord ++ tailWord_207333).sum := by decide
  have hdescent : baseEnd_207333 < baseStart_207333 := by decide
  rcases family_descends (prefixWord ++ tailWord_207333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207336 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_207336 : Nat := 118140960795 + 207336 * 2 ^ 59
def prefixEnd_207336 : Nat := 4983230072969 + 3 ^ 40 * 207336 * 2
def baseEnd_207336 : Nat := 106463024980706030646485

theorem tailTrace_207336 : CollatzResearch.WordTrace tailWord_207336 prefixEnd_207336 106463024980706030646485 := by
  unfold tailWord_207336
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781082588432278507380931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5041443451243038009841241 3781082588432278507380931)
  ·
    refine ⟨5671623882648417761071397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3781082588432278507380931 5671623882648417761071397)
    ·
      refine ⟨1063429477996578330200887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5671623882648417761071397 1063429477996578330200887)
      ·
        refine ⟨1595144216994867495301331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063429477996578330200887 1595144216994867495301331)
        ·
          refine ⟨2392716325492301242951997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595144216994867495301331 2392716325492301242951997)
          ·
            refine ⟨897268622059612966106999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2392716325492301242951997 897268622059612966106999)
            ·
              refine ⟨1345902933089419449160499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897268622059612966106999 1345902933089419449160499)
              ·
                refine ⟨2018854399634129173740749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345902933089419449160499 2018854399634129173740749)
                ·
                  refine ⟨757070399862798440152781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2018854399634129173740749 757070399862798440152781)
                  ·
                    refine ⟨283901399948549415057293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 757070399862798440152781 283901399948549415057293)
                    ·
                      refine ⟨106463024980706030646485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283901399948549415057293 106463024980706030646485)
                      ·
                        rfl

theorem cell23_207336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_207336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207336 prefixEnd_207336 := by exact prefixLift 207336
  have htrace : WordTrace (prefixWord ++ tailWord_207336) baseStart_207336 baseEnd_207336 := by
    simpa [prefixWord, tailWord_207336, baseEnd_207336] using wordTrace_append hprefix tailTrace_207336
  have hstable : (prefixWord ++ tailWord_207336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207336).length < 2 ^ (prefixWord ++ tailWord_207336).sum := by decide
  have hdescent : baseEnd_207336 < baseStart_207336 := by decide
  rcases family_descends (prefixWord ++ tailWord_207336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207353 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 3]
def baseStart_207353 : Nat := 118140960795 + 207353 * 2 ^ 59
def prefixEnd_207353 : Nat := 4983230072969 + 3 ^ 40 * 207353 * 2
def baseEnd_207353 : Nat := 106471754151832464133907

theorem tailTrace_207353 : CollatzResearch.WordTrace tailWord_207353 prefixEnd_207353 106471754151832464133907 := by
  unfold tailWord_207353
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562785217802968918130713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5041856811868645945420475 7562785217802968918130713)
  ·
    refine ⟨5672088913352226688598035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7562785217802968918130713 5672088913352226688598035)
    ·
      refine ⟨8508133370028340032897053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672088913352226688598035 8508133370028340032897053)
      ·
        refine ⟨3190550013760627512336395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8508133370028340032897053 3190550013760627512336395)
        ·
          refine ⟨4785825020640941268504593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3190550013760627512336395 4785825020640941268504593)
          ·
            refine ⟨3589368765480705951378445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4785825020640941268504593 3589368765480705951378445)
            ·
              refine ⟨1346013287055264731766917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3589368765480705951378445 1346013287055264731766917)
              ·
                refine ⟨252377491322862137206297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1346013287055264731766917 252377491322862137206297)
                ·
                  refine ⟨189283118492146602904723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252377491322862137206297 189283118492146602904723)
                  ·
                    refine ⟨283924677738219904357085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189283118492146602904723 283924677738219904357085)
                    ·
                      refine ⟨106471754151832464133907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 283924677738219904357085 106471754151832464133907)
                      ·
                        rfl

theorem cell23_207353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_207353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207353 prefixEnd_207353 := by exact prefixLift 207353
  have htrace : WordTrace (prefixWord ++ tailWord_207353) baseStart_207353 baseEnd_207353 := by
    simpa [prefixWord, tailWord_207353, baseEnd_207353] using wordTrace_append hprefix tailTrace_207353
  have hstable : (prefixWord ++ tailWord_207353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207353).length < 2 ^ (prefixWord ++ tailWord_207353).sum := by decide
  have hdescent : baseEnd_207353 < baseStart_207353 := by decide
  rcases family_descends (prefixWord ++ tailWord_207353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207359 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_207359 : Nat := 118140960795 + 207359 * 2 ^ 59
def prefixEnd_207359 : Nat := 4983230072969 + 3 ^ 40 * 207359 * 2
def baseEnd_207359 : Nat := 106474835035759440658879

theorem tailTrace_207359 : CollatzResearch.WordTrace tailWord_207359 prefixEnd_207359 106474835035759440658879 := by
  unfold tailWord_207359
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563004055781231942849131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5042002703854154628566087 7563004055781231942849131)
  ·
    refine ⟨11344506083671847914273697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7563004055781231942849131 11344506083671847914273697)
    ·
      refine ⟨8508379562753885935705273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11344506083671847914273697 8508379562753885935705273)
      ·
        refine ⟨6381284672065414451778955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8508379562753885935705273 6381284672065414451778955)
        ·
          refine ⟨9571927008098121677668433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381284672065414451778955 9571927008098121677668433)
          ·
            refine ⟨7178945256073591258251325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9571927008098121677668433 7178945256073591258251325)
            ·
              refine ⟨2692104471027596721844247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7178945256073591258251325 2692104471027596721844247)
              ·
                refine ⟨4038156706541395082766371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692104471027596721844247 4038156706541395082766371)
                ·
                  refine ⟨6057235059812092624149557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038156706541395082766371 6057235059812092624149557)
                  ·
                    refine ⟨567865786857383683514021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6057235059812092624149557 567865786857383683514021)
                    ·
                      refine ⟨106474835035759440658879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 567865786857383683514021 106474835035759440658879)
                      ·
                        rfl

theorem cell23_207359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_207359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207359 prefixEnd_207359 := by exact prefixLift 207359
  have htrace : WordTrace (prefixWord ++ tailWord_207359) baseStart_207359 baseEnd_207359 := by
    simpa [prefixWord, tailWord_207359, baseEnd_207359] using wordTrace_append hprefix tailTrace_207359
  have hstable : (prefixWord ++ tailWord_207359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207359).length < 2 ^ (prefixWord ++ tailWord_207359).sum := by decide
  have hdescent : baseEnd_207359 < baseStart_207359 := by decide
  rcases family_descends (prefixWord ++ tailWord_207359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207393 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_207393 : Nat := 118140960795 + 207393 * 2 ^ 59
def prefixEnd_207393 : Nat := 4983230072969 + 3 ^ 40 * 207393 * 2
def baseEnd_207393 : Nat := 106492293378012307633723

theorem tailTrace_207393 : CollatzResearch.WordTrace tailWord_207393 prefixEnd_207393 106492293378012307633723 := by
  unfold tailWord_207393
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564244137658055749586833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5042829425105370499724555 7564244137658055749586833)
  ·
    refine ⟨5673183103243541812190125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7564244137658055749586833 5673183103243541812190125)
    ·
      refine ⟨2127443663716328179571297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5673183103243541812190125 2127443663716328179571297)
      ·
        refine ⟨1595582747787246134678473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127443663716328179571297 1595582747787246134678473)
        ·
          refine ⟨1196687060840434601008855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595582747787246134678473 1196687060840434601008855)
          ·
            refine ⟨1795030591260651901513283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196687060840434601008855 1795030591260651901513283)
            ·
              refine ⟨2692545886890977852269925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795030591260651901513283 2692545886890977852269925)
              ·
                refine ⟨504852353792058347300611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2692545886890977852269925 504852353792058347300611)
                ·
                  refine ⟨757278530688087520950917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504852353792058347300611 757278530688087520950917)
                  ·
                    refine ⟨141989724504016410178297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757278530688087520950917 141989724504016410178297)
                    ·
                      refine ⟨106492293378012307633723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 141989724504016410178297 106492293378012307633723)
                      ·
                        rfl

theorem cell23_207393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_207393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207393 prefixEnd_207393 := by exact prefixLift 207393
  have htrace : WordTrace (prefixWord ++ tailWord_207393) baseStart_207393 baseEnd_207393 := by
    simpa [prefixWord, tailWord_207393, baseEnd_207393] using wordTrace_append hprefix tailTrace_207393
  have hstable : (prefixWord ++ tailWord_207393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207393).length < 2 ^ (prefixWord ++ tailWord_207393).sum := by decide
  have hdescent : baseEnd_207393 < baseStart_207393 := by decide
  rcases family_descends (prefixWord ++ tailWord_207393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207416 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 7]
def baseStart_207416 : Nat := 118140960795 + 207416 * 2 ^ 59
def prefixEnd_207416 : Nat := 4983230072969 + 3 ^ 40 * 207416 * 2
def baseEnd_207416 : Nat := 11833789270340635294013

theorem tailTrace_207416 : CollatzResearch.WordTrace tailWord_207416 prefixEnd_207416 11833789270340635294013 := by
  unfold tailWord_207416
  simp only [CollatzResearch.WordTrace]
  refine ⟨3782541508287365338837051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5043388677716487118449401 3782541508287365338837051)
  ·
    refine ⟨5673812262431048008255577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3782541508287365338837051 5673812262431048008255577)
    ·
      refine ⟨4255359196823286006191683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5673812262431048008255577 4255359196823286006191683)
      ·
        refine ⟨6383038795234929009287525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255359196823286006191683 6383038795234929009287525)
        ·
          refine ⟨1196819774106549189241411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6383038795234929009287525 1196819774106549189241411)
          ·
            refine ⟨1795229661159823783862117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196819774106549189241411 1795229661159823783862117)
            ·
              refine ⟨336605561467466959474147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1795229661159823783862117 336605561467466959474147)
              ·
                refine ⟨504908342201200439211221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336605561467466959474147 504908342201200439211221)
                ·
                  refine ⟨11833789270340635294013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 504908342201200439211221 11833789270340635294013)
                  ·
                    rfl

theorem cell23_207416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 7].length) (baseStart_207416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207416 prefixEnd_207416 := by exact prefixLift 207416
  have htrace : WordTrace (prefixWord ++ tailWord_207416) baseStart_207416 baseEnd_207416 := by
    simpa [prefixWord, tailWord_207416, baseEnd_207416] using wordTrace_append hprefix tailTrace_207416
  have hstable : (prefixWord ++ tailWord_207416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207416).length < 2 ^ (prefixWord ++ tailWord_207416).sum := by decide
  have hdescent : baseEnd_207416 < baseStart_207416 := by decide
  rcases family_descends (prefixWord ++ tailWord_207416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207478 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_207478 : Nat := 118140960795 + 207478 * 2 ^ 59
def prefixEnd_207478 : Nat := 4983230072969 + 3 ^ 40 * 207478 * 2
def baseEnd_207478 : Nat := 106535939233644475070833

theorem tailTrace_207478 : CollatzResearch.WordTrace tailWord_207478 prefixEnd_207478 106535939233644475070833 := by
  unfold tailWord_207478
  simp only [CollatzResearch.WordTrace]
  refine ⟨472959021396882204151943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5044896228233410177620725 472959021396882204151943)
  ·
    refine ⟨709438532095323306227915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 472959021396882204151943 709438532095323306227915)
    ·
      refine ⟨1064157798142984959341873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709438532095323306227915 1064157798142984959341873)
      ·
        refine ⟨798118348607238719506405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064157798142984959341873 798118348607238719506405)
        ·
          refine ⟨149647190363857259907451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 798118348607238719506405 149647190363857259907451)
          ·
            refine ⟨224470785545785889861177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149647190363857259907451 224470785545785889861177)
            ·
              refine ⟨168353089159339417395883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224470785545785889861177 168353089159339417395883)
              ·
                refine ⟨252529633739009126093825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168353089159339417395883 252529633739009126093825)
                ·
                  refine ⟨189397225304256844570369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252529633739009126093825 189397225304256844570369)
                  ·
                    refine ⟨142047918978192633427777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189397225304256844570369 142047918978192633427777)
                    ·
                      refine ⟨106535939233644475070833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142047918978192633427777 106535939233644475070833)
                      ·
                        rfl

theorem cell23_207478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_207478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207478 prefixEnd_207478 := by exact prefixLift 207478
  have htrace : WordTrace (prefixWord ++ tailWord_207478) baseStart_207478 baseEnd_207478 := by
    simpa [prefixWord, tailWord_207478, baseEnd_207478] using wordTrace_append hprefix tailTrace_207478
  have hstable : (prefixWord ++ tailWord_207478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207478).length < 2 ^ (prefixWord ++ tailWord_207478).sum := by decide
  have hdescent : baseEnd_207478 < baseStart_207478 := by decide
  rcases family_descends (prefixWord ++ tailWord_207478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207546 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_207546 : Nat := 118140960795 + 207546 * 2 ^ 59
def prefixEnd_207546 : Nat := 4983230072969 + 3 ^ 40 * 207546 * 2
def baseEnd_207546 : Nat := 106570855918150209020519

theorem tailTrace_207546 : CollatzResearch.WordTrace tailWord_207546 prefixEnd_207546 106570855918150209020519 := by
  unfold tailWord_207546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892456126525940719976623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5046549670735841919937661 1892456126525940719976623)
  ·
    refine ⟨2838684189788911079964935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892456126525940719976623 2838684189788911079964935)
    ·
      refine ⟨4258026284683366619947403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838684189788911079964935 4258026284683366619947403)
      ·
        refine ⟨6387039427025049929921105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258026284683366619947403 6387039427025049929921105)
        ·
          refine ⟨4790279570268787447440829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6387039427025049929921105 4790279570268787447440829)
          ·
            refine ⟨1796354838850795292790311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4790279570268787447440829 1796354838850795292790311)
            ·
              refine ⟨2694532258276192939185467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796354838850795292790311 2694532258276192939185467)
              ·
                refine ⟨4041798387414289408778201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694532258276192939185467 4041798387414289408778201)
                ·
                  refine ⟨3031348790560717056583651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4041798387414289408778201 3031348790560717056583651)
                  ·
                    refine ⟨4547023185841075584875477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031348790560717056583651 4547023185841075584875477)
                    ·
                      refine ⟨106570855918150209020519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4547023185841075584875477 106570855918150209020519)
                      ·
                        rfl

theorem cell23_207546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_207546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207546 prefixEnd_207546 := by exact prefixLift 207546
  have htrace : WordTrace (prefixWord ++ tailWord_207546) baseStart_207546 baseEnd_207546 := by
    simpa [prefixWord, tailWord_207546, baseEnd_207546] using wordTrace_append hprefix tailTrace_207546
  have hstable : (prefixWord ++ tailWord_207546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207546).length < 2 ^ (prefixWord ++ tailWord_207546).sum := by decide
  have hdescent : baseEnd_207546 < baseStart_207546 := by decide
  rcases family_descends (prefixWord ++ tailWord_207546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207560 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_207560 : Nat := 118140960795 + 207560 * 2 ^ 59
def prefixEnd_207560 : Nat := 4983230072969 + 3 ^ 40 * 207560 * 2
def baseEnd_207560 : Nat := 106578044647313154245455

theorem tailTrace_207560 : CollatzResearch.WordTrace tailWord_207560 prefixEnd_207560 106578044647313154245455 := by
  unfold tailWord_207560
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785167564026521635458067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5046890085368695513944089 3785167564026521635458067)
  ·
    refine ⟨5677751346039782453187101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3785167564026521635458067 5677751346039782453187101)
    ·
      refine ⟨2129156754764918419945163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5677751346039782453187101 2129156754764918419945163)
      ·
        refine ⟨3193735132147377629917745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129156754764918419945163 3193735132147377629917745)
        ·
          refine ⟨2395301349110533222438309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193735132147377629917745 2395301349110533222438309)
          ·
            refine ⟨449119002958224979207183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2395301349110533222438309 449119002958224979207183)
            ·
              refine ⟨673678504437337468810775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449119002958224979207183 673678504437337468810775)
              ·
                refine ⟨1010517756656006203216163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673678504437337468810775 1010517756656006203216163)
                ·
                  refine ⟨1515776634984009304824245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010517756656006203216163 1515776634984009304824245)
                  ·
                    refine ⟨142104059529750872327273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1515776634984009304824245 142104059529750872327273)
                    ·
                      refine ⟨106578044647313154245455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142104059529750872327273 106578044647313154245455)
                      ·
                        rfl

theorem cell23_207560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_207560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207560 prefixEnd_207560 := by exact prefixLift 207560
  have htrace : WordTrace (prefixWord ++ tailWord_207560) baseStart_207560 baseEnd_207560 := by
    simpa [prefixWord, tailWord_207560, baseEnd_207560] using wordTrace_append hprefix tailTrace_207560
  have hstable : (prefixWord ++ tailWord_207560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207560).length < 2 ^ (prefixWord ++ tailWord_207560).sum := by decide
  have hdescent : baseEnd_207560 < baseStart_207560 := by decide
  rcases family_descends (prefixWord ++ tailWord_207560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207593 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 3]
def baseStart_207593 : Nat := 118140960795 + 207593 * 2 ^ 59
def prefixEnd_207593 : Nat := 4983230072969 + 3 ^ 40 * 207593 * 2
def baseEnd_207593 : Nat := 106594989508911525132803

theorem tailTrace_207593 : CollatzResearch.WordTrace tailWord_207593 prefixEnd_207593 106594989508911525132803 := by
  unfold tailWord_207593
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571538736933489906867433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5047692491288993271244955 7571538736933489906867433)
  ·
    refine ⟨5678654052700117430150575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7571538736933489906867433 5678654052700117430150575)
    ·
      refine ⟨8517981079050176145225863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678654052700117430150575 8517981079050176145225863)
      ·
        refine ⟨12776971618575264217838795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8517981079050176145225863 12776971618575264217838795)
        ·
          refine ⟨19165457427862896326758193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12776971618575264217838795 19165457427862896326758193)
          ·
            refine ⟨14374093070897172245068645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19165457427862896326758193 14374093070897172245068645)
            ·
              refine ⟨2695142450793219795950371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14374093070897172245068645 2695142450793219795950371)
              ·
                refine ⟨4042713676189829693925557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695142450793219795950371 4042713676189829693925557)
                ·
                  refine ⟨379004407142796533805521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4042713676189829693925557 379004407142796533805521)
                  ·
                    refine ⟨284253305357097400354141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 379004407142796533805521 284253305357097400354141)
                    ·
                      refine ⟨106594989508911525132803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 284253305357097400354141 106594989508911525132803)
                      ·
                        rfl

theorem cell23_207593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_207593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207593 prefixEnd_207593 := by exact prefixLift 207593
  have htrace : WordTrace (prefixWord ++ tailWord_207593) baseStart_207593 baseEnd_207593 := by
    simpa [prefixWord, tailWord_207593, baseEnd_207593] using wordTrace_append hprefix tailTrace_207593
  have hstable : (prefixWord ++ tailWord_207593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207593).length < 2 ^ (prefixWord ++ tailWord_207593).sum := by decide
  have hdescent : baseEnd_207593 < baseStart_207593 := by decide
  rcases family_descends (prefixWord ++ tailWord_207593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207596 : List Nat := [2, 2, 1, 1, 2, 2, 1, 12]
def baseStart_207596 : Nat := 118140960795 + 207596 * 2 ^ 59
def prefixEnd_207596 : Nat := 4983230072969 + 3 ^ 40 * 207596 * 2
def baseEnd_207596 : Nat := 3948019627810185681307

theorem tailTrace_207596 : CollatzResearch.WordTrace tailWord_207596 prefixEnd_207596 3948019627810185681307 := by
  unfold tailWord_207596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785824077961310709613321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5047765437281747612817761 3785824077961310709613321)
  ·
    refine ⟨2839368058470983032209991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3785824077961310709613321 2839368058470983032209991)
    ·
      refine ⟨4259052087706474548314987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2839368058470983032209991 4259052087706474548314987)
      ·
        refine ⟨6388578131559711822472481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259052087706474548314987 6388578131559711822472481)
        ·
          refine ⟨4791433598669783866854361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6388578131559711822472481 4791433598669783866854361)
          ·
            refine ⟨3593575199002337900140771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4791433598669783866854361 3593575199002337900140771)
            ·
              refine ⟨5390362798503506850211157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593575199002337900140771 5390362798503506850211157)
              ·
                refine ⟨3948019627810185681307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 5390362798503506850211157 3948019627810185681307)
                ·
                  rfl

theorem cell23_207596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 12].length) (baseStart_207596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207596 prefixEnd_207596 := by exact prefixLift 207596
  have htrace : WordTrace (prefixWord ++ tailWord_207596) baseStart_207596 baseEnd_207596 := by
    simpa [prefixWord, tailWord_207596, baseEnd_207596] using wordTrace_append hprefix tailTrace_207596
  have hstable : (prefixWord ++ tailWord_207596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207596).length < 2 ^ (prefixWord ++ tailWord_207596).sum := by decide
  have hdescent : baseEnd_207596 < baseStart_207596 := by decide
  rcases family_descends (prefixWord ++ tailWord_207596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207610 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_207610 : Nat := 118140960795 + 207610 * 2 ^ 59
def prefixEnd_207610 : Nat := 4983230072969 + 3 ^ 40 * 207610 * 2
def baseEnd_207610 : Nat := 106603718680037958620225

theorem tailTrace_207610 : CollatzResearch.WordTrace tailWord_207610 prefixEnd_207610 106603718680037958620225 := by
  unfold tailWord_207610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893039694467975452559071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5048105851914601206824189 1893039694467975452559071)
  ·
    refine ⟨2839559541701963178838607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1893039694467975452559071 2839559541701963178838607)
    ·
      refine ⟨4259339312552944768257911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2839559541701963178838607 4259339312552944768257911)
      ·
        refine ⟨6389008968829417152386867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259339312552944768257911 6389008968829417152386867)
        ·
          refine ⟨9583513453244125728580301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389008968829417152386867 9583513453244125728580301)
          ·
            refine ⟨3593817544966547148217613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9583513453244125728580301 3593817544966547148217613)
            ·
              refine ⟨1347681579362455180581605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3593817544966547148217613 1347681579362455180581605)
              ·
                refine ⟨252690296130460346359051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1347681579362455180581605 252690296130460346359051)
                ·
                  refine ⟨379035444195690519538577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252690296130460346359051 379035444195690519538577)
                  ·
                    refine ⟨284276583146767889653933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 379035444195690519538577 284276583146767889653933)
                    ·
                      refine ⟨106603718680037958620225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 284276583146767889653933 106603718680037958620225)
                      ·
                        rfl

theorem cell23_207610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_207610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207610 prefixEnd_207610 := by exact prefixLift 207610
  have htrace : WordTrace (prefixWord ++ tailWord_207610) baseStart_207610 baseEnd_207610 := by
    simpa [prefixWord, tailWord_207610, baseEnd_207610] using wordTrace_append hprefix tailTrace_207610
  have hstable : (prefixWord ++ tailWord_207610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207610).length < 2 ^ (prefixWord ++ tailWord_207610).sum := by decide
  have hdescent : baseEnd_207610 < baseStart_207610 := by decide
  rcases family_descends (prefixWord ++ tailWord_207610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207667 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 3, 3, 2]
def baseStart_207667 : Nat := 118140960795 + 207667 * 2 ^ 59
def prefixEnd_207667 : Nat := 4983230072969 + 3 ^ 40 * 207667 * 2
def baseEnd_207667 : Nat := 106632987077344235607463

theorem tailTrace_207667 : CollatzResearch.WordTrace tailWord_207667 prefixEnd_207667 106632987077344235607463 := by
  unfold tailWord_207667
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574237738665400545061255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5049491825776933696707503 7574237738665400545061255)
  ·
    refine ⟨11361356607998100817591883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7574237738665400545061255 11361356607998100817591883)
    ·
      refine ⟨17042034911997151226387825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11361356607998100817591883 17042034911997151226387825)
      ·
        refine ⟨12781526183997863419790869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17042034911997151226387825 12781526183997863419790869)
        ·
          refine ⟨599134039874899847802697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12781526183997863419790869 599134039874899847802697)
          ·
            refine ⟨449350529906174885852023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599134039874899847802697 449350529906174885852023)
            ·
              refine ⟨674025794859262328778035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449350529906174885852023 674025794859262328778035)
              ·
                refine ⟨1011038692288893493167053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674025794859262328778035 1011038692288893493167053)
                ·
                  refine ⟨379139509608335059937645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011038692288893493167053 379139509608335059937645)
                  ·
                    refine ⟨142177316103125647476617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379139509608335059937645 142177316103125647476617)
                    ·
                      refine ⟨106632987077344235607463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142177316103125647476617 106632987077344235607463)
                      ·
                        rfl

theorem cell23_207667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3, 2].length) (baseStart_207667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207667 prefixEnd_207667 := by exact prefixLift 207667
  have htrace : WordTrace (prefixWord ++ tailWord_207667) baseStart_207667 baseEnd_207667 := by
    simpa [prefixWord, tailWord_207667, baseEnd_207667] using wordTrace_append hprefix tailTrace_207667
  have hstable : (prefixWord ++ tailWord_207667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207667).length < 2 ^ (prefixWord ++ tailWord_207667).sum := by decide
  have hdescent : baseEnd_207667 < baseStart_207667 := by decide
  rcases family_descends (prefixWord ++ tailWord_207667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207683 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5]
def baseStart_207683 : Nat := 118140960795 + 207683 * 2 ^ 59
def prefixEnd_207683 : Nat := 4983230072969 + 3 ^ 40 * 207683 * 2
def baseEnd_207683 : Nat := 106641202767816173007389

theorem tailTrace_207683 : CollatzResearch.WordTrace tailWord_207683 prefixEnd_207683 106641202767816173007389 := by
  unfold tailWord_207683
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574821306607435277643703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5049880871071623518429135 7574821306607435277643703)
  ·
    refine ⟨11362231959911152916465555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7574821306607435277643703 11362231959911152916465555)
    ·
      refine ⟨17043347939866729374698333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11362231959911152916465555 17043347939866729374698333)
      ·
        refine ⟨6391255477450023515511875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17043347939866729374698333 6391255477450023515511875)
        ·
          refine ⟨9586883216175035273267813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391255477450023515511875 9586883216175035273267813)
          ·
            refine ⟨1797540603032819113737715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9586883216175035273267813 1797540603032819113737715)
            ·
              refine ⟨2696310904549228670606573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797540603032819113737715 2696310904549228670606573)
              ·
                refine ⟨1011116589205960751477465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2696310904549228670606573 1011116589205960751477465)
                ·
                  refine ⟨758337441904470563608099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011116589205960751477465 758337441904470563608099)
                  ·
                    refine ⟨1137506162856705845412149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 758337441904470563608099 1137506162856705845412149)
                    ·
                      refine ⟨106641202767816173007389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1137506162856705845412149 106641202767816173007389)
                      ·
                        rfl

theorem cell23_207683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_207683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207683 prefixEnd_207683 := by exact prefixLift 207683
  have htrace : WordTrace (prefixWord ++ tailWord_207683) baseStart_207683 baseEnd_207683 := by
    simpa [prefixWord, tailWord_207683, baseEnd_207683] using wordTrace_append hprefix tailTrace_207683
  have hstable : (prefixWord ++ tailWord_207683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207683).length < 2 ^ (prefixWord ++ tailWord_207683).sum := by decide
  have hdescent : baseEnd_207683 < baseStart_207683 := by decide
  rcases family_descends (prefixWord ++ tailWord_207683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207720 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 7]
def baseStart_207720 : Nat := 118140960795 + 207720 * 2 ^ 59
def prefixEnd_207720 : Nat := 4983230072969 + 3 ^ 40 * 207720 * 2
def baseEnd_207720 : Nat := 11851133505781392027191

theorem tailTrace_207720 : CollatzResearch.WordTrace tailWord_207720 prefixEnd_207720 11851133505781392027191 := by
  unfold tailWord_207720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788085403736695298370307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5050780538315593731160409 3788085403736695298370307)
  ·
    refine ⟨5682128105605042947555461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788085403736695298370307 5682128105605042947555461)
    ·
      refine ⟨1065399019800945552666649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5682128105605042947555461 1065399019800945552666649)
      ·
        refine ⟨799049264850709164499987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1065399019800945552666649 799049264850709164499987)
        ·
          refine ⟨1198573897276063746749981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799049264850709164499987 1198573897276063746749981)
          ·
            refine ⟨449465211478523905031243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1198573897276063746749981 449465211478523905031243)
            ·
              refine ⟨674197817217785857546865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449465211478523905031243 674197817217785857546865)
              ·
                refine ⟨505648362913339393160149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674197817217785857546865 505648362913339393160149)
                ·
                  refine ⟨11851133505781392027191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 505648362913339393160149 11851133505781392027191)
                  ·
                    rfl

theorem cell23_207720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 7].length) (baseStart_207720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207720 prefixEnd_207720 := by exact prefixLift 207720
  have htrace : WordTrace (prefixWord ++ tailWord_207720) baseStart_207720 baseEnd_207720 := by
    simpa [prefixWord, tailWord_207720, baseEnd_207720] using wordTrace_append hprefix tailTrace_207720
  have hstable : (prefixWord ++ tailWord_207720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207720).length < 2 ^ (prefixWord ++ tailWord_207720).sum := by decide
  have hdescent : baseEnd_207720 < baseStart_207720 := by decide
  rcases family_descends (prefixWord ++ tailWord_207720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207737 : List Nat := [1, 2, 1, 3, 2, 4, 2, 3, 5]
def baseStart_207737 : Nat := 118140960795 + 207737 * 2 ^ 59
def prefixEnd_207737 : Nat := 4983230072969 + 3 ^ 40 * 207737 * 2
def baseEnd_207737 : Nat := 11852103413684329081349

theorem tailTrace_207737 : CollatzResearch.WordTrace tailWord_207737 prefixEnd_207737 11852103413684329081349 := by
  unfold tailWord_207737
  simp only [CollatzResearch.WordTrace]
  refine ⟨7576790848411802500109465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5051193898941201666739643 7576790848411802500109465)
  ·
    refine ⟨5682593136308851875082099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7576790848411802500109465 5682593136308851875082099)
    ·
      refine ⟨8523889704463277812623149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682593136308851875082099 8523889704463277812623149)
      ·
        refine ⟨3196458639173729179733681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8523889704463277812623149 3196458639173729179733681)
        ·
          refine ⟨2397343979380296884800261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3196458639173729179733681 2397343979380296884800261)
          ·
            refine ⟨449501996133805665900049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2397343979380296884800261 449501996133805665900049)
            ·
              refine ⟨337126497100354249425037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449501996133805665900049 337126497100354249425037)
              ·
                refine ⟨126422436412632843534389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337126497100354249425037 126422436412632843534389)
                ·
                  refine ⟨11852103413684329081349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126422436412632843534389 11852103413684329081349)
                  ·
                    rfl

theorem cell23_207737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 5].length) (baseStart_207737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207737 prefixEnd_207737 := by exact prefixLift 207737
  have htrace : WordTrace (prefixWord ++ tailWord_207737) baseStart_207737 baseEnd_207737 := by
    simpa [prefixWord, tailWord_207737, baseEnd_207737] using wordTrace_append hprefix tailTrace_207737
  have hstable : (prefixWord ++ tailWord_207737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207737).length < 2 ^ (prefixWord ++ tailWord_207737).sum := by decide
  have hdescent : baseEnd_207737 < baseStart_207737 := by decide
  rcases family_descends (prefixWord ++ tailWord_207737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207743 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_207743 : Nat := 118140960795 + 207743 * 2 ^ 59
def prefixEnd_207743 : Nat := 4983230072969 + 3 ^ 40 * 207743 * 2
def baseEnd_207743 : Nat := 106672011607085938257113

theorem tailTrace_207743 : CollatzResearch.WordTrace tailWord_207743 prefixEnd_207743 106672011607085938257113 := by
  unfold tailWord_207743
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577009686390065524827883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5051339790926710349885255 7577009686390065524827883)
  ·
    refine ⟨11365514529585098287241825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7577009686390065524827883 11365514529585098287241825)
    ·
      refine ⟨8524135897188823715431369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11365514529585098287241825 8524135897188823715431369)
      ·
        refine ⟨6393101922891617786573527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8524135897188823715431369 6393101922891617786573527)
        ·
          refine ⟨9589652884337426679860291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6393101922891617786573527 9589652884337426679860291)
          ·
            refine ⟨14384479326506140019790437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589652884337426679860291 14384479326506140019790437)
            ·
              refine ⟨2697089873719901253710707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14384479326506140019790437 2697089873719901253710707)
              ·
                refine ⟨4045634810579851880566061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697089873719901253710707 4045634810579851880566061)
                ·
                  refine ⟨1517113053967444455212273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4045634810579851880566061 1517113053967444455212273)
                  ·
                    refine ⟨1137834790475583341409205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1517113053967444455212273 1137834790475583341409205)
                    ·
                      refine ⟨106672011607085938257113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1137834790475583341409205 106672011607085938257113)
                      ·
                        rfl

theorem cell23_207743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_207743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207743 prefixEnd_207743 := by exact prefixLift 207743
  have htrace : WordTrace (prefixWord ++ tailWord_207743) baseStart_207743 baseEnd_207743 := by
    simpa [prefixWord, tailWord_207743, baseEnd_207743] using wordTrace_append hprefix tailTrace_207743
  have hstable : (prefixWord ++ tailWord_207743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207743).length < 2 ^ (prefixWord ++ tailWord_207743).sum := by decide
  have hdescent : baseEnd_207743 < baseStart_207743 := by decide
  rcases family_descends (prefixWord ++ tailWord_207743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207861 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 6]
def baseStart_207861 : Nat := 118140960795 + 207861 * 2 ^ 59
def prefixEnd_207861 : Nat := 4983230072969 + 3 ^ 40 * 207861 * 2
def baseEnd_207861 : Nat := 11859178036035164064619

theorem tailTrace_207861 : CollatzResearch.WordTrace tailWord_207861 prefixEnd_207861 11859178036035164064619 := by
  unfold tailWord_207861
  simp only [CollatzResearch.WordTrace]
  refine ⟨7581313499962571677623437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5054208999975047785082291 7581313499962571677623437)
  ·
    refine ⟨2842992562485964379108789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7581313499962571677623437 2842992562485964379108789)
    ·
      refine ⟨266530552733059160541449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2842992562485964379108789 266530552733059160541449)
      ·
        refine ⟨199897914549794370406087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266530552733059160541449 199897914549794370406087)
        ·
          refine ⟨299846871824691555609131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199897914549794370406087 299846871824691555609131)
          ·
            refine ⟨449770307737037333413697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299846871824691555609131 449770307737037333413697)
            ·
              refine ⟨337327730802778000060273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449770307737037333413697 337327730802778000060273)
              ·
                refine ⟨252995798102083500045205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337327730802778000060273 252995798102083500045205)
                ·
                  refine ⟨11859178036035164064619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 252995798102083500045205 11859178036035164064619)
                  ·
                    rfl

theorem cell23_207861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_207861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207861 prefixEnd_207861 := by exact prefixLift 207861
  have htrace : WordTrace (prefixWord ++ tailWord_207861) baseStart_207861 baseEnd_207861 := by
    simpa [prefixWord, tailWord_207861, baseEnd_207861] using wordTrace_append hprefix tailTrace_207861
  have hstable : (prefixWord ++ tailWord_207861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207861).length < 2 ^ (prefixWord ++ tailWord_207861).sum := by decide
  have hdescent : baseEnd_207861 < baseStart_207861 := by decide
  rcases family_descends (prefixWord ++ tailWord_207861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207897 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 3]
def baseStart_207897 : Nat := 118140960795 + 207897 * 2 ^ 59
def prefixEnd_207897 : Nat := 4983230072969 + 3 ^ 40 * 207897 * 2
def baseEnd_207897 : Nat := 106751087627878335731405

theorem tailTrace_207897 : CollatzResearch.WordTrace tailWord_207897 prefixEnd_207897 106751087627878335731405 := by
  unfold tailWord_207897
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582626527832149825933945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5055084351888099883955963 7582626527832149825933945)
  ·
    refine ⟨5686969895874112369450459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7582626527832149825933945 5686969895874112369450459)
    ·
      refine ⟨8530454843811168554175689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5686969895874112369450459 8530454843811168554175689)
      ·
        refine ⟨6397841132858376415631767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8530454843811168554175689 6397841132858376415631767)
        ·
          refine ⟨9596761699287564623447651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397841132858376415631767 9596761699287564623447651)
          ·
            refine ⟨14395142548931346935171477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596761699287564623447651 14395142548931346935171477)
            ·
              refine ⟨674772306981156887586163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14395142548931346935171477 674772306981156887586163)
              ·
                refine ⟨1012158460471735331379245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674772306981156887586163 1012158460471735331379245)
                ·
                  refine ⟨379559422676900749267217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012158460471735331379245 379559422676900749267217)
                  ·
                    refine ⟨284669567007675561950413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 379559422676900749267217 284669567007675561950413)
                    ·
                      refine ⟨106751087627878335731405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 284669567007675561950413 106751087627878335731405)
                      ·
                        rfl

theorem cell23_207897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_207897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207897 prefixEnd_207897 := by exact prefixLift 207897
  have htrace : WordTrace (prefixWord ++ tailWord_207897) baseStart_207897 baseEnd_207897 := by
    simpa [prefixWord, tailWord_207897, baseEnd_207897] using wordTrace_append hprefix tailTrace_207897
  have hstable : (prefixWord ++ tailWord_207897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207897).length < 2 ^ (prefixWord ++ tailWord_207897).sum := by decide
  have hdescent : baseEnd_207897 < baseStart_207897 := by decide
  rcases family_descends (prefixWord ++ tailWord_207897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207907 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4]
def baseStart_207907 : Nat := 118140960795 + 207907 * 2 ^ 59
def prefixEnd_207907 : Nat := 4983230072969 + 3 ^ 40 * 207907 * 2
def baseEnd_207907 : Nat := 106756222434423296606359

theorem tailTrace_207907 : CollatzResearch.WordTrace tailWord_207907 prefixEnd_207907 106756222434423296606359 := by
  unfold tailWord_207907
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582991257795921533797975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5055327505197281022531983 7582991257795921533797975)
  ·
    refine ⟨11374486886693882300696963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7582991257795921533797975 11374486886693882300696963)
    ·
      refine ⟨17061730330040823451045445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11374486886693882300696963 17061730330040823451045445)
      ·
        refine ⟨3199074436882654397071021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17061730330040823451045445 3199074436882654397071021)
        ·
          refine ⟨1199652913830995398901633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3199074436882654397071021 1199652913830995398901633)
          ·
            refine ⟨899739685373246549176225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1199652913830995398901633 899739685373246549176225)
            ·
              refine ⟨674804764029934911882169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899739685373246549176225 674804764029934911882169)
              ·
                refine ⟨506103573022451183911627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674804764029934911882169 506103573022451183911627)
                ·
                  refine ⟨759155359533676775867441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506103573022451183911627 759155359533676775867441)
                  ·
                    refine ⟨569366519650257581900581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759155359533676775867441 569366519650257581900581)
                    ·
                      refine ⟨106756222434423296606359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 569366519650257581900581 106756222434423296606359)
                      ·
                        rfl

theorem cell23_207907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_207907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207907 prefixEnd_207907 := by exact prefixLift 207907
  have htrace : WordTrace (prefixWord ++ tailWord_207907) baseStart_207907 baseEnd_207907 := by
    simpa [prefixWord, tailWord_207907, baseEnd_207907] using wordTrace_append hprefix tailTrace_207907
  have hstable : (prefixWord ++ tailWord_207907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207907).length < 2 ^ (prefixWord ++ tailWord_207907).sum := by decide
  have hdescent : baseEnd_207907 < baseStart_207907 := by decide
  rcases family_descends (prefixWord ++ tailWord_207907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
