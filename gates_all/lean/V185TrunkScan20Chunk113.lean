import V185TrunkScan20Chunk112

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_686775 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 3]
def baseStart_686775 : Nat := 118140960795 + 686775 * 2 ^ 59
def prefixEnd_686775 : Nat := 4983230072969 + 3 ^ 40 * 686775 * 2
def baseEnd_686775 : Nat := 313462823548138420759187

theorem tailTrace_686775 : CollatzResearch.WordTrace tailWord_686775 prefixEnd_686775 313462823548138420759187 := by
  unfold tailWord_686775
  simp only [CollatzResearch.WordTrace]
  refine ⟨25048742086938941677029779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16699161391292627784686519 25048742086938941677029779)
  ·
    refine ⟨37573113130408412515544669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25048742086938941677029779 37573113130408412515544669)
    ·
      refine ⟨14089917423903154693329251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37573113130408412515544669 14089917423903154693329251)
      ·
        refine ⟨21134876135854732039993877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14089917423903154693329251 21134876135854732039993877)
        ·
          refine ⟨990697318868190564374713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21134876135854732039993877 990697318868190564374713)
          ·
            refine ⟨743022989151142923281035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990697318868190564374713 743022989151142923281035)
            ·
              refine ⟨1114534483726714384921553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743022989151142923281035 1114534483726714384921553)
              ·
                refine ⟨835900862795035788691165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114534483726714384921553 835900862795035788691165)
                ·
                  refine ⟨313462823548138420759187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835900862795035788691165 313462823548138420759187)
                  ·
                    rfl

theorem cell20_686775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_686775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686775 prefixEnd_686775 := by exact prefixLift 686775
  have htrace : WordTrace (prefixWord ++ tailWord_686775) baseStart_686775 baseEnd_686775 := by
    simpa [prefixWord, tailWord_686775, baseEnd_686775] using wordTrace_append hprefix tailTrace_686775
  have hstable : (prefixWord ++ tailWord_686775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686775).length < 2 ^ (prefixWord ++ tailWord_686775).sum := by decide
  have hdescent : baseEnd_686775 < baseStart_686775 := by decide
  rcases family_descends (prefixWord ++ tailWord_686775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686782 : List Nat := [4, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_686782 : Nat := 118140960795 + 686782 * 2 ^ 59
def prefixEnd_686782 : Nat := 4983230072969 + 3 ^ 40 * 686782 * 2
def baseEnd_686782 : Nat := 313466018538877507525825

theorem tailTrace_686782 : CollatzResearch.WordTrace tailWord_686782 prefixEnd_686782 313466018538877507525825 := by
  unfold tailWord_686782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131124674739197734066825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16699331598609054581689733 3131124674739197734066825)
  ·
    refine ⟨2348343506054398300550119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3131124674739197734066825 2348343506054398300550119)
    ·
      refine ⟨3522515259081597450825179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348343506054398300550119 3522515259081597450825179)
      ·
        refine ⟨5283772888622396176237769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3522515259081597450825179 5283772888622396176237769)
        ·
          refine ⟨3962829666466797132178327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5283772888622396176237769 3962829666466797132178327)
          ·
            refine ⟨5944244499700195698267491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962829666466797132178327 5944244499700195698267491)
            ·
              refine ⟨8916366749550293547401237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944244499700195698267491 8916366749550293547401237)
              ·
                refine ⟨417954691385170010034433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8916366749550293547401237 417954691385170010034433)
                ·
                  refine ⟨313466018538877507525825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417954691385170010034433 313466018538877507525825)
                  ·
                    rfl

theorem cell20_686782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_686782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686782 prefixEnd_686782 := by exact prefixLift 686782
  have htrace : WordTrace (prefixWord ++ tailWord_686782) baseStart_686782 baseEnd_686782 := by
    simpa [prefixWord, tailWord_686782, baseEnd_686782] using wordTrace_append hprefix tailTrace_686782
  have hstable : (prefixWord ++ tailWord_686782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686782).length < 2 ^ (prefixWord ++ tailWord_686782).sum := by decide
  have hdescent : baseEnd_686782 < baseStart_686782 := by decide
  rcases family_descends (prefixWord ++ tailWord_686782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686817 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_686817 : Nat := 118140960795 + 686817 * 2 ^ 59
def prefixEnd_686817 : Nat := 4983230072969 + 3 ^ 40 * 686817 * 2
def baseEnd_686817 : Nat := 313481993492572941359015

theorem tailTrace_686817 : CollatzResearch.WordTrace tailWord_686817 prefixEnd_686817 313481993492572941359015 := by
  unfold tailWord_686817
  simp only [CollatzResearch.WordTrace]
  refine ⟨25050273952786782850058705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16700182635191188566705803 25050273952786782850058705)
  ·
    refine ⟨18787705464590087137544029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25050273952786782850058705 18787705464590087137544029)
    ·
      refine ⟨7045389549221282676579011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18787705464590087137544029 7045389549221282676579011)
      ·
        refine ⟨10568084323831924014868517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7045389549221282676579011 10568084323831924014868517)
        ·
          refine ⟨1981515810718485752787847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10568084323831924014868517 1981515810718485752787847)
          ·
            refine ⟨2972273716077728629181771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981515810718485752787847 2972273716077728629181771)
            ·
              refine ⟨4458410574116592943772657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972273716077728629181771 4458410574116592943772657)
              ·
                refine ⟨3343807930587444707829493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4458410574116592943772657 3343807930587444707829493)
                ·
                  refine ⟨313481993492572941359015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3343807930587444707829493 313481993492572941359015)
                  ·
                    rfl

theorem cell20_686817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_686817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686817 prefixEnd_686817 := by exact prefixLift 686817
  have htrace : WordTrace (prefixWord ++ tailWord_686817) baseStart_686817 baseEnd_686817 := by
    simpa [prefixWord, tailWord_686817, baseEnd_686817] using wordTrace_append hprefix tailTrace_686817
  have hstable : (prefixWord ++ tailWord_686817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686817).length < 2 ^ (prefixWord ++ tailWord_686817).sum := by decide
  have hdescent : baseEnd_686817 < baseStart_686817 := by decide
  rcases family_descends (prefixWord ++ tailWord_686817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686820 : List Nat := [2, 3, 1, 1, 1, 4, 3, 3, 2]
def baseStart_686820 : Nat := 118140960795 + 686820 * 2 ^ 59
def prefixEnd_686820 : Nat := 4983230072969 + 3 ^ 40 * 686820 * 2
def baseEnd_686820 : Nat := 313483362774318264259003

theorem tailTrace_686820 : CollatzResearch.WordTrace tailWord_686820 prefixEnd_686820 313483362774318264259003 := by
  unfold tailWord_686820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12525191685887957181208957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16700255581183942908278609 12525191685887957181208957)
  ·
    refine ⟨4696946882207983942953359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12525191685887957181208957 4696946882207983942953359)
    ·
      refine ⟨7045420323311975914430039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4696946882207983942953359 7045420323311975914430039)
      ·
        refine ⟨10568130484967963871645059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7045420323311975914430039 10568130484967963871645059)
        ·
          refine ⟨15852195727451945807467589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10568130484967963871645059 15852195727451945807467589)
          ·
            refine ⟨2972286698897239838900173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15852195727451945807467589 2972286698897239838900173)
            ·
              refine ⟨1114607512086464939587565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2972286698897239838900173 1114607512086464939587565)
              ·
                refine ⟨417977817032424352345337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114607512086464939587565 417977817032424352345337)
                ·
                  refine ⟨313483362774318264259003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417977817032424352345337 313483362774318264259003)
                  ·
                    rfl

theorem cell20_686820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_686820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686820 prefixEnd_686820 := by exact prefixLift 686820
  have htrace : WordTrace (prefixWord ++ tailWord_686820) baseStart_686820 baseEnd_686820 := by
    simpa [prefixWord, tailWord_686820, baseEnd_686820] using wordTrace_append hprefix tailTrace_686820
  have hstable : (prefixWord ++ tailWord_686820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686820).length < 2 ^ (prefixWord ++ tailWord_686820).sum := by decide
  have hdescent : baseEnd_686820 < baseStart_686820 := by decide
  rcases family_descends (prefixWord ++ tailWord_686820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686831 : List Nat := [1, 1, 2, 1, 5, 2, 8]
def baseStart_686831 : Nat := 118140960795 + 686831 * 2 ^ 59
def prefixEnd_686831 : Nat := 4983230072969 + 3 ^ 40 * 686831 * 2
def baseEnd_686831 : Nat := 34832042608227901654699

theorem tailTrace_686831 : CollatzResearch.WordTrace tailWord_686831 prefixEnd_686831 34832042608227901654699 := by
  unfold tailWord_686831
  simp only [CollatzResearch.WordTrace]
  refine ⟨25050784574736063241068347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16700523049824042160712231 25050784574736063241068347)
  ·
    refine ⟨37576176862104094861602521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25050784574736063241068347 37576176862104094861602521)
    ·
      refine ⟨28182132646578071146201891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37576176862104094861602521 28182132646578071146201891)
      ·
        refine ⟨42273198969867106719302837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28182132646578071146201891 42273198969867106719302837)
        ·
          refine ⟨3963112403425041254934641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42273198969867106719302837 3963112403425041254934641)
          ·
            refine ⟨2972334302568780941200981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3963112403425041254934641 2972334302568780941200981)
            ·
              refine ⟨34832042608227901654699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2972334302568780941200981 34832042608227901654699)
              ·
                rfl

theorem cell20_686831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_686831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686831 prefixEnd_686831 := by exact prefixLift 686831
  have htrace : WordTrace (prefixWord ++ tailWord_686831) baseStart_686831 baseEnd_686831 := by
    simpa [prefixWord, tailWord_686831, baseEnd_686831] using wordTrace_append hprefix tailTrace_686831
  have hstable : (prefixWord ++ tailWord_686831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686831).length < 2 ^ (prefixWord ++ tailWord_686831).sum := by decide
  have hdescent : baseEnd_686831 < baseStart_686831 := by decide
  rcases family_descends (prefixWord ++ tailWord_686831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686841 : List Nat := [1, 2, 1, 3, 1, 1, 1, 8, 2]
def baseStart_686841 : Nat := 118140960795 + 686841 * 2 ^ 59
def prefixEnd_686841 : Nat := 4983230072969 + 3 ^ 40 * 686841 * 2
def baseEnd_686841 : Nat := 313492947746535524558917

theorem tailTrace_686841 : CollatzResearch.WordTrace tailWord_686841 prefixEnd_686841 313492947746535524558917 := by
  unfold tailWord_686841
  simp only [CollatzResearch.WordTrace]
  refine ⟨25051149304699834948932377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16700766203133223299288251 25051149304699834948932377)
  ·
    refine ⟨18788361978524876211699283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25051149304699834948932377 18788361978524876211699283)
    ·
      refine ⟨28182542967787314317548925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18788361978524876211699283 28182542967787314317548925)
      ·
        refine ⟨10568453612920242869080847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28182542967787314317548925 10568453612920242869080847)
        ·
          refine ⟨15852680419380364303621271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10568453612920242869080847 15852680419380364303621271)
          ·
            refine ⟨23779020629070546455431907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15852680419380364303621271 23779020629070546455431907)
            ·
              refine ⟨35668530943605819683147861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23779020629070546455431907 35668530943605819683147861)
              ·
                refine ⟨417990596995380699411889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 35668530943605819683147861 417990596995380699411889)
                ·
                  refine ⟨313492947746535524558917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417990596995380699411889 313492947746535524558917)
                  ·
                    rfl

theorem cell20_686841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_686841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686841 prefixEnd_686841 := by exact prefixLift 686841
  have htrace : WordTrace (prefixWord ++ tailWord_686841) baseStart_686841 baseEnd_686841 := by
    simpa [prefixWord, tailWord_686841, baseEnd_686841] using wordTrace_append hprefix tailTrace_686841
  have hstable : (prefixWord ++ tailWord_686841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686841).length < 2 ^ (prefixWord ++ tailWord_686841).sum := by decide
  have hdescent : baseEnd_686841 < baseStart_686841 := by decide
  rcases family_descends (prefixWord ++ tailWord_686841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686862 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_686862 : Nat := 118140960795 + 686862 * 2 ^ 59
def prefixEnd_686862 : Nat := 4983230072969 + 3 ^ 40 * 686862 * 2
def baseEnd_686862 : Nat := 313502532718752784858831

theorem tailTrace_686862 : CollatzResearch.WordTrace tailWord_686862 prefixEnd_686862 313502532718752784858831 := by
  unfold tailWord_686862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131489404702969441930855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16701276825082503690297893 3131489404702969441930855)
  ·
    refine ⟨4697234107054454162896283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3131489404702969441930855 4697234107054454162896283)
    ·
      refine ⟨7045851160581681244344425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4697234107054454162896283 7045851160581681244344425)
      ·
        refine ⟨5284388370436260933258319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7045851160581681244344425 5284388370436260933258319)
        ·
          refine ⟨7926582555654391399887479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284388370436260933258319 7926582555654391399887479)
          ·
            refine ⟨11889873833481587099831219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926582555654391399887479 11889873833481587099831219)
            ·
              refine ⟨17834810750222380649746829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11889873833481587099831219 17834810750222380649746829)
              ·
                refine ⟨6688054031333392743655061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17834810750222380649746829 6688054031333392743655061)
                ·
                  refine ⟨313502532718752784858831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6688054031333392743655061 313502532718752784858831)
                  ·
                    rfl

theorem cell20_686862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_686862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686862 prefixEnd_686862 := by exact prefixLift 686862
  have htrace : WordTrace (prefixWord ++ tailWord_686862) baseStart_686862 baseEnd_686862 := by
    simpa [prefixWord, tailWord_686862, baseEnd_686862] using wordTrace_append hprefix tailTrace_686862
  have hstable : (prefixWord ++ tailWord_686862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686862).length < 2 ^ (prefixWord ++ tailWord_686862).sum := by decide
  have hdescent : baseEnd_686862 < baseStart_686862 := by decide
  rcases family_descends (prefixWord ++ tailWord_686862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686869 : List Nat := [1, 3, 2, 1, 2, 2, 1, 8]
def baseStart_686869 : Nat := 118140960795 + 686869 * 2 ^ 59
def prefixEnd_686869 : Nat := 4983230072969 + 3 ^ 40 * 686869 * 2
def baseEnd_686869 : Nat := 104501909236497290541823

theorem tailTrace_686869 : CollatzResearch.WordTrace tailWord_686869 prefixEnd_686869 104501909236497290541823 := by
  unfold tailWord_686869
  simp only [CollatzResearch.WordTrace]
  refine ⟨25052170548598395730951661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16701447032398930487301107 25052170548598395730951661)
  ·
    refine ⟨9394563955724398399106873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25052170548598395730951661 9394563955724398399106873)
    ·
      refine ⟨7045922966793298799330155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9394563955724398399106873 7045922966793298799330155)
      ·
        refine ⟨10568884450189948198995233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7045922966793298799330155 10568884450189948198995233)
        ·
          refine ⟨7926663337642461149246425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10568884450189948198995233 7926663337642461149246425)
          ·
            refine ⟨5944997503231845861934819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7926663337642461149246425 5944997503231845861934819)
            ·
              refine ⟨8917496254847768792902229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944997503231845861934819 8917496254847768792902229)
              ·
                refine ⟨104501909236497290541823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8917496254847768792902229 104501909236497290541823)
                ·
                  rfl

theorem cell20_686869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_686869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686869 prefixEnd_686869 := by exact prefixLift 686869
  have htrace : WordTrace (prefixWord ++ tailWord_686869) baseStart_686869 baseEnd_686869 := by
    simpa [prefixWord, tailWord_686869, baseEnd_686869] using wordTrace_append hprefix tailTrace_686869
  have hstable : (prefixWord ++ tailWord_686869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686869).length < 2 ^ (prefixWord ++ tailWord_686869).sum := by decide
  have hdescent : baseEnd_686869 < baseStart_686869 := by decide
  rcases family_descends (prefixWord ++ tailWord_686869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686948 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_686948 : Nat := 118140960795 + 686948 * 2 ^ 59
def prefixEnd_686948 : Nat := 4983230072969 + 3 ^ 40 * 686948 * 2
def baseEnd_686948 : Nat := 313541785462118707991813

theorem tailTrace_686948 : CollatzResearch.WordTrace tailWord_686948 prefixEnd_686948 313541785462118707991813 := by
  unfold tailWord_686948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12527525957656096111538749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16703367943541461482051665 12527525957656096111538749)
  ·
    refine ⟨4697822234121036041827031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12527525957656096111538749 4697822234121036041827031)
    ·
      refine ⟨7046733351181554062740547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4697822234121036041827031 7046733351181554062740547)
      ·
        refine ⟨10570100026772331094110821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7046733351181554062740547 10570100026772331094110821)
        ·
          refine ⟨1981893755019812080145779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10570100026772331094110821 1981893755019812080145779)
          ·
            refine ⟨2972840632529718120218669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981893755019812080145779 2972840632529718120218669)
            ·
              refine ⟨1114815237198644295082001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2972840632529718120218669 1114815237198644295082001)
              ·
                refine ⟨836111427898983221311501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114815237198644295082001 836111427898983221311501)
                ·
                  refine ⟨313541785462118707991813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836111427898983221311501 313541785462118707991813)
                  ·
                    rfl

theorem cell20_686948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_686948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686948 prefixEnd_686948 := by exact prefixLift 686948
  have htrace : WordTrace (prefixWord ++ tailWord_686948) baseStart_686948 baseEnd_686948 := by
    simpa [prefixWord, tailWord_686948, baseEnd_686948] using wordTrace_append hprefix tailTrace_686948
  have hstable : (prefixWord ++ tailWord_686948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686948).length < 2 ^ (prefixWord ++ tailWord_686948).sum := by decide
  have hdescent : baseEnd_686948 < baseStart_686948 := by decide
  rcases family_descends (prefixWord ++ tailWord_686948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686955 : List Nat := [1, 1, 1, 1, 2, 2, 6, 4, 2]
def baseStart_686955 : Nat := 118140960795 + 686955 * 2 ^ 59
def prefixEnd_686955 : Nat := 4983230072969 + 3 ^ 40 * 686955 * 2
def baseEnd_686955 : Nat := 313544980452857794758451

theorem tailTrace_686955 : CollatzResearch.WordTrace tailWord_686955 prefixEnd_686955 313544980452857794758451 := by
  unfold tailWord_686955
  simp only [CollatzResearch.WordTrace]
  refine ⟨25055307226286832418582319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16703538150857888279054879 25055307226286832418582319)
  ·
    refine ⟨37582960839430248627873479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25055307226286832418582319 37582960839430248627873479)
    ·
      refine ⟨56374441259145372941810219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37582960839430248627873479 56374441259145372941810219)
      ·
        refine ⟨84561661888718059412715329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56374441259145372941810219 84561661888718059412715329)
        ·
          refine ⟨63421246416538544559536497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84561661888718059412715329 63421246416538544559536497)
          ·
            refine ⟨47565934812403908419652373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63421246416538544559536497 47565934812403908419652373)
            ·
              refine ⟨2229653194331433207171205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47565934812403908419652373 2229653194331433207171205)
              ·
                refine ⟨418059973937143726344601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2229653194331433207171205 418059973937143726344601)
                ·
                  refine ⟨313544980452857794758451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418059973937143726344601 313544980452857794758451)
                  ·
                    rfl

theorem cell20_686955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 2].length) (baseStart_686955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686955 prefixEnd_686955 := by exact prefixLift 686955
  have htrace : WordTrace (prefixWord ++ tailWord_686955) baseStart_686955 baseEnd_686955 := by
    simpa [prefixWord, tailWord_686955, baseEnd_686955] using wordTrace_append hprefix tailTrace_686955
  have hstable : (prefixWord ++ tailWord_686955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686955).length < 2 ^ (prefixWord ++ tailWord_686955).sum := by decide
  have hdescent : baseEnd_686955 < baseStart_686955 := by decide
  rcases family_descends (prefixWord ++ tailWord_686955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686965 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 3]
def baseStart_686965 : Nat := 118140960795 + 686965 * 2 ^ 59
def prefixEnd_686965 : Nat := 4983230072969 + 3 ^ 40 * 686965 * 2
def baseEnd_686965 : Nat := 313549544725342204425077

theorem tailTrace_686965 : CollatzResearch.WordTrace tailWord_686965 prefixEnd_686965 313549544725342204425077 := by
  unfold tailWord_686965
  simp only [CollatzResearch.WordTrace]
  refine ⟨25055671956250604126446349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16703781304167069417630899 25055671956250604126446349)
  ·
    refine ⟨9395876983593976547417381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25055671956250604126446349 9395876983593976547417381)
    ·
      refine ⟨1761726934423870602640759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9395876983593976547417381 1761726934423870602640759)
      ·
        refine ⟨2642590401635805903961139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761726934423870602640759 2642590401635805903961139)
        ·
          refine ⟨3963885602453708855941709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642590401635805903961139 3963885602453708855941709)
          ·
            refine ⟨1486457100920140820978141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3963885602453708855941709 1486457100920140820978141)
            ·
              refine ⟨557421412845052807866803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1486457100920140820978141 557421412845052807866803)
              ·
                refine ⟨836132119267579211800205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557421412845052807866803 836132119267579211800205)
                ·
                  refine ⟨313549544725342204425077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836132119267579211800205 313549544725342204425077)
                  ·
                    rfl

theorem cell20_686965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_686965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686965 prefixEnd_686965 := by exact prefixLift 686965
  have htrace : WordTrace (prefixWord ++ tailWord_686965) baseStart_686965 baseEnd_686965 := by
    simpa [prefixWord, tailWord_686965, baseEnd_686965] using wordTrace_append hprefix tailTrace_686965
  have hstable : (prefixWord ++ tailWord_686965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686965).length < 2 ^ (prefixWord ++ tailWord_686965).sum := by decide
  have hdescent : baseEnd_686965 < baseStart_686965 := by decide
  rcases family_descends (prefixWord ++ tailWord_686965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687007 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_687007 : Nat := 118140960795 + 687007 * 2 ^ 59
def prefixEnd_687007 : Nat := 4983230072969 + 3 ^ 40 * 687007 * 2
def baseEnd_687007 : Nat := 313568714669776725024905

theorem tailTrace_687007 : CollatzResearch.WordTrace tailWord_687007 prefixEnd_687007 313568714669776725024905 := by
  unfold tailWord_687007
  simp only [CollatzResearch.WordTrace]
  refine ⟨25057203822098445299475275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16704802548065630199650183 25057203822098445299475275)
  ·
    refine ⟨37585805733147667949212913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25057203822098445299475275 37585805733147667949212913)
    ·
      refine ⟨28189354299860750961909685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37585805733147667949212913 28189354299860750961909685)
      ·
        refine ⟨2642751965611945402679033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28189354299860750961909685 2642751965611945402679033)
        ·
          refine ⟨1982063974208959052009275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2642751965611945402679033 1982063974208959052009275)
          ·
            refine ⟨2973095961313438578013913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982063974208959052009275 2973095961313438578013913)
            ·
              refine ⟨2229821970985078933510435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973095961313438578013913 2229821970985078933510435)
              ·
                refine ⟨3344732956477618400265653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229821970985078933510435 3344732956477618400265653)
                ·
                  refine ⟨313568714669776725024905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3344732956477618400265653 313568714669776725024905)
                  ·
                    rfl

theorem cell20_687007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_687007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687007 prefixEnd_687007 := by exact prefixLift 687007
  have htrace : WordTrace (prefixWord ++ tailWord_687007) baseStart_687007 baseEnd_687007 := by
    simpa [prefixWord, tailWord_687007, baseEnd_687007] using wordTrace_append hprefix tailTrace_687007
  have hstable : (prefixWord ++ tailWord_687007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687007).length < 2 ^ (prefixWord ++ tailWord_687007).sum := by decide
  have hdescent : baseEnd_687007 < baseStart_687007 := by decide
  rcases family_descends (prefixWord ++ tailWord_687007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687010 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_687010 : Nat := 118140960795 + 687010 * 2 ^ 59
def prefixEnd_687010 : Nat := 4983230072969 + 3 ^ 40 * 687010 * 2
def baseEnd_687010 : Nat := 313570083951522047924893

theorem tailTrace_687010 : CollatzResearch.WordTrace tailWord_687010 prefixEnd_687010 313570083951522047924893 := by
  unfold tailWord_687010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264328310271894202958621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16704875494058384541222989 6264328310271894202958621)
  ·
    refine ⟨2349123116351960326109483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6264328310271894202958621 2349123116351960326109483)
    ·
      refine ⟨3523684674527940489164225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349123116351960326109483 3523684674527940489164225)
      ·
        refine ⟨2642763505895955366873169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3523684674527940489164225 2642763505895955366873169)
        ·
          refine ⟨1982072629421966525154877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2642763505895955366873169 1982072629421966525154877)
          ·
            refine ⟨743277236033237446933079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1982072629421966525154877 743277236033237446933079)
            ·
              refine ⟨1114915854049856170399619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743277236033237446933079 1114915854049856170399619)
              ·
                refine ⟨1672373781074784255599429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114915854049856170399619 1672373781074784255599429)
                ·
                  refine ⟨313570083951522047924893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1672373781074784255599429 313570083951522047924893)
                  ·
                    rfl

theorem cell20_687010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_687010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687010 prefixEnd_687010 := by exact prefixLift 687010
  have htrace : WordTrace (prefixWord ++ tailWord_687010) baseStart_687010 baseEnd_687010 := by
    simpa [prefixWord, tailWord_687010, baseEnd_687010] using wordTrace_append hprefix tailTrace_687010
  have hstable : (prefixWord ++ tailWord_687010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687010).length < 2 ^ (prefixWord ++ tailWord_687010).sum := by decide
  have hdescent : baseEnd_687010 < baseStart_687010 := by decide
  rcases family_descends (prefixWord ++ tailWord_687010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687065 : List Nat := [1, 2, 1, 2, 5, 3, 2, 2, 2]
def baseStart_687065 : Nat := 118140960795 + 687065 * 2 ^ 59
def prefixEnd_687065 : Nat := 4983230072969 + 3 ^ 40 * 687065 * 2
def baseEnd_687065 : Nat := 313595187450186301091335

theorem tailTrace_687065 : CollatzResearch.WordTrace tailWord_687065 prefixEnd_687065 313595187450186301091335 := by
  unfold tailWord_687065
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059319255888321205086649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16706212837258880803391099 25059319255888321205086649)
  ·
    refine ⟨18794489441916240903814987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25059319255888321205086649 18794489441916240903814987)
    ·
      refine ⟨28191734162874361355722481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18794489441916240903814987 28191734162874361355722481)
      ·
        refine ⟨21143800622155771016791861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28191734162874361355722481 21143800622155771016791861)
        ·
          refine ⟨1982231308327103532824237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21143800622155771016791861 1982231308327103532824237)
          ·
            refine ⟨743336740622663824809089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1982231308327103532824237 743336740622663824809089)
            ·
              refine ⟨557502555466997868606817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743336740622663824809089 557502555466997868606817)
              ·
                refine ⟨418126916600248401455113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557502555466997868606817 418126916600248401455113)
                ·
                  refine ⟨313595187450186301091335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418126916600248401455113 313595187450186301091335)
                  ·
                    rfl

theorem cell20_687065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_687065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687065 prefixEnd_687065 := by exact prefixLift 687065
  have htrace : WordTrace (prefixWord ++ tailWord_687065) baseStart_687065 baseEnd_687065 := by
    simpa [prefixWord, tailWord_687065, baseEnd_687065] using wordTrace_append hprefix tailTrace_687065
  have hstable : (prefixWord ++ tailWord_687065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687065).length < 2 ^ (prefixWord ++ tailWord_687065).sum := by decide
  have hdescent : baseEnd_687065 < baseStart_687065 := by decide
  rcases family_descends (prefixWord ++ tailWord_687065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687128 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_687128 : Nat := 118140960795 + 687128 * 2 ^ 59
def prefixEnd_687128 : Nat := 4983230072969 + 3 ^ 40 * 687128 * 2
def baseEnd_687128 : Nat := 313623942366838081991077

theorem tailTrace_687128 : CollatzResearch.WordTrace tailWord_687128 prefixEnd_687128 313623942366838081991077 := by
  unfold tailWord_687128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12530808527330041482315019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16707744703106721976420025 12530808527330041482315019)
  ·
    refine ⟨18796212790995062223472529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12530808527330041482315019 18796212790995062223472529)
    ·
      refine ⟨14097159593246296667604397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18796212790995062223472529 14097159593246296667604397)
      ·
        refine ⟨5286434847467361250351649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14097159593246296667604397 5286434847467361250351649)
        ·
          refine ⟨3964826135600520937763737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286434847467361250351649 3964826135600520937763737)
          ·
            refine ⟨2973619601700390703322803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3964826135600520937763737 2973619601700390703322803)
            ·
              refine ⟨4460429402550586054984205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973619601700390703322803 4460429402550586054984205)
              ·
                refine ⟨1672661025956469770619077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4460429402550586054984205 1672661025956469770619077)
                ·
                  refine ⟨313623942366838081991077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1672661025956469770619077 313623942366838081991077)
                  ·
                    rfl

theorem cell20_687128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_687128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687128 prefixEnd_687128 := by exact prefixLift 687128
  have htrace : WordTrace (prefixWord ++ tailWord_687128) baseStart_687128 baseEnd_687128 := by
    simpa [prefixWord, tailWord_687128, baseEnd_687128] using wordTrace_append hprefix tailTrace_687128
  have hstable : (prefixWord ++ tailWord_687128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687128).length < 2 ^ (prefixWord ++ tailWord_687128).sum := by decide
  have hdescent : baseEnd_687128 < baseStart_687128 := by decide
  rcases family_descends (prefixWord ++ tailWord_687128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687169 : List Nat := [1, 2, 5, 1, 4, 1, 6]
def baseStart_687169 : Nat := 118140960795 + 687169 * 2 ^ 59
def prefixEnd_687169 : Nat := 4983230072969 + 3 ^ 40 * 687169 * 2
def baseEnd_687169 : Nat := 34849183987113795736027

theorem tailTrace_687169 : CollatzResearch.WordTrace tailWord_687169 prefixEnd_687169 34849183987113795736027 := by
  unfold tailWord_687169
  simp only [CollatzResearch.WordTrace]
  refine ⟨25063112447511546966872561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16708741631674364644581707 25063112447511546966872561)
  ·
    refine ⟨18797334335633660225154421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25063112447511546966872561 18797334335633660225154421)
    ·
      refine ⟨1762250093965655646108227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18797334335633660225154421 1762250093965655646108227)
      ·
        refine ⟨2643375140948483469162341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762250093965655646108227 2643375140948483469162341)
        ·
          refine ⟨495632838927840650467939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2643375140948483469162341 495632838927840650467939)
          ·
            refine ⟨743449258391760975701909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495632838927840650467939 743449258391760975701909)
            ·
              refine ⟨34849183987113795736027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 743449258391760975701909 34849183987113795736027)
              ·
                rfl

theorem cell20_687169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 6].length) (baseStart_687169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687169 prefixEnd_687169 := by exact prefixLift 687169
  have htrace : WordTrace (prefixWord ++ tailWord_687169) baseStart_687169 baseEnd_687169 := by
    simpa [prefixWord, tailWord_687169, baseEnd_687169] using wordTrace_append hprefix tailTrace_687169
  have hstable : (prefixWord ++ tailWord_687169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687169).length < 2 ^ (prefixWord ++ tailWord_687169).sum := by decide
  have hdescent : baseEnd_687169 < baseStart_687169 := by decide
  rcases family_descends (prefixWord ++ tailWord_687169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687230 : List Nat := [4, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_687230 : Nat := 118140960795 + 687230 * 2 ^ 59
def prefixEnd_687230 : Nat := 4983230072969 + 3 ^ 40 * 687230 * 2
def baseEnd_687230 : Nat := 313670497946179060590661

theorem tailTrace_687230 : CollatzResearch.WordTrace tailWord_687230 prefixEnd_687230 313670497946179060590661 := by
  unfold tailWord_687230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133167162536319298105393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16710224866860369589895429 3133167162536319298105393)
  ·
    refine ⟨2349875371902239473579045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3133167162536319298105393 2349875371902239473579045)
    ·
      refine ⟨440601632231669901296071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2349875371902239473579045 440601632231669901296071)
      ·
        refine ⟨660902448347504851944107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440601632231669901296071 660902448347504851944107)
        ·
          refine ⟨991353672521257277916161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660902448347504851944107 991353672521257277916161)
          ·
            refine ⟨743515254390942958437121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991353672521257277916161 743515254390942958437121)
            ·
              refine ⟨557636440793207218827841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743515254390942958437121 557636440793207218827841)
              ·
                refine ⟨418227330594905414120881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557636440793207218827841 418227330594905414120881)
                ·
                  refine ⟨313670497946179060590661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418227330594905414120881 313670497946179060590661)
                  ·
                    rfl

theorem cell20_687230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_687230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687230 prefixEnd_687230 := by exact prefixLift 687230
  have htrace : WordTrace (prefixWord ++ tailWord_687230) baseStart_687230 baseEnd_687230 := by
    simpa [prefixWord, tailWord_687230, baseEnd_687230] using wordTrace_append hprefix tailTrace_687230
  have hstable : (prefixWord ++ tailWord_687230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687230).length < 2 ^ (prefixWord ++ tailWord_687230).sum := by decide
  have hdescent : baseEnd_687230 < baseStart_687230 := by decide
  rcases family_descends (prefixWord ++ tailWord_687230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687235 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 3]
def baseStart_687235 : Nat := 118140960795 + 687235 * 2 ^ 59
def prefixEnd_687235 : Nat := 4983230072969 + 3 ^ 40 * 687235 * 2
def baseEnd_687235 : Nat := 313672780082421265423973

theorem tailTrace_687235 : CollatzResearch.WordTrace tailWord_687235 prefixEnd_687235 313672780082421265423973 := by
  unfold tailWord_687235
  simp only [CollatzResearch.WordTrace]
  refine ⟨25065519665272440238775159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16710346443514960159183439 25065519665272440238775159)
  ·
    refine ⟨37598279497908660358162739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25065519665272440238775159 37598279497908660358162739)
    ·
      refine ⟨56397419246862990537244109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37598279497908660358162739 56397419246862990537244109)
      ·
        refine ⟨21149032217573621451466541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56397419246862990537244109 21149032217573621451466541)
        ·
          refine ⟨7930887081590108044299953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21149032217573621451466541 7930887081590108044299953)
          ·
            refine ⟨5948165311192581033224965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7930887081590108044299953 5948165311192581033224965)
            ·
              refine ⟨1115280995848608943729681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5948165311192581033224965 1115280995848608943729681)
              ·
                refine ⟨836460746886456707797261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115280995848608943729681 836460746886456707797261)
                ·
                  refine ⟨313672780082421265423973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836460746886456707797261 313672780082421265423973)
                  ·
                    rfl

theorem cell20_687235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_687235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687235 prefixEnd_687235 := by exact prefixLift 687235
  have htrace : WordTrace (prefixWord ++ tailWord_687235) baseStart_687235 baseEnd_687235 := by
    simpa [prefixWord, tailWord_687235, baseEnd_687235] using wordTrace_append hprefix tailTrace_687235
  have hstable : (prefixWord ++ tailWord_687235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687235).length < 2 ^ (prefixWord ++ tailWord_687235).sum := by decide
  have hdescent : baseEnd_687235 < baseStart_687235 := by decide
  rcases family_descends (prefixWord ++ tailWord_687235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687242 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_687242 : Nat := 118140960795 + 687242 * 2 ^ 59
def prefixEnd_687242 : Nat := 4983230072969 + 3 ^ 40 * 687242 * 2
def baseEnd_687242 : Nat := 313675975073160352190611

theorem tailTrace_687242 : CollatzResearch.WordTrace tailWord_687242 prefixEnd_687242 313675975073160352190611 := by
  unfold tailWord_687242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6266443744061770108569995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16710516650831386956186653 6266443744061770108569995)
  ·
    refine ⟨9399665616092655162854993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6266443744061770108569995 9399665616092655162854993)
    ·
      refine ⟨7049749212069491372141245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9399665616092655162854993 7049749212069491372141245)
      ·
        refine ⟨2643655954526059264552967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7049749212069491372141245 2643655954526059264552967)
        ·
          refine ⟨3965483931789088896829451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643655954526059264552967 3965483931789088896829451)
          ·
            refine ⟨5948225897683633345244177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965483931789088896829451 5948225897683633345244177)
            ·
              refine ⟨4461169423262725008933133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5948225897683633345244177 4461169423262725008933133)
              ·
                refine ⟨1672938533723521878349925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4461169423262725008933133 1672938533723521878349925)
                ·
                  refine ⟨313675975073160352190611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1672938533723521878349925 313675975073160352190611)
                  ·
                    rfl

theorem cell20_687242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_687242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687242 prefixEnd_687242 := by exact prefixLift 687242
  have htrace : WordTrace (prefixWord ++ tailWord_687242) baseStart_687242 baseEnd_687242 := by
    simpa [prefixWord, tailWord_687242, baseEnd_687242] using wordTrace_append hprefix tailTrace_687242
  have hstable : (prefixWord ++ tailWord_687242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687242).length < 2 ^ (prefixWord ++ tailWord_687242).sum := by decide
  have hdescent : baseEnd_687242 < baseStart_687242 := by decide
  rcases family_descends (prefixWord ++ tailWord_687242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687297 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 4]
def baseStart_687297 : Nat := 118140960795 + 687297 * 2 ^ 59
def prefixEnd_687297 : Nat := 4983230072969 + 3 ^ 40 * 687297 * 2
def baseEnd_687297 : Nat := 313701078571824605357053

theorem tailTrace_687297 : CollatzResearch.WordTrace tailWord_687297 prefixEnd_687297 313701078571824605357053 := by
  unfold tailWord_687297
  simp only [CollatzResearch.WordTrace]
  refine ⟨25067780991047824827532145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16711853994031883218354763 25067780991047824827532145)
  ·
    refine ⟨18800835743285868620649109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25067780991047824827532145 18800835743285868620649109)
    ·
      refine ⟨881289175466525091592927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18800835743285868620649109 881289175466525091592927)
      ·
        refine ⟨1321933763199787637389391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881289175466525091592927 1321933763199787637389391)
        ·
          refine ⟨1982900644799681456084087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321933763199787637389391 1982900644799681456084087)
          ·
            refine ⟨2974350967199522184126131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982900644799681456084087 2974350967199522184126131)
            ·
              refine ⟨4461526450799283276189197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974350967199522184126131 4461526450799283276189197)
              ·
                refine ⟨1673072419049731228570949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4461526450799283276189197 1673072419049731228570949)
                ·
                  refine ⟨313701078571824605357053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673072419049731228570949 313701078571824605357053)
                  ·
                    rfl

theorem cell20_687297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_687297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687297 prefixEnd_687297 := by exact prefixLift 687297
  have htrace : WordTrace (prefixWord ++ tailWord_687297) baseStart_687297 baseEnd_687297 := by
    simpa [prefixWord, tailWord_687297, baseEnd_687297] using wordTrace_append hprefix tailTrace_687297
  have hstable : (prefixWord ++ tailWord_687297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687297).length < 2 ^ (prefixWord ++ tailWord_687297).sum := by decide
  have hdescent : baseEnd_687297 < baseStart_687297 := by decide
  rcases family_descends (prefixWord ++ tailWord_687297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687332 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_687332 : Nat := 118140960795 + 687332 * 2 ^ 59
def prefixEnd_687332 : Nat := 4983230072969 + 3 ^ 40 * 687332 * 2
def baseEnd_687332 : Nat := 313717053525520039190243

theorem tailTrace_687332 : CollatzResearch.WordTrace tailWord_687332 prefixEnd_687332 313717053525520039190243 := by
  unfold tailWord_687332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12534528772960512902528125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16712705030614017203370833 12534528772960512902528125)
  ·
    refine ⟨4700448289860192338448047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12534528772960512902528125 4700448289860192338448047)
    ·
      refine ⟨7050672434790288507672071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700448289860192338448047 7050672434790288507672071)
      ·
        refine ⟨10576008652185432761508107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050672434790288507672071 10576008652185432761508107)
        ·
          refine ⟨15864012978278149142262161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10576008652185432761508107 15864012978278149142262161)
          ·
            refine ⟨11898009733708611856696621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15864012978278149142262161 11898009733708611856696621)
            ·
              refine ⟨4461753650140729446261233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11898009733708611856696621 4461753650140729446261233)
              ·
                refine ⟨3346315237605547084695925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461753650140729446261233 3346315237605547084695925)
                ·
                  refine ⟨313717053525520039190243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3346315237605547084695925 313717053525520039190243)
                  ·
                    rfl

theorem cell20_687332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_687332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687332 prefixEnd_687332 := by exact prefixLift 687332
  have htrace : WordTrace (prefixWord ++ tailWord_687332) baseStart_687332 baseEnd_687332 := by
    simpa [prefixWord, tailWord_687332, baseEnd_687332] using wordTrace_append hprefix tailTrace_687332
  have hstable : (prefixWord ++ tailWord_687332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687332).length < 2 ^ (prefixWord ++ tailWord_687332).sum := by decide
  have hdescent : baseEnd_687332 < baseStart_687332 := by decide
  rcases family_descends (prefixWord ++ tailWord_687332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687348 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_687348 : Nat := 118140960795 + 687348 * 2 ^ 59
def prefixEnd_687348 : Nat := 4983230072969 + 3 ^ 40 * 687348 * 2
def baseEnd_687348 : Nat := 313724356361495094656845

theorem tailTrace_687348 : CollatzResearch.WordTrace tailWord_687348 prefixEnd_687348 313724356361495094656845 := by
  unfold tailWord_687348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12534820556931530268819349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16713094075908707025092465 12534820556931530268819349)
  ·
    refine ⟨587569713606165481350907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12534820556931530268819349 587569713606165481350907)
    ·
      refine ⟨881354570409248222026361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587569713606165481350907 881354570409248222026361)
      ·
        refine ⟨661015927806936166519771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 881354570409248222026361 661015927806936166519771)
        ·
          refine ⟨991523891710404249779657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661015927806936166519771 991523891710404249779657)
          ·
            refine ⟨743642918782803187334743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991523891710404249779657 743642918782803187334743)
            ·
              refine ⟨1115464378174204781002115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743642918782803187334743 1115464378174204781002115)
              ·
                refine ⟨1673196567261307171503173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115464378174204781002115 1673196567261307171503173)
                ·
                  refine ⟨313724356361495094656845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673196567261307171503173 313724356361495094656845)
                  ·
                    rfl

theorem cell20_687348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_687348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687348 prefixEnd_687348 := by exact prefixLift 687348
  have htrace : WordTrace (prefixWord ++ tailWord_687348) baseStart_687348 baseEnd_687348 := by
    simpa [prefixWord, tailWord_687348, baseEnd_687348] using wordTrace_append hprefix tailTrace_687348
  have hstable : (prefixWord ++ tailWord_687348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687348).length < 2 ^ (prefixWord ++ tailWord_687348).sum := by decide
  have hdescent : baseEnd_687348 < baseStart_687348 := by decide
  rcases family_descends (prefixWord ++ tailWord_687348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687362 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_687362 : Nat := 118140960795 + 687362 * 2 ^ 59
def prefixEnd_687362 : Nat := 4983230072969 + 3 ^ 40 * 687362 * 2
def baseEnd_687362 : Nat := 313730746342973268190121

theorem tailTrace_687362 : CollatzResearch.WordTrace tailWord_687362 prefixEnd_687362 313730746342973268190121 := by
  unfold tailWord_687362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267537933953085232162085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16713434490541560619098893 6267537933953085232162085)
  ·
    refine ⟨1175163362616203481030391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6267537933953085232162085 1175163362616203481030391)
    ·
      refine ⟨1762745043924305221545587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175163362616203481030391 1762745043924305221545587)
      ·
        refine ⟨2644117565886457832318381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762745043924305221545587 2644117565886457832318381)
        ·
          refine ⟨991544087207421687119393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2644117565886457832318381 991544087207421687119393)
          ·
            refine ⟨743658065405566265339545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991544087207421687119393 743658065405566265339545)
            ·
              refine ⟨557743549054174699004659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743658065405566265339545 557743549054174699004659)
              ·
                refine ⟨836615323581262048506989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557743549054174699004659 836615323581262048506989)
                ·
                  refine ⟨313730746342973268190121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836615323581262048506989 313730746342973268190121)
                  ·
                    rfl

theorem cell20_687362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_687362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687362 prefixEnd_687362 := by exact prefixLift 687362
  have htrace : WordTrace (prefixWord ++ tailWord_687362) baseStart_687362 baseEnd_687362 := by
    simpa [prefixWord, tailWord_687362, baseEnd_687362] using wordTrace_append hprefix tailTrace_687362
  have hstable : (prefixWord ++ tailWord_687362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687362).length < 2 ^ (prefixWord ++ tailWord_687362).sum := by decide
  have hdescent : baseEnd_687362 < baseStart_687362 := by decide
  rcases family_descends (prefixWord ++ tailWord_687362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687363 : List Nat := [1, 1, 1, 3, 2, 5, 2, 5]
def baseStart_687363 : Nat := 118140960795 + 687363 * 2 ^ 59
def prefixEnd_687363 : Nat := 4983230072969 + 3 ^ 40 * 687363 * 2
def baseEnd_687363 : Nat := 104577067590073903052261

theorem tailTrace_687363 : CollatzResearch.WordTrace tailWord_687363 prefixEnd_687363 104577067590073903052261 := by
  unfold tailWord_687363
  simp only [CollatzResearch.WordTrace]
  refine ⟨25070188208808718099434743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16713458805872478732956495 25070188208808718099434743)
  ·
    refine ⟨37605282313213077149152115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25070188208808718099434743 37605282313213077149152115)
    ·
      refine ⟨56407923469819615723728173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37605282313213077149152115 56407923469819615723728173)
      ·
        refine ⟨21152971301182355896398065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56407923469819615723728173 21152971301182355896398065)
        ·
          refine ⟨15864728475886766922298549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21152971301182355896398065 15864728475886766922298549)
          ·
            refine ⟨1487318294614384398965489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15864728475886766922298549 1487318294614384398965489)
            ·
              refine ⟨1115488720960788299224117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487318294614384398965489 1115488720960788299224117)
              ·
                refine ⟨104577067590073903052261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1115488720960788299224117 104577067590073903052261)
                ·
                  rfl

theorem cell20_687363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_687363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687363 prefixEnd_687363 := by exact prefixLift 687363
  have htrace : WordTrace (prefixWord ++ tailWord_687363) baseStart_687363 baseEnd_687363 := by
    simpa [prefixWord, tailWord_687363, baseEnd_687363] using wordTrace_append hprefix tailTrace_687363
  have hstable : (prefixWord ++ tailWord_687363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687363).length < 2 ^ (prefixWord ++ tailWord_687363).sum := by decide
  have hdescent : baseEnd_687363 < baseStart_687363 := by decide
  rcases family_descends (prefixWord ++ tailWord_687363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687377 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_687377 : Nat := 118140960795 + 687377 * 2 ^ 59
def prefixEnd_687377 : Nat := 4983230072969 + 3 ^ 40 * 687377 * 2
def baseEnd_687377 : Nat := 313737592751699882690059

theorem tailTrace_687377 : CollatzResearch.WordTrace tailWord_687377 prefixEnd_687377 313737592751699882690059 := by
  unfold tailWord_687377
  simp only [CollatzResearch.WordTrace]
  refine ⟨25070698830757998490444385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16713799220505332326962923 25070698830757998490444385)
  ·
    refine ⟨18803024123068498867833289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25070698830757998490444385 18803024123068498867833289)
    ·
      refine ⟨14102268092301374150874967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18803024123068498867833289 14102268092301374150874967)
      ·
        refine ⟨21153402138452061226312451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14102268092301374150874967 21153402138452061226312451)
        ·
          refine ⟨31730103207678091839468677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21153402138452061226312451 31730103207678091839468677)
          ·
            refine ⟨5949394351439642219900377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31730103207678091839468677 5949394351439642219900377)
            ·
              refine ⟨4462045763579731664925283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5949394351439642219900377 4462045763579731664925283)
              ·
                refine ⟨6693068645369597497387925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462045763579731664925283 6693068645369597497387925)
                ·
                  refine ⟨313737592751699882690059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6693068645369597497387925 313737592751699882690059)
                  ·
                    rfl

theorem cell20_687377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_687377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687377 prefixEnd_687377 := by exact prefixLift 687377
  have htrace : WordTrace (prefixWord ++ tailWord_687377) baseStart_687377 baseEnd_687377 := by
    simpa [prefixWord, tailWord_687377, baseEnd_687377] using wordTrace_append hprefix tailTrace_687377
  have hstable : (prefixWord ++ tailWord_687377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687377).length < 2 ^ (prefixWord ++ tailWord_687377).sum := by decide
  have hdescent : baseEnd_687377 < baseStart_687377 := by decide
  rcases family_descends (prefixWord ++ tailWord_687377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687411 : List Nat := [1, 1, 1, 2, 5, 3, 1, 4, 2]
def baseStart_687411 : Nat := 118140960795 + 687411 * 2 ^ 59
def prefixEnd_687411 : Nat := 4983230072969 + 3 ^ 40 * 687411 * 2
def baseEnd_687411 : Nat := 313753111278146875556587

theorem tailTrace_687411 : CollatzResearch.WordTrace tailWord_687411 prefixEnd_687411 313753111278146875556587 := by
  unfold tailWord_687411
  simp only [CollatzResearch.WordTrace]
  refine ⟨25071938912634822297182087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16714625941756548198121391 25071938912634822297182087)
  ·
    refine ⟨37607908368952233445773131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25071938912634822297182087 37607908368952233445773131)
    ·
      refine ⟨56411862553428350168659697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37607908368952233445773131 56411862553428350168659697)
      ·
        refine ⟨42308896915071262626494773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56411862553428350168659697 42308896915071262626494773)
        ·
          refine ⟨3966459085787930871233885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42308896915071262626494773 3966459085787930871233885)
          ·
            refine ⟨1487422157170474076712707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3966459085787930871233885 1487422157170474076712707)
            ·
              refine ⟨2231133235755711115069061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487422157170474076712707 2231133235755711115069061)
              ·
                refine ⟨418337481704195834075449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2231133235755711115069061 418337481704195834075449)
                ·
                  refine ⟨313753111278146875556587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418337481704195834075449 313753111278146875556587)
                  ·
                    rfl

theorem cell20_687411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 2].length) (baseStart_687411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687411 prefixEnd_687411 := by exact prefixLift 687411
  have htrace : WordTrace (prefixWord ++ tailWord_687411) baseStart_687411 baseEnd_687411 := by
    simpa [prefixWord, tailWord_687411, baseEnd_687411] using wordTrace_append hprefix tailTrace_687411
  have hstable : (prefixWord ++ tailWord_687411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687411).length < 2 ^ (prefixWord ++ tailWord_687411).sum := by decide
  have hdescent : baseEnd_687411 < baseStart_687411 := by decide
  rcases family_descends (prefixWord ++ tailWord_687411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687414 : List Nat := [5, 1, 2, 3, 1, 2, 1, 5]
def baseStart_687414 : Nat := 118140960795 + 687414 * 2 ^ 59
def prefixEnd_687414 : Nat := 4983230072969 + 3 ^ 40 * 687414 * 2
def baseEnd_687414 : Nat := 104584826853297399485525

theorem tailTrace_687414 : CollatzResearch.WordTrace tailWord_687414 prefixEnd_687414 104584826853297399485525 := by
  unfold tailWord_687414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567003020726497113096331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16714698887749302539694197 1567003020726497113096331)
  ·
    refine ⟨2350504531089745669644497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1567003020726497113096331 2350504531089745669644497)
    ·
      refine ⟨1762878398317309252233373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350504531089745669644497 1762878398317309252233373)
      ·
        refine ⟨661079399368990969587515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1762878398317309252233373 661079399368990969587515)
        ·
          refine ⟨991619099053486454381273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661079399368990969587515 991619099053486454381273)
          ·
            refine ⟨743714324290114840785955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991619099053486454381273 743714324290114840785955)
            ·
              refine ⟨1115571486435172261178933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743714324290114840785955 1115571486435172261178933)
              ·
                refine ⟨104584826853297399485525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1115571486435172261178933 104584826853297399485525)
                ·
                  rfl

theorem cell20_687414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_687414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687414 prefixEnd_687414 := by exact prefixLift 687414
  have htrace : WordTrace (prefixWord ++ tailWord_687414) baseStart_687414 baseEnd_687414 := by
    simpa [prefixWord, tailWord_687414, baseEnd_687414] using wordTrace_append hprefix tailTrace_687414
  have hstable : (prefixWord ++ tailWord_687414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687414).length < 2 ^ (prefixWord ++ tailWord_687414).sum := by decide
  have hdescent : baseEnd_687414 < baseStart_687414 := by decide
  rcases family_descends (prefixWord ++ tailWord_687414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687463 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 5]
def baseStart_687463 : Nat := 118140960795 + 687463 * 2 ^ 59
def prefixEnd_687463 : Nat := 4983230072969 + 3 ^ 40 * 687463 * 2
def baseEnd_687463 : Nat := 313776845495065805823041

theorem tailTrace_687463 : CollatzResearch.WordTrace tailWord_687463 prefixEnd_687463 313776845495065805823041 := by
  unfold tailWord_687463
  simp only [CollatzResearch.WordTrace]
  refine ⟨25073835508446435178075043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16715890338964290118716695 25073835508446435178075043)
  ·
    refine ⟨37610753262669652767112565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25073835508446435178075043 37610753262669652767112565)
    ·
      refine ⟨3526008118375279946916803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37610753262669652767112565 3526008118375279946916803)
      ·
        refine ⟨5289012177562919920375205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3526008118375279946916803 5289012177562919920375205)
        ·
          refine ⟨991689783293047485070351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5289012177562919920375205 991689783293047485070351)
          ·
            refine ⟨1487534674939571227605527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991689783293047485070351 1487534674939571227605527)
            ·
              refine ⟨2231302012409356841408291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487534674939571227605527 2231302012409356841408291)
              ·
                refine ⟨3346953018614035262112437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231302012409356841408291 3346953018614035262112437)
                ·
                  refine ⟨313776845495065805823041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3346953018614035262112437 313776845495065805823041)
                  ·
                    rfl

theorem cell20_687463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_687463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687463 prefixEnd_687463 := by exact prefixLift 687463
  have htrace : WordTrace (prefixWord ++ tailWord_687463) baseStart_687463 baseEnd_687463 := by
    simpa [prefixWord, tailWord_687463, baseEnd_687463] using wordTrace_append hprefix tailTrace_687463
  have hstable : (prefixWord ++ tailWord_687463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687463).length < 2 ^ (prefixWord ++ tailWord_687463).sum := by decide
  have hdescent : baseEnd_687463 < baseStart_687463 := by decide
  rcases family_descends (prefixWord ++ tailWord_687463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687490 : List Nat := [3, 4, 2, 1, 1, 3, 2, 4]
def baseStart_687490 : Nat := 118140960795 + 687490 * 2 ^ 59
def prefixEnd_687490 : Nat := 4983230072969 + 3 ^ 40 * 687490 * 2
def baseEnd_687490 : Nat := 104596389676924570640977

theorem tailTrace_687490 : CollatzResearch.WordTrace tailWord_687490 prefixEnd_687490 104596389676924570640977 := by
  unfold tailWord_687490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268705069837154697326981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16716546852899079192871949 6268705069837154697326981)
  ·
    refine ⟨1175382200594466505748809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6268705069837154697326981 1175382200594466505748809)
    ·
      refine ⟨881536650445849879311607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1175382200594466505748809 881536650445849879311607)
      ·
        refine ⟨1322304975668774818967411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881536650445849879311607 1322304975668774818967411)
        ·
          refine ⟨1983457463503162228451117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322304975668774818967411 1983457463503162228451117)
          ·
            refine ⟨743796548813685835669169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1983457463503162228451117 743796548813685835669169)
            ·
              refine ⟨557847411610264376751877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743796548813685835669169 557847411610264376751877)
              ·
                refine ⟨104596389676924570640977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557847411610264376751877 104596389676924570640977)
                ·
                  rfl

theorem cell20_687490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_687490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687490 prefixEnd_687490 := by exact prefixLift 687490
  have htrace : WordTrace (prefixWord ++ tailWord_687490) baseStart_687490 baseEnd_687490 := by
    simpa [prefixWord, tailWord_687490, baseEnd_687490] using wordTrace_append hprefix tailTrace_687490
  have hstable : (prefixWord ++ tailWord_687490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687490).length < 2 ^ (prefixWord ++ tailWord_687490).sum := by decide
  have hdescent : baseEnd_687490 < baseStart_687490 := by decide
  rcases family_descends (prefixWord ++ tailWord_687490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687577 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 3]
def baseStart_687577 : Nat := 118140960795 + 687577 * 2 ^ 59
def prefixEnd_687577 : Nat := 4983230072969 + 3 ^ 40 * 687577 * 2
def baseEnd_687577 : Nat := 313828878201388076022575

theorem tailTrace_687577 : CollatzResearch.WordTrace tailWord_687577 prefixEnd_687577 313828878201388076022575 := by
  unfold tailWord_687577
  simp only [CollatzResearch.WordTrace]
  refine ⟨25077993430033432647724985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16718662286688955098483323 25077993430033432647724985)
  ·
    refine ⟨18808495072525074485793739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25077993430033432647724985 18808495072525074485793739)
    ·
      refine ⟨28212742608787611728690609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18808495072525074485793739 28212742608787611728690609)
      ·
        refine ⟨21159556956590708796517957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28212742608787611728690609 21159556956590708796517957)
        ·
          refine ⟨3967416929360757899347117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21159556956590708796517957 3967416929360757899347117)
          ·
            refine ⟨1487781348510284212255169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3967416929360757899347117 1487781348510284212255169)
            ·
              refine ⟨1115836011382713159191377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487781348510284212255169 1115836011382713159191377)
              ·
                refine ⟨836877008537034869393533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115836011382713159191377 836877008537034869393533)
                ·
                  refine ⟨313828878201388076022575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836877008537034869393533 313828878201388076022575)
                  ·
                    rfl

theorem cell20_687577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_687577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687577 prefixEnd_687577 := by exact prefixLift 687577
  have htrace : WordTrace (prefixWord ++ tailWord_687577) baseStart_687577 baseEnd_687577 := by
    simpa [prefixWord, tailWord_687577, baseEnd_687577] using wordTrace_append hprefix tailTrace_687577
  have hstable : (prefixWord ++ tailWord_687577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687577).length < 2 ^ (prefixWord ++ tailWord_687577).sum := by decide
  have hdescent : baseEnd_687577 < baseStart_687577 := by decide
  rcases family_descends (prefixWord ++ tailWord_687577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687591 : List Nat := [1, 1, 5, 2, 1, 2, 3, 5]
def baseStart_687591 : Nat := 118140960795 + 687591 * 2 ^ 59
def prefixEnd_687591 : Nat := 4983230072969 + 3 ^ 40 * 687591 * 2
def baseEnd_687591 : Nat := 104611756060955416518617

theorem tailTrace_687591 : CollatzResearch.WordTrace tailWord_687591 prefixEnd_687591 104611756060955416518617 := by
  unfold tailWord_687591
  simp only [CollatzResearch.WordTrace]
  refine ⟨25078504051982713038734627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16719002701321808692489751 25078504051982713038734627)
  ·
    refine ⟨37617756077974069558101941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25078504051982713038734627 37617756077974069558101941)
    ·
      refine ⟨3526664632310069021072057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37617756077974069558101941 3526664632310069021072057)
      ·
        refine ⟨2644998474232551765804043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3526664632310069021072057 2644998474232551765804043)
        ·
          refine ⟨3967497711348827648706065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644998474232551765804043 3967497711348827648706065)
          ·
            refine ⟨2975623283511620736529549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3967497711348827648706065 2975623283511620736529549)
            ·
              refine ⟨1115858731316857776198581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2975623283511620736529549 1115858731316857776198581)
              ·
                refine ⟨104611756060955416518617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1115858731316857776198581 104611756060955416518617)
                ·
                  rfl

theorem cell20_687591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_687591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687591 prefixEnd_687591 := by exact prefixLift 687591
  have htrace : WordTrace (prefixWord ++ tailWord_687591) baseStart_687591 baseEnd_687591 := by
    simpa [prefixWord, tailWord_687591, baseEnd_687591] using wordTrace_append hprefix tailTrace_687591
  have hstable : (prefixWord ++ tailWord_687591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687591).length < 2 ^ (prefixWord ++ tailWord_687591).sum := by decide
  have hdescent : baseEnd_687591 < baseStart_687591 := by decide
  rcases family_descends (prefixWord ++ tailWord_687591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687612 : List Nat := [2, 2, 2, 1, 2, 1, 2, 8]
def baseStart_687612 : Nat := 118140960795 + 687612 * 2 ^ 59
def prefixEnd_687612 : Nat := 4983230072969 + 3 ^ 40 * 687612 * 2
def baseEnd_687612 : Nat := 104614951051694503285255

theorem tailTrace_687612 : CollatzResearch.WordTrace tailWord_687612 prefixEnd_687612 104614951051694503285255 := by
  unfold tailWord_687612
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539634992453316812624545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16719513323271089083499393 12539634992453316812624545)
  ·
    refine ⟨9404726244339987609468409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12539634992453316812624545 9404726244339987609468409)
    ·
      refine ⟨7053544683254990707101307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9404726244339987609468409 7053544683254990707101307)
      ·
        refine ⟨10580317024882486060651961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7053544683254990707101307 10580317024882486060651961)
        ·
          refine ⟨7935237768661864545488971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10580317024882486060651961 7935237768661864545488971)
          ·
            refine ⟨11902856652992796818233457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935237768661864545488971 11902856652992796818233457)
            ·
              refine ⟨8927142489744597613675093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11902856652992796818233457 8927142489744597613675093)
              ·
                refine ⟨104614951051694503285255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8927142489744597613675093 104614951051694503285255)
                ·
                  rfl

theorem cell20_687612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_687612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687612 prefixEnd_687612 := by exact prefixLift 687612
  have htrace : WordTrace (prefixWord ++ tailWord_687612) baseStart_687612 baseEnd_687612 := by
    simpa [prefixWord, tailWord_687612, baseEnd_687612] using wordTrace_append hprefix tailTrace_687612
  have hstable : (prefixWord ++ tailWord_687612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687612).length < 2 ^ (prefixWord ++ tailWord_687612).sum := by decide
  have hdescent : baseEnd_687612 < baseStart_687612 := by decide
  rcases family_descends (prefixWord ++ tailWord_687612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687618 : List Nat := [3, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_687618 : Nat := 118140960795 + 687618 * 2 ^ 59
def prefixEnd_687618 : Nat := 4983230072969 + 3 ^ 40 * 687618 * 2
def baseEnd_687618 : Nat := 313847591718574155655741

theorem tailTrace_687618 : CollatzResearch.WordTrace tailWord_687618 prefixEnd_687618 313847591718574155655741 := by
  unfold tailWord_687618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269872205721224162491877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16719659215256597766645005 6269872205721224162491877)
  ·
    refine ⟨1175601038572729530467227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6269872205721224162491877 1175601038572729530467227)
    ·
      refine ⟨1763401557859094295700841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175601038572729530467227 1763401557859094295700841)
      ·
        refine ⟨1322551168394320721775631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1763401557859094295700841 1322551168394320721775631)
        ·
          refine ⟨1983826752591481082663447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322551168394320721775631 1983826752591481082663447)
          ·
            refine ⟨2975740128887221623995171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983826752591481082663447 2975740128887221623995171)
            ·
              refine ⟨4463610193330832435992757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975740128887221623995171 4463610193330832435992757)
              ·
                refine ⟨418463455624765540874321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4463610193330832435992757 418463455624765540874321)
                ·
                  refine ⟨313847591718574155655741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418463455624765540874321 313847591718574155655741)
                  ·
                    rfl

theorem cell20_687618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_687618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687618 prefixEnd_687618 := by exact prefixLift 687618
  have htrace : WordTrace (prefixWord ++ tailWord_687618) baseStart_687618 baseEnd_687618 := by
    simpa [prefixWord, tailWord_687618, baseEnd_687618] using wordTrace_append hprefix tailTrace_687618
  have hstable : (prefixWord ++ tailWord_687618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687618).length < 2 ^ (prefixWord ++ tailWord_687618).sum := by decide
  have hdescent : baseEnd_687618 < baseStart_687618 := by decide
  rcases family_descends (prefixWord ++ tailWord_687618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687667 : List Nat := [1, 1, 1, 2, 4, 3, 4, 4]
def baseStart_687667 : Nat := 118140960795 + 687667 * 2 ^ 59
def prefixEnd_687667 : Nat := 4983230072969 + 3 ^ 40 * 687667 * 2
def baseEnd_687667 : Nat := 104623318884582587674069

theorem tailTrace_687667 : CollatzResearch.WordTrace tailWord_687667 prefixEnd_687667 104623318884582587674069 := by
  unfold tailWord_687667
  simp only [CollatzResearch.WordTrace]
  refine ⟨25081275999707378018501255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16720850666471585345667503 25081275999707378018501255)
  ·
    refine ⟨37621913999561067027751883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25081275999707378018501255 37621913999561067027751883)
    ·
      refine ⟨56432870999341600541627825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37621913999561067027751883 56432870999341600541627825)
      ·
        refine ⟨42324653249506200406220869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56432870999341600541627825 42324653249506200406220869)
        ·
          refine ⟨7935872484282412576166413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42324653249506200406220869 7935872484282412576166413)
          ·
            refine ⟨2975952181605904716062405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7935872484282412576166413 2975952181605904716062405)
            ·
              refine ⟨557991034051107134261701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2975952181605904716062405 557991034051107134261701)
              ·
                refine ⟨104623318884582587674069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557991034051107134261701 104623318884582587674069)
                ·
                  rfl

theorem cell20_687667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_687667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687667 prefixEnd_687667 := by exact prefixLift 687667
  have htrace : WordTrace (prefixWord ++ tailWord_687667) baseStart_687667 baseEnd_687667 := by
    simpa [prefixWord, tailWord_687667, baseEnd_687667] using wordTrace_append hprefix tailTrace_687667
  have hstable : (prefixWord ++ tailWord_687667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687667).length < 2 ^ (prefixWord ++ tailWord_687667).sum := by decide
  have hdescent : baseEnd_687667 < baseStart_687667 := by decide
  rcases family_descends (prefixWord ++ tailWord_687667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687698 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_687698 : Nat := 118140960795 + 687698 * 2 ^ 59
def prefixEnd_687698 : Nat := 4983230072969 + 3 ^ 40 * 687698 * 2
def baseEnd_687698 : Nat := 313884105898449432988747

theorem tailTrace_687698 : CollatzResearch.WordTrace tailWord_687698 prefixEnd_687698 313884105898449432988747 := by
  unfold tailWord_687698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6270601665648767578219937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16721604441730046875253165 6270601665648767578219937)
  ·
    refine ⟨4702951249236575683664953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6270601665648767578219937 4702951249236575683664953)
    ·
      refine ⟨3527213436927431762748715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4702951249236575683664953 3527213436927431762748715)
      ·
        refine ⟨5290820155391147644123073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527213436927431762748715 5290820155391147644123073)
        ·
          refine ⟨3968115116543360733092305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5290820155391147644123073 3968115116543360733092305)
          ·
            refine ⟨2976086337407520549819229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3968115116543360733092305 2976086337407520549819229)
            ·
              refine ⟨1116032376527820206182211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2976086337407520549819229 1116032376527820206182211)
              ·
                refine ⟨1674048564791730309273317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116032376527820206182211 1674048564791730309273317)
                ·
                  refine ⟨313884105898449432988747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674048564791730309273317 313884105898449432988747)
                  ·
                    rfl

theorem cell20_687698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_687698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687698 prefixEnd_687698 := by exact prefixLift 687698
  have htrace : WordTrace (prefixWord ++ tailWord_687698) baseStart_687698 baseEnd_687698 := by
    simpa [prefixWord, tailWord_687698, baseEnd_687698] using wordTrace_append hprefix tailTrace_687698
  have hstable : (prefixWord ++ tailWord_687698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687698).length < 2 ^ (prefixWord ++ tailWord_687698).sum := by decide
  have hdescent : baseEnd_687698 < baseStart_687698 := by decide
  rcases family_descends (prefixWord ++ tailWord_687698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687708 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_687708 : Nat := 118140960795 + 687708 * 2 ^ 59
def prefixEnd_687708 : Nat := 4983230072969 + 3 ^ 40 * 687708 * 2
def baseEnd_687708 : Nat := 313888670170933842655373

theorem tailTrace_687708 : CollatzResearch.WordTrace tailWord_687708 prefixEnd_687708 313888670170933842655373 := by
  unfold tailWord_687708
  simp only [CollatzResearch.WordTrace]
  refine ⟨12541385696279421010371889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16721847595039228013829185 12541385696279421010371889)
  ·
    refine ⟨9406039272209565757778917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12541385696279421010371889 9406039272209565757778917)
    ·
      refine ⟨1763632363539293579583547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9406039272209565757778917 1763632363539293579583547)
      ·
        refine ⟨2645448545308940369375321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763632363539293579583547 2645448545308940369375321)
        ·
          refine ⟨1984086408981705277031491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2645448545308940369375321 1984086408981705277031491)
          ·
            refine ⟨2976129613472557915547237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984086408981705277031491 2976129613472557915547237)
            ·
              refine ⟨558024302526104609165107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2976129613472557915547237 558024302526104609165107)
              ·
                refine ⟨837036453789156913747661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558024302526104609165107 837036453789156913747661)
                ·
                  refine ⟨313888670170933842655373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837036453789156913747661 313888670170933842655373)
                  ·
                    rfl

theorem cell20_687708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_687708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687708 prefixEnd_687708 := by exact prefixLift 687708
  have htrace : WordTrace (prefixWord ++ tailWord_687708) baseStart_687708 baseEnd_687708 := by
    simpa [prefixWord, tailWord_687708, baseEnd_687708] using wordTrace_append hprefix tailTrace_687708
  have hstable : (prefixWord ++ tailWord_687708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687708).length < 2 ^ (prefixWord ++ tailWord_687708).sum := by decide
  have hdescent : baseEnd_687708 < baseStart_687708 := by decide
  rcases family_descends (prefixWord ++ tailWord_687708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687719 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_687719 : Nat := 118140960795 + 687719 * 2 ^ 59
def prefixEnd_687719 : Nat := 4983230072969 + 3 ^ 40 * 687719 * 2
def baseEnd_687719 : Nat := 313893690870666693288661

theorem tailTrace_687719 : CollatzResearch.WordTrace tailWord_687719 prefixEnd_687719 313893690870666693288661 := by
  unfold tailWord_687719
  simp only [CollatzResearch.WordTrace]
  refine ⟨25083172595518990899394211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16722115063679327266262807 25083172595518990899394211)
  ·
    refine ⟨37624758893278486349091317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25083172595518990899394211 37624758893278486349091317)
    ·
      refine ⟨3527321146244858095227311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37624758893278486349091317 3527321146244858095227311)
      ·
        refine ⟨5290981719367287142840967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527321146244858095227311 5290981719367287142840967)
        ·
          refine ⟨7936472579050930714261451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290981719367287142840967 7936472579050930714261451)
          ·
            refine ⟨11904708868576396071392177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7936472579050930714261451 11904708868576396071392177)
            ·
              refine ⟨8928531651432297053544133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11904708868576396071392177 8928531651432297053544133)
              ·
                refine ⟨1674099684643555697539525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8928531651432297053544133 1674099684643555697539525)
                ·
                  refine ⟨313893690870666693288661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674099684643555697539525 313893690870666693288661)
                  ·
                    rfl

theorem cell20_687719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_687719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687719 prefixEnd_687719 := by exact prefixLift 687719
  have htrace : WordTrace (prefixWord ++ tailWord_687719) baseStart_687719 baseEnd_687719 := by
    simpa [prefixWord, tailWord_687719, baseEnd_687719] using wordTrace_append hprefix tailTrace_687719
  have hstable : (prefixWord ++ tailWord_687719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687719).length < 2 ^ (prefixWord ++ tailWord_687719).sum := by decide
  have hdescent : baseEnd_687719 < baseStart_687719 := by decide
  rcases family_descends (prefixWord ++ tailWord_687719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687753 : List Nat := [1, 2, 1, 1, 4, 1, 6, 2, 2]
def baseStart_687753 : Nat := 118140960795 + 687753 * 2 ^ 59
def prefixEnd_687753 : Nat := 4983230072969 + 3 ^ 40 * 687753 * 2
def baseEnd_687753 : Nat := 313909209397113686155189

theorem tailTrace_687753 : CollatzResearch.WordTrace tailWord_687753 prefixEnd_687753 313909209397113686155189 := by
  unfold tailWord_687753
  simp only [CollatzResearch.WordTrace]
  refine ⟨25084412677395814706131913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16722941784930543137421275 25084412677395814706131913)
  ·
    refine ⟨18813309508046861029598935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25084412677395814706131913 18813309508046861029598935)
    ·
      refine ⟨28219964262070291544398403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18813309508046861029598935 28219964262070291544398403)
      ·
        refine ⟨42329946393105437316597605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28219964262070291544398403 42329946393105437316597605)
        ·
          refine ⟨7936864948707269496862051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42329946393105437316597605 7936864948707269496862051)
          ·
            refine ⟨11905297423060904245293077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7936864948707269496862051 11905297423060904245293077)
            ·
              refine ⟨558060816705979886498113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11905297423060904245293077 558060816705979886498113)
              ·
                refine ⟨418545612529484914873585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558060816705979886498113 418545612529484914873585)
                ·
                  refine ⟨313909209397113686155189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418545612529484914873585 313909209397113686155189)
                  ·
                    rfl

theorem cell20_687753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_687753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687753 prefixEnd_687753 := by exact prefixLift 687753
  have htrace : WordTrace (prefixWord ++ tailWord_687753) baseStart_687753 baseEnd_687753 := by
    simpa [prefixWord, tailWord_687753, baseEnd_687753] using wordTrace_append hprefix tailTrace_687753
  have hstable : (prefixWord ++ tailWord_687753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687753).length < 2 ^ (prefixWord ++ tailWord_687753).sum := by decide
  have hdescent : baseEnd_687753 < baseStart_687753 := by decide
  rcases family_descends (prefixWord ++ tailWord_687753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687774 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_687774 : Nat := 118140960795 + 687774 * 2 ^ 59
def prefixEnd_687774 : Nat := 4983230072969 + 3 ^ 40 * 687774 * 2
def baseEnd_687774 : Nat := 313918794369330946455103

theorem tailTrace_687774 : CollatzResearch.WordTrace tailWord_687774 prefixEnd_687774 313918794369330946455103 := by
  unfold tailWord_687774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135647326289966911580797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16723452406879823528430917 3135647326289966911580797)
  ·
    refine ⟨1175867747358737591842799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3135647326289966911580797 1175867747358737591842799)
    ·
      refine ⟨1763801621038106387764199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175867747358737591842799 1763801621038106387764199)
      ·
        refine ⟨2645702431557159581646299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763801621038106387764199 2645702431557159581646299)
        ·
          refine ⟨3968553647335739372469449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645702431557159581646299 3968553647335739372469449)
          ·
            refine ⟨2976415235501804529352087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3968553647335739372469449 2976415235501804529352087)
            ·
              refine ⟨4464622853252706794028131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976415235501804529352087 4464622853252706794028131)
              ·
                refine ⟨6696934279879060191042197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464622853252706794028131 6696934279879060191042197)
                ·
                  refine ⟨313918794369330946455103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6696934279879060191042197 313918794369330946455103)
                  ·
                    rfl

theorem cell20_687774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_687774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687774 prefixEnd_687774 := by exact prefixLift 687774
  have htrace : WordTrace (prefixWord ++ tailWord_687774) baseStart_687774 baseEnd_687774 := by
    simpa [prefixWord, tailWord_687774, baseEnd_687774] using wordTrace_append hprefix tailTrace_687774
  have hstable : (prefixWord ++ tailWord_687774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687774).length < 2 ^ (prefixWord ++ tailWord_687774).sum := by decide
  have hdescent : baseEnd_687774 < baseStart_687774 := by decide
  rcases family_descends (prefixWord ++ tailWord_687774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687798 : List Nat := [5, 1, 3, 1, 1, 2, 7]
def baseStart_687798 : Nat := 118140960795 + 687798 * 2 ^ 59
def prefixEnd_687798 : Nat := 4983230072969 + 3 ^ 40 * 687798 * 2
def baseEnd_687798 : Nat := 34881083180365947739445

theorem tailTrace_687798 : CollatzResearch.WordTrace tailWord_687798 prefixEnd_687798 34881083180365947739445 := by
  unfold tailWord_687798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567878372639549211970003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16724035974821858261013365 1567878372639549211970003)
  ·
    refine ⟨2351817558959323817955005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1567878372639549211970003 2351817558959323817955005)
    ·
      refine ⟨881931584609746431733127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2351817558959323817955005 881931584609746431733127)
      ·
        refine ⟨1322897376914619647599691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881931584609746431733127 1322897376914619647599691)
        ·
          refine ⟨1984346065371929471399537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322897376914619647599691 1984346065371929471399537)
          ·
            refine ⟨1488259549028947103549653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1984346065371929471399537 1488259549028947103549653)
            ·
              refine ⟨34881083180365947739445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1488259549028947103549653 34881083180365947739445)
              ·
                rfl

theorem cell20_687798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 7].length) (baseStart_687798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687798 prefixEnd_687798 := by exact prefixLift 687798
  have htrace : WordTrace (prefixWord ++ tailWord_687798) baseStart_687798 baseEnd_687798 := by
    simpa [prefixWord, tailWord_687798, baseEnd_687798] using wordTrace_append hprefix tailTrace_687798
  have hstable : (prefixWord ++ tailWord_687798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687798).length < 2 ^ (prefixWord ++ tailWord_687798).sum := by decide
  have hdescent : baseEnd_687798 < baseStart_687798 := by decide
  rcases family_descends (prefixWord ++ tailWord_687798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687802 : List Nat := [3, 1, 1, 1, 2, 5, 7]
def baseStart_687802 : Nat := 118140960795 + 687802 * 2 ^ 59
def prefixEnd_687802 : Nat := 4983230072969 + 3 ^ 40 * 687802 * 2
def baseEnd_687802 : Nat := 34881286036920810391295

theorem tailTrace_687802 : CollatzResearch.WordTrace tailWord_687802 prefixEnd_687802 34881286036920810391295 := by
  unfold tailWord_687802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6271549963554574018666415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16724133236145530716443773 6271549963554574018666415)
  ·
    refine ⟨9407324945331861027999623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6271549963554574018666415 9407324945331861027999623)
    ·
      refine ⟨14110987417997791541999435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9407324945331861027999623 14110987417997791541999435)
      ·
        refine ⟨21166481126996687312999153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14110987417997791541999435 21166481126996687312999153)
        ·
          refine ⟨15874860845247515484749365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21166481126996687312999153 15874860845247515484749365)
          ·
            refine ⟨1488268204241954576695253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15874860845247515484749365 1488268204241954576695253)
            ·
              refine ⟨34881286036920810391295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1488268204241954576695253 34881286036920810391295)
              ·
                rfl

theorem cell20_687802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 7].length) (baseStart_687802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687802 prefixEnd_687802 := by exact prefixLift 687802
  have htrace : WordTrace (prefixWord ++ tailWord_687802) baseStart_687802 baseEnd_687802 := by
    simpa [prefixWord, tailWord_687802, baseEnd_687802] using wordTrace_append hprefix tailTrace_687802
  have hstable : (prefixWord ++ tailWord_687802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687802).length < 2 ^ (prefixWord ++ tailWord_687802).sum := by decide
  have hdescent : baseEnd_687802 < baseStart_687802 := by decide
  rcases family_descends (prefixWord ++ tailWord_687802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687812 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_687812 : Nat := 118140960795 + 687812 * 2 ^ 59
def prefixEnd_687812 : Nat := 4983230072969 + 3 ^ 40 * 687812 * 2
def baseEnd_687812 : Nat := 313936138604771703188281

theorem tailTrace_687812 : CollatzResearch.WordTrace tailWord_687812 prefixEnd_687812 313936138604771703188281 := by
  unfold tailWord_687812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12543282292091033891264845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16724376389454711855019793 12543282292091033891264845)
  ·
    refine ⟨4703730859534137709224317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12543282292091033891264845 4703730859534137709224317)
    ·
      refine ⟨1763899072325301640959119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4703730859534137709224317 1763899072325301640959119)
      ·
        refine ⟨2645848608487952461438679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763899072325301640959119 2645848608487952461438679)
        ·
          refine ⟨3968772912731928692158019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645848608487952461438679 3968772912731928692158019)
          ·
            refine ⟨5953159369097893038237029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968772912731928692158019 5953159369097893038237029)
            ·
              refine ⟨1116217381705854944669443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5953159369097893038237029 1116217381705854944669443)
              ·
                refine ⟨1674326072558782417004165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116217381705854944669443 1674326072558782417004165)
                ·
                  refine ⟨313936138604771703188281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674326072558782417004165 313936138604771703188281)
                  ·
                    rfl

theorem cell20_687812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_687812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687812 prefixEnd_687812 := by exact prefixLift 687812
  have htrace : WordTrace (prefixWord ++ tailWord_687812) baseStart_687812 baseEnd_687812 := by
    simpa [prefixWord, tailWord_687812, baseEnd_687812] using wordTrace_append hprefix tailTrace_687812
  have hstable : (prefixWord ++ tailWord_687812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687812).length < 2 ^ (prefixWord ++ tailWord_687812).sum := by decide
  have hdescent : baseEnd_687812 < baseStart_687812 := by decide
  rcases family_descends (prefixWord ++ tailWord_687812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687833 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_687833 : Nat := 118140960795 + 687833 * 2 ^ 59
def prefixEnd_687833 : Nat := 4983230072969 + 3 ^ 40 * 687833 * 2
def baseEnd_687833 : Nat := 313945723576988963488195

theorem tailTrace_687833 : CollatzResearch.WordTrace tailWord_687833 prefixEnd_687833 313945723576988963488195 := by
  unfold tailWord_687833
  simp only [CollatzResearch.WordTrace]
  refine ⟨25087330517105988369044153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16724887011403992246029435 25087330517105988369044153)
  ·
    refine ⟨18815497887829491276783115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25087330517105988369044153 18815497887829491276783115)
    ·
      refine ⟨28223246831744236915174673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18815497887829491276783115 28223246831744236915174673)
      ·
        refine ⟨21167435123808177686381005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28223246831744236915174673 21167435123808177686381005)
        ·
          refine ⟨7937788171428066632392877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21167435123808177686381005 7937788171428066632392877)
          ·
            refine ⟨2976670564285524987147329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7937788171428066632392877 2976670564285524987147329)
            ·
              refine ⟨2232502923214143740360497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2976670564285524987147329 2232502923214143740360497)
              ·
                refine ⟨1674377192410607805270373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232502923214143740360497 1674377192410607805270373)
                ·
                  refine ⟨313945723576988963488195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674377192410607805270373 313945723576988963488195)
                  ·
                    rfl

theorem cell20_687833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_687833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687833 prefixEnd_687833 := by exact prefixLift 687833
  have htrace : WordTrace (prefixWord ++ tailWord_687833) baseStart_687833 baseEnd_687833 := by
    simpa [prefixWord, tailWord_687833, baseEnd_687833] using wordTrace_append hprefix tailTrace_687833
  have hstable : (prefixWord ++ tailWord_687833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687833).length < 2 ^ (prefixWord ++ tailWord_687833).sum := by decide
  have hdescent : baseEnd_687833 < baseStart_687833 := by decide
  rcases family_descends (prefixWord ++ tailWord_687833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687836 : List Nat := [2, 2, 5, 1, 2, 1, 1, 6]
def baseStart_687836 : Nat := 118140960795 + 687836 * 2 ^ 59
def prefixEnd_687836 : Nat := 4983230072969 + 3 ^ 40 * 687836 * 2
def baseEnd_687836 : Nat := 104649030952911428796061

theorem tailTrace_687836 : CollatzResearch.WordTrace tailWord_687836 prefixEnd_687836 104649030952911428796061 := by
  unfold tailWord_687836
  simp only [CollatzResearch.WordTrace]
  refine ⟨12543719968047559940701681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16724959957396746587602241 12543719968047559940701681)
  ·
    refine ⟨9407789976035669955526261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12543719968047559940701681 9407789976035669955526261)
    ·
      refine ⟨881980310253344058330587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9407789976035669955526261 881980310253344058330587)
      ·
        refine ⟨1322970465380016087495881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881980310253344058330587 1322970465380016087495881)
        ·
          refine ⟨992227849035012065621911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322970465380016087495881 992227849035012065621911)
          ·
            refine ⟨1488341773552518098432867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992227849035012065621911 1488341773552518098432867)
            ·
              refine ⟨2232512660328777147649301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488341773552518098432867 2232512660328777147649301)
              ·
                refine ⟨104649030952911428796061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2232512660328777147649301 104649030952911428796061)
                ·
                  rfl

theorem cell20_687836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_687836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687836 prefixEnd_687836 := by exact prefixLift 687836
  have htrace : WordTrace (prefixWord ++ tailWord_687836) baseStart_687836 baseEnd_687836 := by
    simpa [prefixWord, tailWord_687836, baseEnd_687836] using wordTrace_append hprefix tailTrace_687836
  have hstable : (prefixWord ++ tailWord_687836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687836).length < 2 ^ (prefixWord ++ tailWord_687836).sum := by decide
  have hdescent : baseEnd_687836 < baseStart_687836 := by decide
  rcases family_descends (prefixWord ++ tailWord_687836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687860 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_687860 : Nat := 118140960795 + 687860 * 2 ^ 59
def prefixEnd_687860 : Nat := 4983230072969 + 3 ^ 40 * 687860 * 2
def baseEnd_687860 : Nat := 313958047112696869588085

theorem tailTrace_687860 : CollatzResearch.WordTrace tailWord_687860 prefixEnd_687860 313958047112696869588085 := by
  unfold tailWord_687860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12544157644004085990138517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16725543525338781320184689 12544157644004085990138517)
  ·
    refine ⟨588007389562691530787743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12544157644004085990138517 588007389562691530787743)
    ·
      refine ⟨882011084344037296181615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588007389562691530787743 882011084344037296181615)
      ·
        refine ⟨1323016626516055944272423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882011084344037296181615 1323016626516055944272423)
        ·
          refine ⟨1984524939774083916408635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323016626516055944272423 1984524939774083916408635)
          ·
            refine ⟨2976787409661125874612953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984524939774083916408635 2976787409661125874612953)
            ·
              refine ⟨2232590557245844405959715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2976787409661125874612953 2232590557245844405959715)
              ·
                refine ⟨3348885835868766608939573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232590557245844405959715 3348885835868766608939573)
                ·
                  refine ⟨313958047112696869588085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348885835868766608939573 313958047112696869588085)
                  ·
                    rfl

theorem cell20_687860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_687860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687860 prefixEnd_687860 := by exact prefixLift 687860
  have htrace : WordTrace (prefixWord ++ tailWord_687860) baseStart_687860 baseEnd_687860 := by
    simpa [prefixWord, tailWord_687860, baseEnd_687860] using wordTrace_append hprefix tailTrace_687860
  have hstable : (prefixWord ++ tailWord_687860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687860).length < 2 ^ (prefixWord ++ tailWord_687860).sum := by decide
  have hdescent : baseEnd_687860 < baseStart_687860 := by decide
  rcases family_descends (prefixWord ++ tailWord_687860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687871 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_687871 : Nat := 118140960795 + 687871 * 2 ^ 59
def prefixEnd_687871 : Nat := 4983230072969 + 3 ^ 40 * 687871 * 2
def baseEnd_687871 : Nat := 313963067812429720221373

theorem tailTrace_687871 : CollatzResearch.WordTrace tailWord_687871 prefixEnd_687871 313963067812429720221373 := by
  unfold tailWord_687871
  simp only [CollatzResearch.WordTrace]
  refine ⟨25088716490968320858927467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16725810993978880572618311 25088716490968320858927467)
  ·
    refine ⟨37633074736452481288391201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25088716490968320858927467 37633074736452481288391201)
    ·
      refine ⟨28224806052339360966293401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37633074736452481288391201 28224806052339360966293401)
      ·
        refine ⟨21168604539254520724720051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28224806052339360966293401 21168604539254520724720051)
        ·
          refine ⟨31752906808881781087080077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21168604539254520724720051 31752906808881781087080077)
          ·
            refine ⟨11907340053330667907655029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31752906808881781087080077 11907340053330667907655029)
            ·
              refine ⟨1116313129999750116342659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11907340053330667907655029 1116313129999750116342659)
              ·
                refine ⟨1674469694999625174513989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116313129999750116342659 1674469694999625174513989)
                ·
                  refine ⟨313963067812429720221373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674469694999625174513989 313963067812429720221373)
                  ·
                    rfl

theorem cell20_687871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_687871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687871 prefixEnd_687871 := by exact prefixLift 687871
  have htrace : WordTrace (prefixWord ++ tailWord_687871) baseStart_687871 baseEnd_687871 := by
    simpa [prefixWord, tailWord_687871, baseEnd_687871] using wordTrace_append hprefix tailTrace_687871
  have hstable : (prefixWord ++ tailWord_687871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687871).length < 2 ^ (prefixWord ++ tailWord_687871).sum := by decide
  have hdescent : baseEnd_687871 < baseStart_687871 := by decide
  rcases family_descends (prefixWord ++ tailWord_687871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687918 : List Nat := [4, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_687918 : Nat := 118140960795 + 687918 * 2 ^ 59
def prefixEnd_687918 : Nat := 4983230072969 + 3 ^ 40 * 687918 * 2
def baseEnd_687918 : Nat := 313984519893106445654515

theorem tailTrace_687918 : CollatzResearch.WordTrace tailWord_687918 prefixEnd_687918 313984519893106445654515 := by
  unfold tailWord_687918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136303840224755985736051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16726953814532031923925605 3136303840224755985736051)
  ·
    refine ⟨4704455760337133978604077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3136303840224755985736051 4704455760337133978604077)
    ·
      refine ⟨1764170910126425241976529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4704455760337133978604077 1764170910126425241976529)
      ·
        refine ⟨1323128182594818931482397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1764170910126425241976529 1323128182594818931482397)
        ·
          refine ⟨496173068473057099305899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1323128182594818931482397 496173068473057099305899)
          ·
            refine ⟨744259602709585648958849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496173068473057099305899 744259602709585648958849)
            ·
              refine ⟨558194702032189236719137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744259602709585648958849 558194702032189236719137)
              ·
                refine ⟨418646026524141927539353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558194702032189236719137 418646026524141927539353)
                ·
                  refine ⟨313984519893106445654515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418646026524141927539353 313984519893106445654515)
                  ·
                    rfl

theorem cell20_687918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_687918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687918 prefixEnd_687918 := by exact prefixLift 687918
  have htrace : WordTrace (prefixWord ++ tailWord_687918) baseStart_687918 baseEnd_687918 := by
    simpa [prefixWord, tailWord_687918, baseEnd_687918] using wordTrace_append hprefix tailTrace_687918
  have hstable : (prefixWord ++ tailWord_687918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687918).length < 2 ^ (prefixWord ++ tailWord_687918).sum := by decide
  have hdescent : baseEnd_687918 < baseStart_687918 := by decide
  rcases family_descends (prefixWord ++ tailWord_687918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687922 : List Nat := [3, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_687922 : Nat := 118140960795 + 687922 * 2 ^ 59
def prefixEnd_687922 : Nat := 4983230072969 + 3 ^ 40 * 687922 * 2
def baseEnd_687922 : Nat := 313986345602100209521165

theorem tailTrace_687922 : CollatzResearch.WordTrace tailWord_687922 prefixEnd_687922 313986345602100209521165 := by
  unfold tailWord_687922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272644153445889142258505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16727051075855704379356013 6272644153445889142258505)
  ·
    refine ⟨4704483115084416856693879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6272644153445889142258505 4704483115084416856693879)
    ·
      refine ⟨7056724672626625285040819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4704483115084416856693879 7056724672626625285040819)
      ·
        refine ⟨10585087008939937927561229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7056724672626625285040819 10585087008939937927561229)
        ·
          refine ⟨3969407628352476722835461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10585087008939937927561229 3969407628352476722835461)
          ·
            refine ⟨744263930316089385531649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3969407628352476722835461 744263930316089385531649)
            ·
              refine ⟨558197947737067039148737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744263930316089385531649 558197947737067039148737)
              ·
                refine ⟨418648460802800279361553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558197947737067039148737 418648460802800279361553)
                ·
                  refine ⟨313986345602100209521165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418648460802800279361553 313986345602100209521165)
                  ·
                    rfl

theorem cell20_687922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_687922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687922 prefixEnd_687922 := by exact prefixLift 687922
  have htrace : WordTrace (prefixWord ++ tailWord_687922) baseStart_687922 baseEnd_687922 := by
    simpa [prefixWord, tailWord_687922, baseEnd_687922] using wordTrace_append hprefix tailTrace_687922
  have hstable : (prefixWord ++ tailWord_687922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687922).length < 2 ^ (prefixWord ++ tailWord_687922).sum := by decide
  have hdescent : baseEnd_687922 < baseStart_687922 := by decide
  rcases family_descends (prefixWord ++ tailWord_687922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687929 : List Nat := [1, 2, 1, 7, 2, 1, 1, 5]
def baseStart_687929 : Nat := 118140960795 + 687929 * 2 ^ 59
def prefixEnd_687929 : Nat := 4983230072969 + 3 ^ 40 * 687929 * 2
def baseEnd_687929 : Nat := 104663180197613098762601

theorem tailTrace_687929 : CollatzResearch.WordTrace tailWord_687929 prefixEnd_687929 104663180197613098762601 := by
  unfold tailWord_687929
  simp only [CollatzResearch.WordTrace]
  refine ⟨25090831924758196764538841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16727221283172131176359227 25090831924758196764538841)
  ·
    refine ⟨18818123943568647573404131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25090831924758196764538841 18818123943568647573404131)
    ·
      refine ⟨28227185915352971360106197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18818123943568647573404131 28227185915352971360106197)
      ·
        refine ⟨661574669891085266252489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28227185915352971360106197 661574669891085266252489)
        ·
          refine ⟨496181002418313949689367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661574669891085266252489 496181002418313949689367)
          ·
            refine ⟨744271503627470924534051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496181002418313949689367 744271503627470924534051)
            ·
              refine ⟨1116407255441206386801077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744271503627470924534051 1116407255441206386801077)
              ·
                refine ⟨104663180197613098762601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1116407255441206386801077 104663180197613098762601)
                ·
                  rfl

theorem cell20_687929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5].length) (baseStart_687929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687929 prefixEnd_687929 := by exact prefixLift 687929
  have htrace : WordTrace (prefixWord ++ tailWord_687929) baseStart_687929 baseEnd_687929 := by
    simpa [prefixWord, tailWord_687929, baseEnd_687929] using wordTrace_append hprefix tailTrace_687929
  have hstable : (prefixWord ++ tailWord_687929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687929).length < 2 ^ (prefixWord ++ tailWord_687929).sum := by decide
  have hdescent : baseEnd_687929 < baseStart_687929 := by decide
  rcases family_descends (prefixWord ++ tailWord_687929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687933 : List Nat := [1, 4, 1, 4, 1, 1, 3, 5]
def baseStart_687933 : Nat := 118140960795 + 687933 * 2 ^ 59
def prefixEnd_687933 : Nat := 4983230072969 + 3 ^ 40 * 687933 * 2
def baseEnd_687933 : Nat := 104663788767277686718151

theorem tailTrace_687933 : CollatzResearch.WordTrace tailWord_687933 prefixEnd_687933 104663788767277686718151 := by
  unfold tailWord_687933
  simp only [CollatzResearch.WordTrace]
  refine ⟨25090977816743705447684453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16727318544495803631789635 25090977816743705447684453)
  ·
    refine ⟨4704558340639444771440835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25090977816743705447684453 4704558340639444771440835)
    ·
      refine ⟨7056837510959167157161253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4704558340639444771440835 7056837510959167157161253)
      ·
        refine ⟨1323157033304843841967735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7056837510959167157161253 1323157033304843841967735)
        ·
          refine ⟨1984735549957265762951603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323157033304843841967735 1984735549957265762951603)
          ·
            refine ⟨2977103324935898644427405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984735549957265762951603 2977103324935898644427405)
            ·
              refine ⟨1116413746850961991660277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2977103324935898644427405 1116413746850961991660277)
              ·
                refine ⟨104663788767277686718151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1116413746850961991660277 104663788767277686718151)
                ·
                  rfl

theorem cell20_687933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_687933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687933 prefixEnd_687933 := by exact prefixLift 687933
  have htrace : WordTrace (prefixWord ++ tailWord_687933) baseStart_687933 baseEnd_687933 := by
    simpa [prefixWord, tailWord_687933, baseEnd_687933] using wordTrace_append hprefix tailTrace_687933
  have hstable : (prefixWord ++ tailWord_687933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687933).length < 2 ^ (prefixWord ++ tailWord_687933).sum := by decide
  have hdescent : baseEnd_687933 < baseStart_687933 := by decide
  rcases family_descends (prefixWord ++ tailWord_687933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687961 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_687961 : Nat := 118140960795 + 687961 * 2 ^ 59
def prefixEnd_687961 : Nat := 4983230072969 + 3 ^ 40 * 687961 * 2
def baseEnd_687961 : Nat := 314004146264789407221005

theorem tailTrace_687961 : CollatzResearch.WordTrace tailWord_687961 prefixEnd_687961 314004146264789407221005 := by
  unfold tailWord_687961
  simp only [CollatzResearch.WordTrace]
  refine ⟨25091999060642266229703737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16727999373761510819802491 25091999060642266229703737)
  ·
    refine ⟨18818999295481699672277803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25091999060642266229703737 18818999295481699672277803)
    ·
      refine ⟨28228498943222549508416705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18818999295481699672277803 28228498943222549508416705)
      ·
        refine ⟨21171374207416912131312529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28228498943222549508416705 21171374207416912131312529)
        ·
          refine ⟨15878530655562684098484397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21171374207416912131312529 15878530655562684098484397)
          ·
            refine ⟨5954448995836006536931649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15878530655562684098484397 5954448995836006536931649)
            ·
              refine ⟨4465836746877004902698737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954448995836006536931649 4465836746877004902698737)
              ·
                refine ⟨3349377560157753677024053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465836746877004902698737 3349377560157753677024053)
                ·
                  refine ⟨314004146264789407221005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3349377560157753677024053 314004146264789407221005)
                  ·
                    rfl

theorem cell20_687961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_687961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687961 prefixEnd_687961 := by exact prefixLift 687961
  have htrace : WordTrace (prefixWord ++ tailWord_687961) baseStart_687961 baseEnd_687961 := by
    simpa [prefixWord, tailWord_687961, baseEnd_687961] using wordTrace_append hprefix tailTrace_687961
  have hstable : (prefixWord ++ tailWord_687961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687961).length < 2 ^ (prefixWord ++ tailWord_687961).sum := by decide
  have hdescent : baseEnd_687961 < baseStart_687961 := by decide
  rcases family_descends (prefixWord ++ tailWord_687961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687985 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_687985 : Nat := 118140960795 + 687985 * 2 ^ 59
def prefixEnd_687985 : Nat := 4983230072969 + 3 ^ 40 * 687985 * 2
def baseEnd_687985 : Nat := 314015100518751990420907

theorem tailTrace_687985 : CollatzResearch.WordTrace tailWord_687985 prefixEnd_687985 314015100518751990420907 := by
  unfold tailWord_687985
  simp only [CollatzResearch.WordTrace]
  refine ⟨25092874412555318328577409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16728582941703545552384939 25092874412555318328577409)
  ·
    refine ⟨18819655809416488746433057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25092874412555318328577409 18819655809416488746433057)
    ·
      refine ⟨14114741857062366559824793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18819655809416488746433057 14114741857062366559824793)
      ·
        refine ⟨10586056392796774919868595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14114741857062366559824793 10586056392796774919868595)
        ·
          refine ⟨15879084589195162379802893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586056392796774919868595 15879084589195162379802893)
          ·
            refine ⟨5954656720948185892426085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15879084589195162379802893 5954656720948185892426085)
            ·
              refine ⟨1116498135177784854829891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5954656720948185892426085 1116498135177784854829891)
              ·
                refine ⟨1674747202766677282244837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116498135177784854829891 1674747202766677282244837)
                ·
                  refine ⟨314015100518751990420907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674747202766677282244837 314015100518751990420907)
                  ·
                    rfl

theorem cell20_687985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_687985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_687985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_687985 prefixEnd_687985 := by exact prefixLift 687985
  have htrace : WordTrace (prefixWord ++ tailWord_687985) baseStart_687985 baseEnd_687985 := by
    simpa [prefixWord, tailWord_687985, baseEnd_687985] using wordTrace_append hprefix tailTrace_687985
  have hstable : (prefixWord ++ tailWord_687985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687985).length < 2 ^ (prefixWord ++ tailWord_687985).sum := by decide
  have hdescent : baseEnd_687985 < baseStart_687985 := by decide
  rcases family_descends (prefixWord ++ tailWord_687985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688022 : List Nat := [5, 3, 1, 1, 3, 1, 6]
def baseStart_688022 : Nat := 118140960795 + 688022 * 2 ^ 59
def prefixEnd_688022 : Nat := 4983230072969 + 3 ^ 40 * 688022 * 2
def baseEnd_688022 : Nat := 34892443147438256243047

theorem tailTrace_688022 : CollatzResearch.WordTrace tailWord_688022 prefixEnd_688022 34892443147438256243047 := by
  unfold tailWord_688022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568388994588829602979645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16729482608947515765116213 1568388994588829602979645)
  ·
    refine ⟨588145872970811101117367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1568388994588829602979645 588145872970811101117367)
    ·
      refine ⟨882218809456216651676051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588145872970811101117367 882218809456216651676051)
      ·
        refine ⟨1323328214184324977514077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882218809456216651676051 1323328214184324977514077)
        ·
          refine ⟨496248080319121866567779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1323328214184324977514077 496248080319121866567779)
          ·
            refine ⟨744372120478682799851669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496248080319121866567779 744372120478682799851669)
            ·
              refine ⟨34892443147438256243047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 744372120478682799851669 34892443147438256243047)
              ·
                rfl

theorem cell20_688022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 6].length) (baseStart_688022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688022 prefixEnd_688022 := by exact prefixLift 688022
  have htrace : WordTrace (prefixWord ++ tailWord_688022) baseStart_688022 baseEnd_688022 := by
    simpa [prefixWord, tailWord_688022, baseEnd_688022] using wordTrace_append hprefix tailTrace_688022
  have hstable : (prefixWord ++ tailWord_688022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688022).length < 2 ^ (prefixWord ++ tailWord_688022).sum := by decide
  have hdescent : baseEnd_688022 < baseStart_688022 := by decide
  rcases family_descends (prefixWord ++ tailWord_688022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688078 : List Nat := [4, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_688078 : Nat := 118140960795 + 688078 * 2 ^ 59
def prefixEnd_688078 : Nat := 4983230072969 + 3 ^ 40 * 688078 * 2
def baseEnd_688078 : Nat := 314057548252857000320527

theorem tailTrace_688078 : CollatzResearch.WordTrace tailWord_688078 prefixEnd_688078 314057548252857000320527 := by
  unfold tailWord_688078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137033300152299401464111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16730844267478930141141925 3137033300152299401464111)
  ·
    refine ⟨4705549950228449102196167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3137033300152299401464111 4705549950228449102196167)
    ·
      refine ⟨7058324925342673653294251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4705549950228449102196167 7058324925342673653294251)
      ·
        refine ⟨10587487388014010479941377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7058324925342673653294251 10587487388014010479941377)
        ·
          refine ⟨7940615541010507859956033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10587487388014010479941377 7940615541010507859956033)
          ·
            refine ⟨5955461655757880894967025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7940615541010507859956033 5955461655757880894967025)
            ·
              refine ⟨4466596241818410671225269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5955461655757880894967025 4466596241818410671225269)
              ·
                refine ⟨418743397670476000427369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4466596241818410671225269 418743397670476000427369)
                ·
                  refine ⟨314057548252857000320527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418743397670476000427369 314057548252857000320527)
                  ·
                    rfl

theorem cell20_688078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_688078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688078 prefixEnd_688078 := by exact prefixLift 688078
  have htrace : WordTrace (prefixWord ++ tailWord_688078) baseStart_688078 baseEnd_688078 := by
    simpa [prefixWord, tailWord_688078, baseEnd_688078] using wordTrace_append hprefix tailTrace_688078
  have hstable : (prefixWord ++ tailWord_688078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688078).length < 2 ^ (prefixWord ++ tailWord_688078).sum := by decide
  have hdescent : baseEnd_688078 < baseStart_688078 := by decide
  rcases family_descends (prefixWord ++ tailWord_688078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688089 : List Nat := [1, 2, 1, 2, 14]
def baseStart_688089 : Nat := 118140960795 + 688089 * 2 ^ 59
def prefixEnd_688089 : Nat := 4983230072969 + 3 ^ 40 * 688089 * 2
def baseEnd_688089 : Nat := 3877315666081356184615

theorem tailTrace_688089 : CollatzResearch.WordTrace tailWord_688089 prefixEnd_688089 3877315666081356184615 := by
  unfold tailWord_688089
  simp only [CollatzResearch.WordTrace]
  refine ⟨25096667604178544090363321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16731111736119029393575547 25096667604178544090363321)
  ·
    refine ⟨18822500703133908067772491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25096667604178544090363321 18822500703133908067772491)
    ·
      refine ⟨28233751054700862101658737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18822500703133908067772491 28233751054700862101658737)
      ·
        refine ⟨21175313291025646576244053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28233751054700862101658737 21175313291025646576244053)
        ·
          refine ⟨3877315666081356184615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 21175313291025646576244053 3877315666081356184615)
          ·
            rfl

theorem cell20_688089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 14].length) (baseStart_688089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688089 prefixEnd_688089 := by exact prefixLift 688089
  have htrace : WordTrace (prefixWord ++ tailWord_688089) baseStart_688089 baseEnd_688089 := by
    simpa [prefixWord, tailWord_688089, baseEnd_688089] using wordTrace_append hprefix tailTrace_688089
  have hstable : (prefixWord ++ tailWord_688089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688089).length < 2 ^ (prefixWord ++ tailWord_688089).sum := by decide
  have hdescent : baseEnd_688089 < baseStart_688089 := by decide
  rcases family_descends (prefixWord ++ tailWord_688089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688095 : List Nat := [1, 1, 2, 3, 4, 1, 4, 2, 2]
def baseStart_688095 : Nat := 118140960795 + 688095 * 2 ^ 59
def prefixEnd_688095 : Nat := 4983230072969 + 3 ^ 40 * 688095 * 2
def baseEnd_688095 : Nat := 314065307516080496753791

theorem tailTrace_688095 : CollatzResearch.WordTrace tailWord_688095 prefixEnd_688095 314065307516080496753791 := by
  unfold tailWord_688095
  simp only [CollatzResearch.WordTrace]
  refine ⟨25096886442156807115081739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16731257628104538076721159 25096886442156807115081739)
  ·
    refine ⟨37645329663235210672622609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25096886442156807115081739 37645329663235210672622609)
    ·
      refine ⟨28233997247426408004466957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37645329663235210672622609 28233997247426408004466957)
      ·
        refine ⟨10587748967784903001675109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28233997247426408004466957 10587748967784903001675109)
        ·
          refine ⟨1985202931459669312814083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10587748967784903001675109 1985202931459669312814083)
          ·
            refine ⟨2977804397189503969221125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985202931459669312814083 2977804397189503969221125)
            ·
              refine ⟨558338324473031994228961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2977804397189503969221125 558338324473031994228961)
              ·
                refine ⟨418753743354773995671721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558338324473031994228961 418753743354773995671721)
                ·
                  refine ⟨314065307516080496753791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418753743354773995671721 314065307516080496753791)
                  ·
                    rfl

theorem cell20_688095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 2].length) (baseStart_688095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688095 prefixEnd_688095 := by exact prefixLift 688095
  have htrace : WordTrace (prefixWord ++ tailWord_688095) baseStart_688095 baseEnd_688095 := by
    simpa [prefixWord, tailWord_688095, baseEnd_688095] using wordTrace_append hprefix tailTrace_688095
  have hstable : (prefixWord ++ tailWord_688095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688095).length < 2 ^ (prefixWord ++ tailWord_688095).sum := by decide
  have hdescent : baseEnd_688095 < baseStart_688095 := by decide
  rcases family_descends (prefixWord ++ tailWord_688095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688120 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_688120 : Nat := 118140960795 + 688120 * 2 ^ 59
def prefixEnd_688120 : Nat := 4983230072969 + 3 ^ 40 * 688120 * 2
def baseEnd_688120 : Nat := 314076718197291520920355

theorem tailTrace_688120 : CollatzResearch.WordTrace tailWord_688120 prefixEnd_688120 314076718197291520920355 := by
  unfold tailWord_688120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12548899133533118192370907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16731865511377490923161209 12548899133533118192370907)
  ·
    refine ⟨18823348700299677288556361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12548899133533118192370907 18823348700299677288556361)
    ·
      refine ⟨14117511525224757966417271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18823348700299677288556361 14117511525224757966417271)
      ·
        refine ⟨21176267287837136949625907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14117511525224757966417271 21176267287837136949625907)
        ·
          refine ⟨31764400931755705424438861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21176267287837136949625907 31764400931755705424438861)
          ·
            refine ⟨11911650349408389534164573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31764400931755705424438861 11911650349408389534164573)
            ·
              refine ⟨4466868881028146075311715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11911650349408389534164573 4466868881028146075311715)
              ·
                refine ⟨6700303321542219112967573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4466868881028146075311715 6700303321542219112967573)
                ·
                  refine ⟨314076718197291520920355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6700303321542219112967573 314076718197291520920355)
                  ·
                    rfl

theorem cell20_688120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_688120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688120 prefixEnd_688120 := by exact prefixLift 688120
  have htrace : WordTrace (prefixWord ++ tailWord_688120) baseStart_688120 baseEnd_688120 := by
    simpa [prefixWord, tailWord_688120, baseEnd_688120] using wordTrace_append hprefix tailTrace_688120
  have hstable : (prefixWord ++ tailWord_688120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688120).length < 2 ^ (prefixWord ++ tailWord_688120).sum := by decide
  have hdescent : baseEnd_688120 < baseStart_688120 := by decide
  rcases family_descends (prefixWord ++ tailWord_688120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688127 : List Nat := [1, 1, 2, 2, 1, 2, 1, 10]
def baseStart_688127 : Nat := 118140960795 + 688127 * 2 ^ 59
def prefixEnd_688127 : Nat := 4983230072969 + 3 ^ 40 * 688127 * 2
def baseEnd_688127 : Nat := 104693304396010202562331

theorem tailTrace_688127 : CollatzResearch.WordTrace tailWord_688127 prefixEnd_688127 104693304396010202562331 := by
  unfold tailWord_688127
  simp only [CollatzResearch.WordTrace]
  refine ⟨25098053578040876580246635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16732035718693917720164423 25098053578040876580246635)
  ·
    refine ⟨37647080367061314870369953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25098053578040876580246635 37647080367061314870369953)
    ·
      refine ⟨28235310275295986152777465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37647080367061314870369953 28235310275295986152777465)
      ·
        refine ⟨21176482706471989614583099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28235310275295986152777465 21176482706471989614583099)
        ·
          refine ⟨31764724059707984421874649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21176482706471989614583099 31764724059707984421874649)
          ·
            refine ⟨23823543044780988316405987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31764724059707984421874649 23823543044780988316405987)
            ·
              refine ⟨35735314567171482474608981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23823543044780988316405987 35735314567171482474608981)
              ·
                refine ⟨104693304396010202562331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35735314567171482474608981 104693304396010202562331)
                ·
                  rfl

theorem cell20_688127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_688127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688127 prefixEnd_688127 := by exact prefixLift 688127
  have htrace : WordTrace (prefixWord ++ tailWord_688127) baseStart_688127 baseEnd_688127 := by
    simpa [prefixWord, tailWord_688127, baseEnd_688127] using wordTrace_append hprefix tailTrace_688127
  have hstable : (prefixWord ++ tailWord_688127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688127).length < 2 ^ (prefixWord ++ tailWord_688127).sum := by decide
  have hdescent : baseEnd_688127 < baseStart_688127 := by decide
  rcases family_descends (prefixWord ++ tailWord_688127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688154 : List Nat := [3, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_688154 : Nat := 118140960795 + 688154 * 2 ^ 59
def prefixEnd_688154 : Nat := 4983230072969 + 3 ^ 40 * 688154 * 2
def baseEnd_688154 : Nat := 314092236723738513786883

theorem tailTrace_688154 : CollatzResearch.WordTrace tailWord_688154 prefixEnd_688154 314092236723738513786883 := by
  unfold tailWord_688154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274759587235765047869879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16732692232628706794319677 6274759587235765047869879)
  ·
    refine ⟨9412139380853647571804819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6274759587235765047869879 9412139380853647571804819)
    ·
      refine ⟨14118209071280471357707229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9412139380853647571804819 14118209071280471357707229)
      ·
        refine ⟨5294328401730176759140211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14118209071280471357707229 5294328401730176759140211)
        ·
          refine ⟨7941492602595265138710317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294328401730176759140211 7941492602595265138710317)
          ·
            refine ⟨2978059725973224427016369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7941492602595265138710317 2978059725973224427016369)
            ·
              refine ⟨2233544794479918320262277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2978059725973224427016369 2233544794479918320262277)
              ·
                refine ⟨418789648964984685049177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2233544794479918320262277 418789648964984685049177)
                ·
                  refine ⟨314092236723738513786883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418789648964984685049177 314092236723738513786883)
                  ·
                    rfl

theorem cell20_688154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_688154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688154 prefixEnd_688154 := by exact prefixLift 688154
  have htrace : WordTrace (prefixWord ++ tailWord_688154) baseStart_688154 baseEnd_688154 := by
    simpa [prefixWord, tailWord_688154, baseEnd_688154] using wordTrace_append hprefix tailTrace_688154
  have hstable : (prefixWord ++ tailWord_688154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688154).length < 2 ^ (prefixWord ++ tailWord_688154).sum := by decide
  have hdescent : baseEnd_688154 < baseStart_688154 := by decide
  rcases family_descends (prefixWord ++ tailWord_688154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688164 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_688164 : Nat := 118140960795 + 688164 * 2 ^ 59
def prefixEnd_688164 : Nat := 4983230072969 + 3 ^ 40 * 688164 * 2
def baseEnd_688164 : Nat := 314096800996222923453509

theorem tailTrace_688164 : CollatzResearch.WordTrace tailWord_688164 prefixEnd_688164 314096800996222923453509 := by
  unfold tailWord_688164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12549701539453415949671773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16732935385937887932895697 12549701539453415949671773)
  ·
    refine ⟨4706138077295030981126915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12549701539453415949671773 4706138077295030981126915)
    ·
      refine ⟨7059207115942546471690373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4706138077295030981126915 7059207115942546471690373)
      ·
        refine ⟨1323601334239227463441945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7059207115942546471690373 1323601334239227463441945)
        ·
          refine ⟨992701000679420597581459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1323601334239227463441945 992701000679420597581459)
          ·
            refine ⟨1489051501019130896372189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992701000679420597581459 1489051501019130896372189)
            ·
              refine ⟨558394312882174086139571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1489051501019130896372189 558394312882174086139571)
              ·
                refine ⟨837591469323261129209357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558394312882174086139571 837591469323261129209357)
                ·
                  refine ⟨314096800996222923453509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837591469323261129209357 314096800996222923453509)
                  ·
                    rfl

theorem cell20_688164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_688164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688164 prefixEnd_688164 := by exact prefixLift 688164
  have htrace : WordTrace (prefixWord ++ tailWord_688164) baseStart_688164 baseEnd_688164 := by
    simpa [prefixWord, tailWord_688164, baseEnd_688164] using wordTrace_append hprefix tailTrace_688164
  have hstable : (prefixWord ++ tailWord_688164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688164).length < 2 ^ (prefixWord ++ tailWord_688164).sum := by decide
  have hdescent : baseEnd_688164 < baseStart_688164 := by decide
  rcases family_descends (prefixWord ++ tailWord_688164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688189 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_688189 : Nat := 118140960795 + 688189 * 2 ^ 59
def prefixEnd_688189 : Nat := 4983230072969 + 3 ^ 40 * 688189 * 2
def baseEnd_688189 : Nat := 314108211677433947620073

theorem tailTrace_688189 : CollatzResearch.WordTrace tailWord_688189 prefixEnd_688189 314108211677433947620073 := by
  unfold tailWord_688189
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100314903816261169003621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16733543269210840779335747 25100314903816261169003621)
  ·
    refine ⟨4706309044465548969188179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25100314903816261169003621 4706309044465548969188179)
    ·
      refine ⟨7059463566698323453782269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4706309044465548969188179 7059463566698323453782269)
      ·
        refine ⟨2647298837511871295168351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7059463566698323453782269 2647298837511871295168351)
        ·
          refine ⟨3970948256267806942752527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647298837511871295168351 3970948256267806942752527)
          ·
            refine ⟨5956422384401710414128791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970948256267806942752527 5956422384401710414128791)
            ·
              refine ⟨8934633576602565621193187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956422384401710414128791 8934633576602565621193187)
              ·
                refine ⟨13401950364903848431789781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8934633576602565621193187 13401950364903848431789781)
                ·
                  refine ⟨314108211677433947620073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13401950364903848431789781 314108211677433947620073)
                  ·
                    rfl

theorem cell20_688189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_688189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688189 prefixEnd_688189 := by exact prefixLift 688189
  have htrace : WordTrace (prefixWord ++ tailWord_688189) baseStart_688189 baseEnd_688189 := by
    simpa [prefixWord, tailWord_688189, baseEnd_688189] using wordTrace_append hprefix tailTrace_688189
  have hstable : (prefixWord ++ tailWord_688189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688189).length < 2 ^ (prefixWord ++ tailWord_688189).sum := by decide
  have hdescent : baseEnd_688189 < baseStart_688189 := by decide
  rcases family_descends (prefixWord ++ tailWord_688189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688192 : List Nat := [2, 1, 1, 2, 2, 4, 3, 3, 2]
def baseStart_688192 : Nat := 118140960795 + 688192 * 2 ^ 59
def prefixEnd_688192 : Nat := 4983230072969 + 3 ^ 40 * 688192 * 2
def baseEnd_688192 : Nat := 314109580959179270520061

theorem tailTrace_688192 : CollatzResearch.WordTrace tailWord_688192 prefixEnd_688192 314109580959179270520061 := by
  unfold tailWord_688192
  simp only [CollatzResearch.WordTrace]
  refine ⟨12550212161402696340681415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16733616215203595120908553 12550212161402696340681415)
  ·
    refine ⟨18825318242104044511022123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12550212161402696340681415 18825318242104044511022123)
    ·
      refine ⟨28237977363156066766533185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18825318242104044511022123 28237977363156066766533185)
      ·
        refine ⟨21178483022367050074899889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28237977363156066766533185 21178483022367050074899889)
        ·
          refine ⟨15883862266775287556174917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21178483022367050074899889 15883862266775287556174917)
          ·
            refine ⟨2978224175020366416782797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15883862266775287556174917 2978224175020366416782797)
            ·
              refine ⟨1116834065632637406293549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2978224175020366416782797 1116834065632637406293549)
              ·
                refine ⟨418812774612239027360081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1116834065632637406293549 418812774612239027360081)
                ·
                  refine ⟨314109580959179270520061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418812774612239027360081 314109580959179270520061)
                  ·
                    rfl

theorem cell20_688192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_688192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688192 prefixEnd_688192 := by exact prefixLift 688192
  have htrace : WordTrace (prefixWord ++ tailWord_688192) baseStart_688192 baseEnd_688192 := by
    simpa [prefixWord, tailWord_688192, baseEnd_688192] using wordTrace_append hprefix tailTrace_688192
  have hstable : (prefixWord ++ tailWord_688192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688192).length < 2 ^ (prefixWord ++ tailWord_688192).sum := by decide
  have hdescent : baseEnd_688192 < baseStart_688192 := by decide
  rcases family_descends (prefixWord ++ tailWord_688192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688213 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_688213 : Nat := 118140960795 + 688213 * 2 ^ 59
def prefixEnd_688213 : Nat := 4983230072969 + 3 ^ 40 * 688213 * 2
def baseEnd_688213 : Nat := 314119165931396530819975

theorem tailTrace_688213 : CollatzResearch.WordTrace tailWord_688213 prefixEnd_688213 314119165931396530819975 := by
  unfold tailWord_688213
  simp only [CollatzResearch.WordTrace]
  refine ⟨25101190255729313267877293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16734126837152875511918195 25101190255729313267877293)
  ·
    refine ⟨9412946345898492475453985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25101190255729313267877293 9412946345898492475453985)
    ·
      refine ⟨7059709759423869356590489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9412946345898492475453985 7059709759423869356590489)
      ·
        refine ⟨5294782319567902017442867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7059709759423869356590489 5294782319567902017442867)
        ·
          refine ⟨7942173479351853026164301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294782319567902017442867 7942173479351853026164301)
          ·
            refine ⟨2978315054756944884811613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7942173479351853026164301 2978315054756944884811613)
            ·
              refine ⟨1116868145533854331804355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2978315054756944884811613 1116868145533854331804355)
              ·
                refine ⟨1675302218300781497706533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116868145533854331804355 1675302218300781497706533)
                ·
                  refine ⟨314119165931396530819975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675302218300781497706533 314119165931396530819975)
                  ·
                    rfl

theorem cell20_688213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_688213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688213 prefixEnd_688213 := by exact prefixLift 688213
  have htrace : WordTrace (prefixWord ++ tailWord_688213) baseStart_688213 baseEnd_688213 := by
    simpa [prefixWord, tailWord_688213, baseEnd_688213] using wordTrace_append hprefix tailTrace_688213
  have hstable : (prefixWord ++ tailWord_688213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688213).length < 2 ^ (prefixWord ++ tailWord_688213).sum := by decide
  have hdescent : baseEnd_688213 < baseStart_688213 := by decide
  rcases family_descends (prefixWord ++ tailWord_688213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688220 : List Nat := [2, 2, 4, 1, 1, 2, 1, 7]
def baseStart_688220 : Nat := 118140960795 + 688220 * 2 ^ 59
def prefixEnd_688220 : Nat := 4983230072969 + 3 ^ 40 * 688220 * 2
def baseEnd_688220 : Nat := 104707453640711872528871

theorem tailTrace_688220 : CollatzResearch.WordTrace tailWord_688220 prefixEnd_688220 104707453640711872528871 := by
  unfold tailWord_688220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12550722783351976731691057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16734297044469302308921409 12550722783351976731691057)
  ·
    refine ⟨9413042087513982548768293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12550722783351976731691057 9413042087513982548768293)
    ·
      refine ⟨1764945391408871727894055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9413042087513982548768293 1764945391408871727894055)
      ·
        refine ⟨2647418087113307591841083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764945391408871727894055 2647418087113307591841083)
        ·
          refine ⟨3971127130669961387761625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647418087113307591841083 3971127130669961387761625)
          ·
            refine ⟨2978345348002471040821219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3971127130669961387761625 2978345348002471040821219)
            ·
              refine ⟨4467518022003706561231829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978345348002471040821219 4467518022003706561231829)
              ·
                refine ⟨104707453640711872528871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4467518022003706561231829 104707453640711872528871)
                ·
                  rfl

theorem cell20_688220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_688220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688220 prefixEnd_688220 := by exact prefixLift 688220
  have htrace : WordTrace (prefixWord ++ tailWord_688220) baseStart_688220 baseEnd_688220 := by
    simpa [prefixWord, tailWord_688220, baseEnd_688220] using wordTrace_append hprefix tailTrace_688220
  have hstable : (prefixWord ++ tailWord_688220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688220).length < 2 ^ (prefixWord ++ tailWord_688220).sum := by decide
  have hdescent : baseEnd_688220 < baseStart_688220 := by decide
  rcases family_descends (prefixWord ++ tailWord_688220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688241 : List Nat := [1, 2, 2, 2, 1, 1, 3, 8]
def baseStart_688241 : Nat := 118140960795 + 688241 * 2 ^ 59
def prefixEnd_688241 : Nat := 4983230072969 + 3 ^ 40 * 688241 * 2
def baseEnd_688241 : Nat := 104710648631450959295509

theorem tailTrace_688241 : CollatzResearch.WordTrace tailWord_688241 prefixEnd_688241 104710648631450959295509 := by
  unfold tailWord_688241
  simp only [CollatzResearch.WordTrace]
  refine ⟨25102211499627874049896577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16734807666418582699931051 25102211499627874049896577)
  ·
    refine ⟨18826658624720905537422433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25102211499627874049896577 18826658624720905537422433)
    ·
      refine ⟨14119993968540679153066825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18826658624720905537422433 14119993968540679153066825)
      ·
        refine ⟨10589995476405509364800119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14119993968540679153066825 10589995476405509364800119)
        ·
          refine ⟨15884993214608264047200179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10589995476405509364800119 15884993214608264047200179)
          ·
            refine ⟨23827489821912396070800269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15884993214608264047200179 23827489821912396070800269)
            ·
              refine ⟨8935308683217148526550101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23827489821912396070800269 8935308683217148526550101)
              ·
                refine ⟨104710648631450959295509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8935308683217148526550101 104710648631450959295509)
                ·
                  rfl

theorem cell20_688241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_688241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688241 prefixEnd_688241 := by exact prefixLift 688241
  have htrace : WordTrace (prefixWord ++ tailWord_688241) baseStart_688241 baseEnd_688241 := by
    simpa [prefixWord, tailWord_688241, baseEnd_688241] using wordTrace_append hprefix tailTrace_688241
  have hstable : (prefixWord ++ tailWord_688241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688241).length < 2 ^ (prefixWord ++ tailWord_688241).sum := by decide
  have hdescent : baseEnd_688241 < baseStart_688241 := by decide
  rcases family_descends (prefixWord ++ tailWord_688241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688264 : List Nat := [2, 1, 3, 4, 1, 3, 2, 2, 2]
def baseStart_688264 : Nat := 118140960795 + 688264 * 2 ^ 59
def prefixEnd_688264 : Nat := 4983230072969 + 3 ^ 40 * 688264 * 2
def baseEnd_688264 : Nat := 314142443721067020119767

theorem tailTrace_688264 : CollatzResearch.WordTrace tailWord_688264 prefixEnd_688264 314142443721067020119767 := by
  unfold tailWord_688264
  simp only [CollatzResearch.WordTrace]
  refine ⟨12551525189272274488991923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16735366919029699318655897 12551525189272274488991923)
  ·
    refine ⟨18827287783908411733487885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12551525189272274488991923 18827287783908411733487885)
    ·
      refine ⟨7060232918965654400057957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18827287783908411733487885 7060232918965654400057957)
      ·
        refine ⟨1323793672306060200010867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7060232918965654400057957 1323793672306060200010867)
        ·
          refine ⟨1985690508459090300016301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323793672306060200010867 1985690508459090300016301)
          ·
            refine ⟨744633940672158862506113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1985690508459090300016301 744633940672158862506113)
            ·
              refine ⟨558475455504119146879585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744633940672158862506113 558475455504119146879585)
              ·
                refine ⟨418856591628089360159689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558475455504119146879585 418856591628089360159689)
                ·
                  refine ⟨314142443721067020119767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418856591628089360159689 314142443721067020119767)
                  ·
                    rfl

theorem cell20_688264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_688264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688264 prefixEnd_688264 := by exact prefixLift 688264
  have htrace : WordTrace (prefixWord ++ tailWord_688264) baseStart_688264 baseEnd_688264 := by
    simpa [prefixWord, tailWord_688264, baseEnd_688264] using wordTrace_append hprefix tailTrace_688264
  have hstable : (prefixWord ++ tailWord_688264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688264).length < 2 ^ (prefixWord ++ tailWord_688264).sum := by decide
  have hdescent : baseEnd_688264 < baseStart_688264 := by decide
  rcases family_descends (prefixWord ++ tailWord_688264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688272 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_688272 : Nat := 118140960795 + 688272 * 2 ^ 59
def prefixEnd_688272 : Nat := 4983230072969 + 3 ^ 40 * 688272 * 2
def baseEnd_688272 : Nat := 314146095139054547853067

theorem tailTrace_688272 : CollatzResearch.WordTrace tailWord_688272 prefixEnd_688272 314146095139054547853067 := by
  unfold tailWord_688272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12551671081257783172137535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16735561441677044229516713 12551671081257783172137535)
  ·
    refine ⟨18827506621886674758206303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12551671081257783172137535 18827506621886674758206303)
    ·
      refine ⟨28241259932830012137309455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18827506621886674758206303 28241259932830012137309455)
      ·
        refine ⟨42361889899245018205964183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28241259932830012137309455 42361889899245018205964183)
        ·
          refine ⟨63542834848867527308946275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42361889899245018205964183 63542834848867527308946275)
          ·
            refine ⟨95314252273301290963419413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63542834848867527308946275 95314252273301290963419413)
            ·
              refine ⟨4467855575310998013910285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95314252273301290963419413 4467855575310998013910285)
              ·
                refine ⟨1675445840741624255216357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4467855575310998013910285 1675445840741624255216357)
                ·
                  refine ⟨314146095139054547853067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675445840741624255216357 314146095139054547853067)
                  ·
                    rfl

theorem cell20_688272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_688272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688272 prefixEnd_688272 := by exact prefixLift 688272
  have htrace : WordTrace (prefixWord ++ tailWord_688272) baseStart_688272 baseEnd_688272 := by
    simpa [prefixWord, tailWord_688272, baseEnd_688272] using wordTrace_append hprefix tailTrace_688272
  have hstable : (prefixWord ++ tailWord_688272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688272).length < 2 ^ (prefixWord ++ tailWord_688272).sum := by decide
  have hdescent : baseEnd_688272 < baseStart_688272 := by decide
  rcases family_descends (prefixWord ++ tailWord_688272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688289 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_688289 : Nat := 118140960795 + 688289 * 2 ^ 59
def prefixEnd_688289 : Nat := 4983230072969 + 3 ^ 40 * 688289 * 2
def baseEnd_688289 : Nat := 314153854402278044286331

theorem tailTrace_688289 : CollatzResearch.WordTrace tailWord_688289 prefixEnd_688289 314153854402278044286331 := by
  unfold tailWord_688289
  simp only [CollatzResearch.WordTrace]
  refine ⟨25103962203453978247643921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16735974802302652165095947 25103962203453978247643921)
  ·
    refine ⟨18827971652590483685732941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25103962203453978247643921 18827971652590483685732941)
    ·
      refine ⟨7060489369721431382149853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18827971652590483685732941 7060489369721431382149853)
      ·
        refine ⟨2647683513645536768306195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7060489369721431382149853 2647683513645536768306195)
        ·
          refine ⟨3971525270468305152459293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647683513645536768306195 3971525270468305152459293)
          ·
            refine ⟨1489321976425614432172235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3971525270468305152459293 1489321976425614432172235)
            ·
              refine ⟨2233982964638421648258353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489321976425614432172235 2233982964638421648258353)
              ·
                refine ⟨1675487223478816236193765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233982964638421648258353 1675487223478816236193765)
                ·
                  refine ⟨314153854402278044286331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675487223478816236193765 314153854402278044286331)
                  ·
                    rfl

theorem cell20_688289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_688289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688289 prefixEnd_688289 := by exact prefixLift 688289
  have htrace : WordTrace (prefixWord ++ tailWord_688289) baseStart_688289 baseEnd_688289 := by
    simpa [prefixWord, tailWord_688289, baseEnd_688289] using wordTrace_append hprefix tailTrace_688289
  have hstable : (prefixWord ++ tailWord_688289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688289).length < 2 ^ (prefixWord ++ tailWord_688289).sum := by decide
  have hdescent : baseEnd_688289 < baseStart_688289 := by decide
  rcases family_descends (prefixWord ++ tailWord_688289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688306 : List Nat := [3, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_688306 : Nat := 118140960795 + 688306 * 2 ^ 59
def prefixEnd_688306 : Nat := 4983230072969 + 3 ^ 40 * 688306 * 2
def baseEnd_688306 : Nat := 314161613665501540719595

theorem tailTrace_688306 : CollatzResearch.WordTrace tailWord_688306 prefixEnd_688306 314161613665501540719595 := by
  unfold tailWord_688306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6276145561098097537753193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16736388162928260100675181 6276145561098097537753193)
  ·
    refine ⟨4707109170823573153314895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6276145561098097537753193 4707109170823573153314895)
    ·
      refine ⟨7060663756235359729972343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4707109170823573153314895 7060663756235359729972343)
      ·
        refine ⟨10590995634353039594958515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7060663756235359729972343 10590995634353039594958515)
        ·
          refine ⟨15886493451529559392437773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10590995634353039594958515 15886493451529559392437773)
          ·
            refine ⟨5957435044323584772164165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15886493451529559392437773 5957435044323584772164165)
            ·
              refine ⟨1117019070810672144780781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5957435044323584772164165 1117019070810672144780781)
              ·
                refine ⟨418882151554002054292793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1117019070810672144780781 418882151554002054292793)
                ·
                  refine ⟨314161613665501540719595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418882151554002054292793 314161613665501540719595)
                  ·
                    rfl

theorem cell20_688306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_688306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688306 prefixEnd_688306 := by exact prefixLift 688306
  have htrace : WordTrace (prefixWord ++ tailWord_688306) baseStart_688306 baseEnd_688306 := by
    simpa [prefixWord, tailWord_688306, baseEnd_688306] using wordTrace_append hprefix tailTrace_688306
  have hstable : (prefixWord ++ tailWord_688306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688306).length < 2 ^ (prefixWord ++ tailWord_688306).sum := by decide
  have hdescent : baseEnd_688306 < baseStart_688306 := by decide
  rcases family_descends (prefixWord ++ tailWord_688306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688316 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 3]
def baseStart_688316 : Nat := 118140960795 + 688316 * 2 ^ 59
def prefixEnd_688316 : Nat := 4983230072969 + 3 ^ 40 * 688316 * 2
def baseEnd_688316 : Nat := 314166177937985950386221

theorem tailTrace_688316 : CollatzResearch.WordTrace tailWord_688316 prefixEnd_688316 314166177937985950386221 := by
  unfold tailWord_688316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12552473487178080929438401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16736631316237441239251201 12552473487178080929438401)
  ·
    refine ⟨9414355115383560697078801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12552473487178080929438401 9414355115383560697078801)
    ·
      refine ⟨7060766336537670522809101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9414355115383560697078801 7060766336537670522809101)
      ·
        refine ⟨2647787376201626446053413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7060766336537670522809101 2647787376201626446053413)
        ·
          refine ⟨496460133037804958635015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2647787376201626446053413 496460133037804958635015)
          ·
            refine ⟨744690199556707437952523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496460133037804958635015 744690199556707437952523)
            ·
              refine ⟨1117035299335061156928785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744690199556707437952523 1117035299335061156928785)
              ·
                refine ⟨837776474501295867696589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117035299335061156928785 837776474501295867696589)
                ·
                  refine ⟨314166177937985950386221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837776474501295867696589 314166177937985950386221)
                  ·
                    rfl

theorem cell20_688316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_688316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688316 prefixEnd_688316 := by exact prefixLift 688316
  have htrace : WordTrace (prefixWord ++ tailWord_688316) baseStart_688316 baseEnd_688316 := by
    simpa [prefixWord, tailWord_688316, baseEnd_688316] using wordTrace_append hprefix tailTrace_688316
  have hstable : (prefixWord ++ tailWord_688316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688316).length < 2 ^ (prefixWord ++ tailWord_688316).sum := by decide
  have hdescent : baseEnd_688316 < baseStart_688316 := by decide
  rcases family_descends (prefixWord ++ tailWord_688316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688320 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_688320 : Nat := 118140960795 + 688320 * 2 ^ 59
def prefixEnd_688320 : Nat := 4983230072969 + 3 ^ 40 * 688320 * 2
def baseEnd_688320 : Nat := 314168003646979714252871

theorem tailTrace_688320 : CollatzResearch.WordTrace tailWord_688320 prefixEnd_688320 314168003646979714252871 := by
  unfold tailWord_688320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12552546433170835271011207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16736728577561113694681609 12552546433170835271011207)
  ·
    refine ⟨18828819649756252906516811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12552546433170835271011207 18828819649756252906516811)
    ·
      refine ⟨28243229474634379359775217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18828819649756252906516811 28243229474634379359775217)
      ·
        refine ⟨21182422105975784519831413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28243229474634379359775217 21182422105975784519831413)
        ·
          refine ⟨1985852072435229798734195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21182422105975784519831413 1985852072435229798734195)
          ·
            refine ⟨2978778108652844698101293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985852072435229798734195 2978778108652844698101293)
            ·
              refine ⟨1117041790744816761787985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2978778108652844698101293 1117041790744816761787985)
              ·
                refine ⟨837781343058612571340989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117041790744816761787985 837781343058612571340989)
                ·
                  refine ⟨314168003646979714252871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837781343058612571340989 314168003646979714252871)
                  ·
                    rfl

theorem cell20_688320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_688320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688320 prefixEnd_688320 := by exact prefixLift 688320
  have htrace : WordTrace (prefixWord ++ tailWord_688320) baseStart_688320 baseEnd_688320 := by
    simpa [prefixWord, tailWord_688320, baseEnd_688320] using wordTrace_append hprefix tailTrace_688320
  have hstable : (prefixWord ++ tailWord_688320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688320).length < 2 ^ (prefixWord ++ tailWord_688320).sum := by decide
  have hdescent : baseEnd_688320 < baseStart_688320 := by decide
  rcases family_descends (prefixWord ++ tailWord_688320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688393 : List Nat := [1, 2, 1, 1, 3, 4, 1, 7]
def baseStart_688393 : Nat := 118140960795 + 688393 * 2 ^ 59
def prefixEnd_688393 : Nat := 4983230072969 + 3 ^ 40 * 688393 * 2
def baseEnd_688393 : Nat := 104733774278705301606413

theorem tailTrace_688393 : CollatzResearch.WordTrace tailWord_688393 prefixEnd_688393 104733774278705301606413 := by
  unfold tailWord_688393
  simp only [CollatzResearch.WordTrace]
  refine ⟨25107755395077204009429833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16738503596718136006286555 25107755395077204009429833)
  ·
    refine ⟨18830816546307903007072375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25107755395077204009429833 18830816546307903007072375)
    ·
      refine ⟨28246224819461854510608563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18830816546307903007072375 28246224819461854510608563)
      ·
        refine ⟨42369337229192781765912845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28246224819461854510608563 42369337229192781765912845)
        ·
          refine ⟨15888501460947293162217317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42369337229192781765912845 15888501460947293162217317)
          ·
            refine ⟨2979094023927617467915747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15888501460947293162217317 2979094023927617467915747)
            ·
              refine ⟨4468641035891426201873621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979094023927617467915747 4468641035891426201873621)
              ·
                refine ⟨104733774278705301606413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4468641035891426201873621 104733774278705301606413)
                ·
                  rfl

theorem cell20_688393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_688393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688393 prefixEnd_688393 := by exact prefixLift 688393
  have htrace : WordTrace (prefixWord ++ tailWord_688393) baseStart_688393 baseEnd_688393 := by
    simpa [prefixWord, tailWord_688393, baseEnd_688393] using wordTrace_append hprefix tailTrace_688393
  have hstable : (prefixWord ++ tailWord_688393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688393).length < 2 ^ (prefixWord ++ tailWord_688393).sum := by decide
  have hdescent : baseEnd_688393 < baseStart_688393 := by decide
  rcases family_descends (prefixWord ++ tailWord_688393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688430 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_688430 : Nat := 118140960795 + 688430 * 2 ^ 59
def prefixEnd_688430 : Nat := 4983230072969 + 3 ^ 40 * 688430 * 2
def baseEnd_688430 : Nat := 314218210644308220585755

theorem tailTrace_688430 : CollatzResearch.WordTrace tailWord_688430 prefixEnd_688430 314218210644308220585755 := by
  unfold tailWord_688430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138638111992894916065843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16739403263962106219017829 3138638111992894916065843)
  ·
    refine ⟨4707957167989342374098765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3138638111992894916065843 4707957167989342374098765)
    ·
      refine ⟨1765483937996003390287037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4707957167989342374098765 1765483937996003390287037)
      ·
        refine ⟨662056476748501271357639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1765483937996003390287037 662056476748501271357639)
        ·
          refine ⟨993084715122751907036459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662056476748501271357639 993084715122751907036459)
          ·
            refine ⟨1489627072684127860554689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993084715122751907036459 1489627072684127860554689)
            ·
              refine ⟨1117220304513095895416017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489627072684127860554689 1117220304513095895416017)
              ·
                refine ⟨837915228384821921562013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117220304513095895416017 837915228384821921562013)
                ·
                  refine ⟨314218210644308220585755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837915228384821921562013 314218210644308220585755)
                  ·
                    rfl

theorem cell20_688430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_688430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688430 prefixEnd_688430 := by exact prefixLift 688430
  have htrace : WordTrace (prefixWord ++ tailWord_688430) baseStart_688430 baseEnd_688430 := by
    simpa [prefixWord, tailWord_688430, baseEnd_688430] using wordTrace_append hprefix tailTrace_688430
  have hstable : (prefixWord ++ tailWord_688430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688430).length < 2 ^ (prefixWord ++ tailWord_688430).sum := by decide
  have hdescent : baseEnd_688430 < baseStart_688430 := by decide
  rcases family_descends (prefixWord ++ tailWord_688430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688455 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 3]
def baseStart_688455 : Nat := 118140960795 + 688455 * 2 ^ 59
def prefixEnd_688455 : Nat := 4983230072969 + 3 ^ 40 * 688455 * 2
def baseEnd_688455 : Nat := 314229621325519244752319

theorem tailTrace_688455 : CollatzResearch.WordTrace tailWord_688455 prefixEnd_688455 314229621325519244752319 := by
  unfold tailWord_688455
  simp only [CollatzResearch.WordTrace]
  refine ⟨25110016720852588598186819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16740011147235059065457879 25110016720852588598186819)
  ·
    refine ⟨37665025081278882897280229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25110016720852588598186819 37665025081278882897280229)
    ·
      refine ⟨7062192202739790543240043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37665025081278882897280229 7062192202739790543240043)
      ·
        refine ⟨10593288304109685814860065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7062192202739790543240043 10593288304109685814860065)
        ·
          refine ⟨7944966228082264361145049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10593288304109685814860065 7944966228082264361145049)
          ·
            refine ⟨5958724671061698270858787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7944966228082264361145049 5958724671061698270858787)
            ·
              refine ⟨8938087006592547406288181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5958724671061698270858787 8938087006592547406288181)
              ·
                refine ⟨837945656868051319339517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8938087006592547406288181 837945656868051319339517)
                ·
                  refine ⟨314229621325519244752319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837945656868051319339517 314229621325519244752319)
                  ·
                    rfl

theorem cell20_688455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_688455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688455 prefixEnd_688455 := by exact prefixLift 688455
  have htrace : WordTrace (prefixWord ++ tailWord_688455) baseStart_688455 baseEnd_688455 := by
    simpa [prefixWord, tailWord_688455, baseEnd_688455] using wordTrace_append hprefix tailTrace_688455
  have hstable : (prefixWord ++ tailWord_688455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688455).length < 2 ^ (prefixWord ++ tailWord_688455).sum := by decide
  have hdescent : baseEnd_688455 < baseStart_688455 := by decide
  rcases family_descends (prefixWord ++ tailWord_688455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688479 : List Nat := [1, 1, 2, 3, 1, 2, 3, 5, 2]
def baseStart_688479 : Nat := 118140960795 + 688479 * 2 ^ 59
def prefixEnd_688479 : Nat := 4983230072969 + 3 ^ 40 * 688479 * 2
def baseEnd_688479 : Nat := 314240575579481827952221

theorem tailTrace_688479 : CollatzResearch.WordTrace tailWord_688479 prefixEnd_688479 314240575579481827952221 := by
  unfold tailWord_688479
  simp only [CollatzResearch.WordTrace]
  refine ⟨25110892072765640697060491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16740594715177093798040327 25110892072765640697060491)
  ·
    refine ⟨37666338109148461045590737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25110892072765640697060491 37666338109148461045590737)
    ·
      refine ⟨28249753581861345784193053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37666338109148461045590737 28249753581861345784193053)
      ·
        refine ⟨10593657593198004669072395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28249753581861345784193053 10593657593198004669072395)
        ·
          refine ⟨15890486389797007003608593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10593657593198004669072395 15890486389797007003608593)
          ·
            refine ⟨11917864792347755252706445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15890486389797007003608593 11917864792347755252706445)
            ·
              refine ⟨4469199297130408219764917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11917864792347755252706445 4469199297130408219764917)
              ·
                refine ⟨418987434105975770602961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4469199297130408219764917 418987434105975770602961)
                ·
                  refine ⟨314240575579481827952221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418987434105975770602961 314240575579481827952221)
                  ·
                    rfl

theorem cell20_688479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 2].length) (baseStart_688479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688479 prefixEnd_688479 := by exact prefixLift 688479
  have htrace : WordTrace (prefixWord ++ tailWord_688479) baseStart_688479 baseEnd_688479 := by
    simpa [prefixWord, tailWord_688479, baseEnd_688479] using wordTrace_append hprefix tailTrace_688479
  have hstable : (prefixWord ++ tailWord_688479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688479).length < 2 ^ (prefixWord ++ tailWord_688479).sum := by decide
  have hdescent : baseEnd_688479 < baseStart_688479 := by decide
  rcases family_descends (prefixWord ++ tailWord_688479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688493 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_688493 : Nat := 118140960795 + 688493 * 2 ^ 59
def prefixEnd_688493 : Nat := 4983230072969 + 3 ^ 40 * 688493 * 2
def baseEnd_688493 : Nat := 314246965560960001485497

theorem tailTrace_688493 : CollatzResearch.WordTrace tailWord_688493 prefixEnd_688493 314246965560960001485497 := by
  unfold tailWord_688493
  simp only [CollatzResearch.WordTrace]
  refine ⟨25111402694714921088070133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16740935129809947392046755 25111402694714921088070133)
  ·
    refine ⟨2354194002629523852006575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25111402694714921088070133 2354194002629523852006575)
    ·
      refine ⟨3531291003944285778009863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354194002629523852006575 3531291003944285778009863)
      ·
        refine ⟨5296936505916428667014795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531291003944285778009863 5296936505916428667014795)
        ·
          refine ⟨7945404758874643000522193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296936505916428667014795 7945404758874643000522193)
          ·
            refine ⟨5959053569155982250391645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7945404758874643000522193 5959053569155982250391645)
            ·
              refine ⟨2234645088433493343896867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5959053569155982250391645 2234645088433493343896867)
              ·
                refine ⟨3351967632650240015845301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234645088433493343896867 3351967632650240015845301)
                ·
                  refine ⟨314246965560960001485497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3351967632650240015845301 314246965560960001485497)
                  ·
                    rfl

theorem cell20_688493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_688493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688493 prefixEnd_688493 := by exact prefixLift 688493
  have htrace : WordTrace (prefixWord ++ tailWord_688493) baseStart_688493 baseEnd_688493 := by
    simpa [prefixWord, tailWord_688493, baseEnd_688493] using wordTrace_append hprefix tailTrace_688493
  have hstable : (prefixWord ++ tailWord_688493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688493).length < 2 ^ (prefixWord ++ tailWord_688493).sum := by decide
  have hdescent : baseEnd_688493 < baseStart_688493 := by decide
  rcases family_descends (prefixWord ++ tailWord_688493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688524 : List Nat := [2, 2, 1, 2, 1, 4, 4, 4]
def baseStart_688524 : Nat := 118140960795 + 688524 * 2 ^ 59
def prefixEnd_688524 : Nat := 4983230072969 + 3 ^ 40 * 688524 * 2
def baseEnd_688524 : Nat := 104753704935220557150679

theorem tailTrace_688524 : CollatzResearch.WordTrace tailWord_688524 prefixEnd_688524 104753704935220557150679 := by
  unfold tailWord_688524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12556266678801306691224313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16741688905068408921632417 12556266678801306691224313)
  ·
    refine ⟨9417200009100980018418235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12556266678801306691224313 9417200009100980018418235)
    ·
      refine ⟨14125800013651470027627353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9417200009100980018418235 14125800013651470027627353)
      ·
        refine ⟨10594350010238602520720515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14125800013651470027627353 10594350010238602520720515)
        ·
          refine ⟨15891525015357903781080773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594350010238602520720515 15891525015357903781080773)
          ·
            refine ⟨2979660940379606958952645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15891525015357903781080773 2979660940379606958952645)
            ·
              refine ⟨558686426321176304803621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2979660940379606958952645 558686426321176304803621)
              ·
                refine ⟨104753704935220557150679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558686426321176304803621 104753704935220557150679)
                ·
                  rfl

theorem cell20_688524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_688524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688524 prefixEnd_688524 := by exact prefixLift 688524
  have htrace : WordTrace (prefixWord ++ tailWord_688524) baseStart_688524 baseEnd_688524 := by
    simpa [prefixWord, tailWord_688524, baseEnd_688524] using wordTrace_append hprefix tailTrace_688524
  have hstable : (prefixWord ++ tailWord_688524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688524).length < 2 ^ (prefixWord ++ tailWord_688524).sum := by decide
  have hdescent : baseEnd_688524 < baseStart_688524 := by decide
  rcases family_descends (prefixWord ++ tailWord_688524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688541 : List Nat := [1, 4, 2, 1, 5, 1, 6]
def baseStart_688541 : Nat := 118140960795 + 688541 * 2 ^ 59
def prefixEnd_688541 : Nat := 4983230072969 + 3 ^ 40 * 688541 * 2
def baseEnd_688541 : Nat := 34918763785431685320589

theorem tailTrace_688541 : CollatzResearch.WordTrace tailWord_688541 prefixEnd_688541 34918763785431685320589 := by
  unfold tailWord_688541
  simp only [CollatzResearch.WordTrace]
  refine ⟨25113153398541025285817477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16742102265694016857211651 25113153398541025285817477)
  ·
    refine ⟨4708716262226442241090777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25113153398541025285817477 4708716262226442241090777)
    ·
      refine ⟨3531537196669831680818083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4708716262226442241090777 3531537196669831680818083)
      ·
        refine ⟨5297305795004747521227125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531537196669831680818083 5297305795004747521227125)
        ·
          refine ⟨496622418281695080115043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5297305795004747521227125 496622418281695080115043)
          ·
            refine ⟨744933627422542620172565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496622418281695080115043 744933627422542620172565)
            ·
              refine ⟨34918763785431685320589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 744933627422542620172565 34918763785431685320589)
              ·
                rfl

theorem cell20_688541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 6].length) (baseStart_688541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688541 prefixEnd_688541 := by exact prefixLift 688541
  have htrace : WordTrace (prefixWord ++ tailWord_688541) baseStart_688541 baseEnd_688541 := by
    simpa [prefixWord, tailWord_688541, baseEnd_688541] using wordTrace_append hprefix tailTrace_688541
  have hstable : (prefixWord ++ tailWord_688541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688541).length < 2 ^ (prefixWord ++ tailWord_688541).sum := by decide
  have hdescent : baseEnd_688541 < baseStart_688541 := by decide
  rcases family_descends (prefixWord ++ tailWord_688541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688551 : List Nat := [1, 1, 6, 1, 1, 3, 3, 2, 2]
def baseStart_688551 : Nat := 118140960795 + 688551 * 2 ^ 59
def prefixEnd_688551 : Nat := 4983230072969 + 3 ^ 40 * 688551 * 2
def baseEnd_688551 : Nat := 314273438341369577551927

theorem tailTrace_688551 : CollatzResearch.WordTrace tailWord_688551 prefixEnd_688551 314273438341369577551927 := by
  unfold tailWord_688551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25113518128504796993681507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16742345419003197995787671 25113518128504796993681507)
  ·
    refine ⟨37670277192757195490522261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25113518128504796993681507 37670277192757195490522261)
    ·
      refine ⟨1765794243410493538618231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37670277192757195490522261 1765794243410493538618231)
      ·
        refine ⟨2648691365115740307927347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765794243410493538618231 2648691365115740307927347)
        ·
          refine ⟨3973037047673610461891021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648691365115740307927347 3973037047673610461891021)
          ·
            refine ⟨1489888892877603923209133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3973037047673610461891021 1489888892877603923209133)
            ·
              refine ⟨558708334829101471203425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1489888892877603923209133 558708334829101471203425)
              ·
                refine ⟨419031251121826103402569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558708334829101471203425 419031251121826103402569)
                ·
                  refine ⟨314273438341369577551927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419031251121826103402569 314273438341369577551927)
                  ·
                    rfl

theorem cell20_688551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 2].length) (baseStart_688551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688551 prefixEnd_688551 := by exact prefixLift 688551
  have htrace : WordTrace (prefixWord ++ tailWord_688551) baseStart_688551 baseEnd_688551 := by
    simpa [prefixWord, tailWord_688551, baseEnd_688551] using wordTrace_append hprefix tailTrace_688551
  have hstable : (prefixWord ++ tailWord_688551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688551).length < 2 ^ (prefixWord ++ tailWord_688551).sum := by decide
  have hdescent : baseEnd_688551 < baseStart_688551 := by decide
  rcases family_descends (prefixWord ++ tailWord_688551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688583 : List Nat := [1, 1, 4, 1, 1, 4, 2, 6]
def baseStart_688583 : Nat := 118140960795 + 688583 * 2 ^ 59
def prefixEnd_688583 : Nat := 4983230072969 + 3 ^ 40 * 688583 * 2
def baseEnd_688583 : Nat := 104762681337773229495043

theorem tailTrace_688583 : CollatzResearch.WordTrace tailWord_688583 prefixEnd_688583 104762681337773229495043 := by
  unfold tailWord_688583
  simp only [CollatzResearch.WordTrace]
  refine ⟨25114685264388866458846403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16743123509592577639230935 25114685264388866458846403)
  ·
    refine ⟨37672027896583299688269605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25114685264388866458846403 37672027896583299688269605)
    ·
      refine ⟨7063505230609368691550551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37672027896583299688269605 7063505230609368691550551)
      ·
        refine ⟨10595257845914053037325827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063505230609368691550551 10595257845914053037325827)
        ·
          refine ⟨15892886768871079555988741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10595257845914053037325827 15892886768871079555988741)
          ·
            refine ⟨2979916269163327416747889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15892886768871079555988741 2979916269163327416747889)
            ·
              refine ⟨2234937201872495562560917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2979916269163327416747889 2234937201872495562560917)
              ·
                refine ⟨104762681337773229495043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2234937201872495562560917 104762681337773229495043)
                ·
                  rfl

theorem cell20_688583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_688583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688583 prefixEnd_688583 := by exact prefixLift 688583
  have htrace : WordTrace (prefixWord ++ tailWord_688583) baseStart_688583 baseEnd_688583 := by
    simpa [prefixWord, tailWord_688583, baseEnd_688583] using wordTrace_append hprefix tailTrace_688583
  have hstable : (prefixWord ++ tailWord_688583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688583).length < 2 ^ (prefixWord ++ tailWord_688583).sum := by decide
  have hdescent : baseEnd_688583 < baseStart_688583 := by decide
  rcases family_descends (prefixWord ++ tailWord_688583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688607 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 3]
def baseStart_688607 : Nat := 118140960795 + 688607 * 2 ^ 59
def prefixEnd_688607 : Nat := 4983230072969 + 3 ^ 40 * 688607 * 2
def baseEnd_688607 : Nat := 314298998267282271685031

theorem tailTrace_688607 : CollatzResearch.WordTrace tailWord_688607 prefixEnd_688607 314298998267282271685031 := by
  unfold tailWord_688607
  simp only [CollatzResearch.WordTrace]
  refine ⟨25115560616301918557720075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16743707077534612371813383 25115560616301918557720075)
  ·
    refine ⟨37673340924452877836580113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25115560616301918557720075 37673340924452877836580113)
    ·
      refine ⟨28255005693339658377435085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37673340924452877836580113 28255005693339658377435085)
      ·
        refine ⟨10595627135002371891538157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28255005693339658377435085 10595627135002371891538157)
        ·
          refine ⟨3973360175625889459326809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10595627135002371891538157 3973360175625889459326809)
          ·
            refine ⟨2980020131719417094495107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3973360175625889459326809 2980020131719417094495107)
            ·
              refine ⟨4470030197579125641742661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980020131719417094495107 4470030197579125641742661)
              ·
                refine ⟨838130662046086057826749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4470030197579125641742661 838130662046086057826749)
                ·
                  refine ⟨314298998267282271685031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838130662046086057826749 314298998267282271685031)
                  ·
                    rfl

theorem cell20_688607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_688607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688607 prefixEnd_688607 := by exact prefixLift 688607
  have htrace : WordTrace (prefixWord ++ tailWord_688607) baseStart_688607 baseEnd_688607 := by
    simpa [prefixWord, tailWord_688607, baseEnd_688607] using wordTrace_append hprefix tailTrace_688607
  have hstable : (prefixWord ++ tailWord_688607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688607).length < 2 ^ (prefixWord ++ tailWord_688607).sum := by decide
  have hdescent : baseEnd_688607 < baseStart_688607 := by decide
  rcases family_descends (prefixWord ++ tailWord_688607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688669 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_688669 : Nat := 118140960795 + 688669 * 2 ^ 59
def prefixEnd_688669 : Nat := 4983230072969 + 3 ^ 40 * 688669 * 2
def baseEnd_688669 : Nat := 314327296756685611618111

theorem tailTrace_688669 : CollatzResearch.WordTrace tailWord_688669 prefixEnd_688669 314327296756685611618111 := by
  unfold tailWord_688669
  simp only [CollatzResearch.WordTrace]
  refine ⟨25117821942077303146477061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16745214628051535430984707 25117821942077303146477061)
  ·
    refine ⟨4709591614139494339964449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25117821942077303146477061 4709591614139494339964449)
    ·
      refine ⟨3532193710604620754973337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4709591614139494339964449 3532193710604620754973337)
      ·
        refine ⟨2649145282953465566230003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3532193710604620754973337 2649145282953465566230003)
        ·
          refine ⟨3973717924430198349345005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649145282953465566230003 3973717924430198349345005)
          ·
            refine ⟨1490144221661324381004377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3973717924430198349345005 1490144221661324381004377)
            ·
              refine ⟨1117608166245993285753283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490144221661324381004377 1117608166245993285753283)
              ·
                refine ⟨1676412249368989928629925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117608166245993285753283 1676412249368989928629925)
                ·
                  refine ⟨314327296756685611618111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676412249368989928629925 314327296756685611618111)
                  ·
                    rfl

theorem cell20_688669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_688669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688669 prefixEnd_688669 := by exact prefixLift 688669
  have htrace : WordTrace (prefixWord ++ tailWord_688669) baseStart_688669 baseEnd_688669 := by
    simpa [prefixWord, tailWord_688669, baseEnd_688669] using wordTrace_append hprefix tailTrace_688669
  have hstable : (prefixWord ++ tailWord_688669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688669).length < 2 ^ (prefixWord ++ tailWord_688669).sum := by decide
  have hdescent : baseEnd_688669 < baseStart_688669 := by decide
  rcases family_descends (prefixWord ++ tailWord_688669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688690 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_688690 : Nat := 118140960795 + 688690 * 2 ^ 59
def prefixEnd_688690 : Nat := 4983230072969 + 3 ^ 40 * 688690 * 2
def baseEnd_688690 : Nat := 314336881728902871918025

theorem tailTrace_688690 : CollatzResearch.WordTrace tailWord_688690 prefixEnd_688690 314336881728902871918025 := by
  unfold tailWord_688690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6279646968750305933247881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16745725250000815821994349 6279646968750305933247881)
  ·
    refine ⟨4709735226562729449935911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6279646968750305933247881 4709735226562729449935911)
    ·
      refine ⟨7064602839844094174903867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4709735226562729449935911 7064602839844094174903867)
      ·
        refine ⟨10596904259766141262355801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7064602839844094174903867 10596904259766141262355801)
        ·
          refine ⟨7947678194824605946766851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10596904259766141262355801 7947678194824605946766851)
          ·
            refine ⟨11921517292236908920150277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7947678194824605946766851 11921517292236908920150277)
            ·
              refine ⟨2235284492294420422528177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11921517292236908920150277 2235284492294420422528177)
              ·
                refine ⟨1676463369220815316896133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2235284492294420422528177 1676463369220815316896133)
                ·
                  refine ⟨314336881728902871918025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676463369220815316896133 314336881728902871918025)
                  ·
                    rfl

theorem cell20_688690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_688690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688690 prefixEnd_688690 := by exact prefixLift 688690
  have htrace : WordTrace (prefixWord ++ tailWord_688690) baseStart_688690 baseEnd_688690 := by
    simpa [prefixWord, tailWord_688690, baseEnd_688690] using wordTrace_append hprefix tailTrace_688690
  have hstable : (prefixWord ++ tailWord_688690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688690).length < 2 ^ (prefixWord ++ tailWord_688690).sum := by decide
  have hdescent : baseEnd_688690 < baseStart_688690 := by decide
  rcases family_descends (prefixWord ++ tailWord_688690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688697 : List Nat := [1, 2, 1, 5, 1, 1, 3, 6]
def baseStart_688697 : Nat := 118140960795 + 688697 * 2 ^ 59
def prefixEnd_688697 : Nat := 4983230072969 + 3 ^ 40 * 688697 * 2
def baseEnd_688697 : Nat := 104780025573213986228221

theorem tailTrace_688697 : CollatzResearch.WordTrace tailWord_688697 prefixEnd_688697 104780025573213986228221 := by
  unfold tailWord_688697
  simp only [CollatzResearch.WordTrace]
  refine ⟨25118843185975863928496345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16745895457317242618997563 25118843185975863928496345)
  ·
    refine ⟨18839132389481897946372259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25118843185975863928496345 18839132389481897946372259)
    ·
      refine ⟨28258698584222846919558389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18839132389481897946372259 28258698584222846919558389)
      ·
        refine ⟨2649252992270891898708599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28258698584222846919558389 2649252992270891898708599)
        ·
          refine ⟨3973879488406337848062899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649252992270891898708599 3973879488406337848062899)
          ·
            refine ⟨5960819232609506772094349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973879488406337848062899 5960819232609506772094349)
            ·
              refine ⟨2235307212228565039535381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5960819232609506772094349 2235307212228565039535381)
              ·
                refine ⟨104780025573213986228221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2235307212228565039535381 104780025573213986228221)
                ·
                  rfl

theorem cell20_688697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_688697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688697 prefixEnd_688697 := by exact prefixLift 688697
  have htrace : WordTrace (prefixWord ++ tailWord_688697) baseStart_688697 baseEnd_688697 := by
    simpa [prefixWord, tailWord_688697, baseEnd_688697] using wordTrace_append hprefix tailTrace_688697
  have hstable : (prefixWord ++ tailWord_688697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688697).length < 2 ^ (prefixWord ++ tailWord_688697).sum := by decide
  have hdescent : baseEnd_688697 < baseStart_688697 := by decide
  rcases family_descends (prefixWord ++ tailWord_688697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688704 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_688704 : Nat := 118140960795 + 688704 * 2 ^ 59
def prefixEnd_688704 : Nat := 4983230072969 + 3 ^ 40 * 688704 * 2
def baseEnd_688704 : Nat := 314343271710381045451301

theorem tailTrace_688704 : CollatzResearch.WordTrace tailWord_688704 prefixEnd_688704 314343271710381045451301 := by
  unfold tailWord_688704
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559549248475252062000583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16746065664633669416000777 12559549248475252062000583)
  ·
    refine ⟨18839323872712878093000875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12559549248475252062000583 18839323872712878093000875)
    ·
      refine ⟨28258985809069317139501313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18839323872712878093000875 28258985809069317139501313)
      ·
        refine ⟨21194239356801987854625985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28258985809069317139501313 21194239356801987854625985)
        ·
          refine ⟨15895679517601490890969489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21194239356801987854625985 15895679517601490890969489)
          ·
            refine ⟨11921759638201118168227117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15895679517601490890969489 11921759638201118168227117)
            ·
              refine ⟨4470659864325419313085169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11921759638201118168227117 4470659864325419313085169)
              ·
                refine ⟨3352994898244064484813877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470659864325419313085169 3352994898244064484813877)
                ·
                  refine ⟨314343271710381045451301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3352994898244064484813877 314343271710381045451301)
                  ·
                    rfl

theorem cell20_688704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_688704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688704 prefixEnd_688704 := by exact prefixLift 688704
  have htrace : WordTrace (prefixWord ++ tailWord_688704) baseStart_688704 baseEnd_688704 := by
    simpa [prefixWord, tailWord_688704, baseEnd_688704] using wordTrace_append hprefix tailTrace_688704
  have hstable : (prefixWord ++ tailWord_688704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688704).length < 2 ^ (prefixWord ++ tailWord_688704).sum := by decide
  have hdescent : baseEnd_688704 < baseStart_688704 := by decide
  rcases family_descends (prefixWord ++ tailWord_688704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688728 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_688728 : Nat := 118140960795 + 688728 * 2 ^ 59
def prefixEnd_688728 : Nat := 4983230072969 + 3 ^ 40 * 688728 * 2
def baseEnd_688728 : Nat := 314354225964343628651203

theorem tailTrace_688728 : CollatzResearch.WordTrace tailWord_688728 prefixEnd_688728 314354225964343628651203 := by
  unfold tailWord_688728
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559986924431778111437419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16746649232575704148583225 12559986924431778111437419)
  ·
    refine ⟨18839980386647667167156129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12559986924431778111437419 18839980386647667167156129)
    ·
      refine ⟨14129985289985750375367097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18839980386647667167156129 14129985289985750375367097)
      ·
        refine ⟨10597488967489312781525323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14129985289985750375367097 10597488967489312781525323)
        ·
          refine ⟨15896233451233969172287985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10597488967489312781525323 15896233451233969172287985)
          ·
            refine ⟨11922175088425476879215989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15896233451233969172287985 11922175088425476879215989)
            ·
              refine ⟨1117703914539888457426499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11922175088425476879215989 1117703914539888457426499)
              ·
                refine ⟨1676555871809832686139749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117703914539888457426499 1676555871809832686139749)
                ·
                  refine ⟨314354225964343628651203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676555871809832686139749 314354225964343628651203)
                  ·
                    rfl

theorem cell20_688728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_688728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688728 prefixEnd_688728 := by exact prefixLift 688728
  have htrace : WordTrace (prefixWord ++ tailWord_688728) baseStart_688728 baseEnd_688728 := by
    simpa [prefixWord, tailWord_688728, baseEnd_688728] using wordTrace_append hprefix tailTrace_688728
  have hstable : (prefixWord ++ tailWord_688728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688728).length < 2 ^ (prefixWord ++ tailWord_688728).sum := by decide
  have hdescent : baseEnd_688728 < baseStart_688728 := by decide
  rcases family_descends (prefixWord ++ tailWord_688728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688797 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 3]
def baseStart_688797 : Nat := 118140960795 + 688797 * 2 ^ 59
def prefixEnd_688797 : Nat := 4983230072969 + 3 ^ 40 * 688797 * 2
def baseEnd_688797 : Nat := 314385719444486055350921

theorem tailTrace_688797 : CollatzResearch.WordTrace tailWord_688797 prefixEnd_688797 314385719444486055350921 := by
  unfold tailWord_688797
  simp only [CollatzResearch.WordTrace]
  refine ⟨25122490485613581007136645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16748326990409054004757763 25122490485613581007136645)
  ·
    refine ⟨4710466966052546438838121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25122490485613581007136645 4710466966052546438838121)
    ·
      refine ⟨3532850224539409829128591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4710466966052546438838121 3532850224539409829128591)
      ·
        refine ⟨5299275336809114743692887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3532850224539409829128591 5299275336809114743692887)
        ·
          refine ⟨7948913005213672115539331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299275336809114743692887 7948913005213672115539331)
          ·
            refine ⟨11923369507820508173308997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7948913005213672115539331 11923369507820508173308997)
            ·
              refine ⟨2235631782716345282495437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11923369507820508173308997 2235631782716345282495437)
              ·
                refine ⟨838361918518629480935789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2235631782716345282495437 838361918518629480935789)
                ·
                  refine ⟨314385719444486055350921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838361918518629480935789 314385719444486055350921)
                  ·
                    rfl

theorem cell20_688797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_688797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688797 prefixEnd_688797 := by exact prefixLift 688797
  have htrace : WordTrace (prefixWord ++ tailWord_688797) baseStart_688797 baseEnd_688797 := by
    simpa [prefixWord, tailWord_688797, baseEnd_688797] using wordTrace_append hprefix tailTrace_688797
  have hstable : (prefixWord ++ tailWord_688797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688797).length < 2 ^ (prefixWord ++ tailWord_688797).sum := by decide
  have hdescent : baseEnd_688797 < baseStart_688797 := by decide
  rcases family_descends (prefixWord ++ tailWord_688797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688804 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_688804 : Nat := 118140960795 + 688804 * 2 ^ 59
def prefixEnd_688804 : Nat := 4983230072969 + 3 ^ 40 * 688804 * 2
def baseEnd_688804 : Nat := 314388914435225142117559

theorem tailTrace_688804 : CollatzResearch.WordTrace tailWord_688804 prefixEnd_688804 314388914435225142117559 := by
  unfold tailWord_688804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12561372898294110601320733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16748497197725480801760977 12561372898294110601320733)
  ·
    refine ⟨4710514836860291475495275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12561372898294110601320733 4710514836860291475495275)
    ·
      refine ⟨7065772255290437213242913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710514836860291475495275 7065772255290437213242913)
      ·
        refine ⟨5299329191467827909932185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7065772255290437213242913 5299329191467827909932185)
        ·
          refine ⟨3974496893600870932449139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5299329191467827909932185 3974496893600870932449139)
          ·
            refine ⟨5961745340401306398673709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974496893600870932449139 5961745340401306398673709)
            ·
              refine ⟨2235654502650489899502641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5961745340401306398673709 2235654502650489899502641)
              ·
                refine ⟨1676740876987867424626981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2235654502650489899502641 1676740876987867424626981)
                ·
                  refine ⟨314388914435225142117559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676740876987867424626981 314388914435225142117559)
                  ·
                    rfl

theorem cell20_688804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_688804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688804 prefixEnd_688804 := by exact prefixLift 688804
  have htrace : WordTrace (prefixWord ++ tailWord_688804) baseStart_688804 baseEnd_688804 := by
    simpa [prefixWord, tailWord_688804, baseEnd_688804] using wordTrace_append hprefix tailTrace_688804
  have hstable : (prefixWord ++ tailWord_688804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688804).length < 2 ^ (prefixWord ++ tailWord_688804).sum := by decide
  have hdescent : baseEnd_688804 < baseStart_688804 := by decide
  rcases family_descends (prefixWord ++ tailWord_688804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688817 : List Nat := [1, 2, 2, 6, 1, 1, 2, 3, 2]
def baseStart_688817 : Nat := 118140960795 + 688817 * 2 ^ 59
def prefixEnd_688817 : Nat := 4983230072969 + 3 ^ 40 * 688817 * 2
def baseEnd_688817 : Nat := 314394847989454874684173

theorem tailTrace_688817 : CollatzResearch.WordTrace tailWord_688817 prefixEnd_688817 314394847989454874684173 := by
  unfold tailWord_688817
  simp only [CollatzResearch.WordTrace]
  refine ⟨25123219945541124422864705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16748813297027416281909803 25123219945541124422864705)
  ·
    refine ⟨18842414959155843317148529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25123219945541124422864705 18842414959155843317148529)
    ·
      refine ⟨14131811219366882487861397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18842414959155843317148529 14131811219366882487861397)
      ·
        refine ⟨662428650907822616618503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14131811219366882487861397 662428650907822616618503)
        ·
          refine ⟨993642976361733924927755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662428650907822616618503 993642976361733924927755)
          ·
            refine ⟨1490464464542600887391633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993642976361733924927755 1490464464542600887391633)
            ·
              refine ⟨1117848348406950665543725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490464464542600887391633 1117848348406950665543725)
              ·
                refine ⟨419193130652606499578897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1117848348406950665543725 419193130652606499578897)
                ·
                  refine ⟨314394847989454874684173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419193130652606499578897 314394847989454874684173)
                  ·
                    rfl

theorem cell20_688817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_688817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688817 prefixEnd_688817 := by exact prefixLift 688817
  have htrace : WordTrace (prefixWord ++ tailWord_688817) baseStart_688817 baseEnd_688817 := by
    simpa [prefixWord, tailWord_688817, baseEnd_688817] using wordTrace_append hprefix tailTrace_688817
  have hstable : (prefixWord ++ tailWord_688817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688817).length < 2 ^ (prefixWord ++ tailWord_688817).sum := by decide
  have hdescent : baseEnd_688817 < baseStart_688817 := by decide
  rcases family_descends (prefixWord ++ tailWord_688817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688818 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_688818 : Nat := 118140960795 + 688818 * 2 ^ 59
def prefixEnd_688818 : Nat := 4983230072969 + 3 ^ 40 * 688818 * 2
def baseEnd_688818 : Nat := 314395304416703315650835

theorem tailTrace_688818 : CollatzResearch.WordTrace tailWord_688818 prefixEnd_688818 314395304416703315650835 := by
  unfold tailWord_688818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280814104634375398412777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16748837612358334395767405 6280814104634375398412777)
  ·
    refine ⟨4710610578475781548809583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6280814104634375398412777 4710610578475781548809583)
    ·
      refine ⟨7065915867713672323214375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710610578475781548809583 7065915867713672323214375)
      ·
        refine ⟨10598873801570508484821563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7065915867713672323214375 10598873801570508484821563)
        ·
          refine ⟨15898310702355762727232345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10598873801570508484821563 15898310702355762727232345)
          ·
            refine ⟨11923733026766822045424259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15898310702355762727232345 11923733026766822045424259)
            ·
              refine ⟨17885599540150233068136389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11923733026766822045424259 17885599540150233068136389)
              ·
                refine ⟨3353549913778168700275573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17885599540150233068136389 3353549913778168700275573)
                ·
                  refine ⟨314395304416703315650835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3353549913778168700275573 314395304416703315650835)
                  ·
                    rfl

theorem cell20_688818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_688818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688818 prefixEnd_688818 := by exact prefixLift 688818
  have htrace : WordTrace (prefixWord ++ tailWord_688818) baseStart_688818 baseEnd_688818 := by
    simpa [prefixWord, tailWord_688818, baseEnd_688818] using wordTrace_append hprefix tailTrace_688818
  have hstable : (prefixWord ++ tailWord_688818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688818).length < 2 ^ (prefixWord ++ tailWord_688818).sum := by decide
  have hdescent : baseEnd_688818 < baseStart_688818 := by decide
  rcases family_descends (prefixWord ++ tailWord_688818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688825 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_688825 : Nat := 118140960795 + 688825 * 2 ^ 59
def prefixEnd_688825 : Nat := 4983230072969 + 3 ^ 40 * 688825 * 2
def baseEnd_688825 : Nat := 314398499407442402417473

theorem tailTrace_688825 : CollatzResearch.WordTrace tailWord_688825 prefixEnd_688825 314398499407442402417473 := by
  unfold tailWord_688825
  simp only [CollatzResearch.WordTrace]
  refine ⟨25123511729512141789155929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16749007819674761192770619 25123511729512141789155929)
  ·
    refine ⟨18842633797134106341866947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25123511729512141789155929 18842633797134106341866947)
    ·
      refine ⟨28263950695701159512800421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18842633797134106341866947 28263950695701159512800421)
      ·
        refine ⟨5299490755443967408650079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28263950695701159512800421 5299490755443967408650079)
        ·
          refine ⟨7949236133165951112975119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299490755443967408650079 7949236133165951112975119)
          ·
            refine ⟨11923854199748926669462679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7949236133165951112975119 11923854199748926669462679)
            ·
              refine ⟨17885781299623390004194019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11923854199748926669462679 17885781299623390004194019)
              ·
                refine ⟨26828671949435085006291029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17885781299623390004194019 26828671949435085006291029)
                ·
                  refine ⟨314398499407442402417473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26828671949435085006291029 314398499407442402417473)
                  ·
                    rfl

theorem cell20_688825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_688825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688825 prefixEnd_688825 := by exact prefixLift 688825
  have htrace : WordTrace (prefixWord ++ tailWord_688825) baseStart_688825 baseEnd_688825 := by
    simpa [prefixWord, tailWord_688825, baseEnd_688825] using wordTrace_append hprefix tailTrace_688825
  have hstable : (prefixWord ++ tailWord_688825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688825).length < 2 ^ (prefixWord ++ tailWord_688825).sum := by decide
  have hdescent : baseEnd_688825 < baseStart_688825 := by decide
  rcases family_descends (prefixWord ++ tailWord_688825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688842 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_688842 : Nat := 118140960795 + 688842 * 2 ^ 59
def prefixEnd_688842 : Nat := 4983230072969 + 3 ^ 40 * 688842 * 2
def baseEnd_688842 : Nat := 314406258670665898850737

theorem tailTrace_688842 : CollatzResearch.WordTrace tailWord_688842 prefixEnd_688842 314406258670665898850737 := by
  unfold tailWord_688842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281032942612638423131195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16749421180300369128349853 6281032942612638423131195)
  ·
    refine ⟨9421549413918957634696793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6281032942612638423131195 9421549413918957634696793)
    ·
      refine ⟨7066162060439218226022595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9421549413918957634696793 7066162060439218226022595)
      ·
        refine ⟨10599243090658827339033893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7066162060439218226022595 10599243090658827339033893)
        ·
          refine ⟨1987358079498530126068855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10599243090658827339033893 1987358079498530126068855)
          ·
            refine ⟨2981037119247795189103283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987358079498530126068855 2981037119247795189103283)
            ·
              refine ⟨4471555678871692783654925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981037119247795189103283 4471555678871692783654925)
              ·
                refine ⟨1676833379576884793870597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4471555678871692783654925 1676833379576884793870597)
                ·
                  refine ⟨314406258670665898850737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676833379576884793870597 314406258670665898850737)
                  ·
                    rfl

theorem cell20_688842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_688842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688842 prefixEnd_688842 := by exact prefixLift 688842
  have htrace : WordTrace (prefixWord ++ tailWord_688842) baseStart_688842 baseEnd_688842 := by
    simpa [prefixWord, tailWord_688842, baseEnd_688842] using wordTrace_append hprefix tailTrace_688842
  have hstable : (prefixWord ++ tailWord_688842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688842).length < 2 ^ (prefixWord ++ tailWord_688842).sum := by decide
  have hdescent : baseEnd_688842 < baseStart_688842 := by decide
  rcases family_descends (prefixWord ++ tailWord_688842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688948 : List Nat := [2, 5, 1, 1, 3, 2, 2, 2, 2]
def baseStart_688948 : Nat := 118140960795 + 688948 * 2 ^ 59
def prefixEnd_688948 : Nat := 4983230072969 + 3 ^ 40 * 688948 * 2
def baseEnd_688948 : Nat := 314454639959000641316971

theorem tailTrace_688948 : CollatzResearch.WordTrace tailWord_688948 prefixEnd_688948 314454639959000641316971 := by
  unfold tailWord_688948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12563998954033266897941749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16751998605377689197255665 12563998954033266897941749)
  ·
    refine ⟨1177874901940618771682039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12563998954033266897941749 1177874901940618771682039)
    ·
      refine ⟨1766812352910928157523059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177874901940618771682039 1766812352910928157523059)
      ·
        refine ⟨2650218529366392236284589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766812352910928157523059 2650218529366392236284589)
        ·
          refine ⟨993831948512397088606721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2650218529366392236284589 993831948512397088606721)
          ·
            refine ⟨745373961384297816455041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 993831948512397088606721 745373961384297816455041)
            ·
              refine ⟨559030471038223362341281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745373961384297816455041 559030471038223362341281)
              ·
                refine ⟨419272853278667521755961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559030471038223362341281 419272853278667521755961)
                ·
                  refine ⟨314454639959000641316971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419272853278667521755961 314454639959000641316971)
                  ·
                    rfl

theorem cell20_688948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_688948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688948 prefixEnd_688948 := by exact prefixLift 688948
  have htrace : WordTrace (prefixWord ++ tailWord_688948) baseStart_688948 baseEnd_688948 := by
    simpa [prefixWord, tailWord_688948, baseEnd_688948] using wordTrace_append hprefix tailTrace_688948
  have hstable : (prefixWord ++ tailWord_688948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688948).length < 2 ^ (prefixWord ++ tailWord_688948).sum := by decide
  have hdescent : baseEnd_688948 < baseStart_688948 := by decide
  rcases family_descends (prefixWord ++ tailWord_688948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688949 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 3]
def baseStart_688949 : Nat := 118140960795 + 688949 * 2 ^ 59
def prefixEnd_688949 : Nat := 4983230072969 + 3 ^ 40 * 688949 * 2
def baseEnd_688949 : Nat := 314455096386249082283633

theorem tailTrace_688949 : CollatzResearch.WordTrace tailWord_688949 prefixEnd_688949 314455096386249082283633 := by
  unfold tailWord_688949
  simp only [CollatzResearch.WordTrace]
  refine ⟨25128034381062910966669901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16752022920708607311113267 25128034381062910966669901)
  ·
    refine ⟨9423012892898591612501213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25128034381062910966669901 9423012892898591612501213)
    ·
      refine ⟨3533629834836971854687955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9423012892898591612501213 3533629834836971854687955)
      ·
        refine ⟨5300444752255457782031933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533629834836971854687955 5300444752255457782031933)
        ·
          refine ⟨1987666782095796668261975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5300444752255457782031933 1987666782095796668261975)
          ·
            refine ⟨2981500173143695002392963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987666782095796668261975 2981500173143695002392963)
            ·
              refine ⟨4472250259715542503589445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981500173143695002392963 4472250259715542503589445)
              ·
                refine ⟨838546923696664219423021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4472250259715542503589445 838546923696664219423021)
                ·
                  refine ⟨314455096386249082283633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838546923696664219423021 314455096386249082283633)
                  ·
                    rfl

theorem cell20_688949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_688949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688949 prefixEnd_688949 := by exact prefixLift 688949
  have htrace : WordTrace (prefixWord ++ tailWord_688949) baseStart_688949 baseEnd_688949 := by
    simpa [prefixWord, tailWord_688949, baseEnd_688949] using wordTrace_append hprefix tailTrace_688949
  have hstable : (prefixWord ++ tailWord_688949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688949).length < 2 ^ (prefixWord ++ tailWord_688949).sum := by decide
  have hdescent : baseEnd_688949 < baseStart_688949 := by decide
  rcases family_descends (prefixWord ++ tailWord_688949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688984 : List Nat := [2, 1, 2, 2, 1, 1, 1, 10]
def baseStart_688984 : Nat := 118140960795 + 688984 * 2 ^ 59
def prefixEnd_688984 : Nat := 4983230072969 + 3 ^ 40 * 688984 * 2
def baseEnd_688984 : Nat := 104823690446648172038941

theorem tailTrace_688984 : CollatzResearch.WordTrace tailWord_688984 prefixEnd_688984 104823690446648172038941 := by
  unfold tailWord_688984
  simp only [CollatzResearch.WordTrace]
  refine ⟨12564655467968055972097003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16752873957290741296129337 12564655467968055972097003)
  ·
    refine ⟨18846983201952083958145505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12564655467968055972097003 18846983201952083958145505)
    ·
      refine ⟨14135237401464062968609129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18846983201952083958145505 14135237401464062968609129)
      ·
        refine ⟨10601428051098047226456847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14135237401464062968609129 10601428051098047226456847)
        ·
          refine ⟨15902142076647070839685271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10601428051098047226456847 15902142076647070839685271)
          ·
            refine ⟨23853213114970606259527907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15902142076647070839685271 23853213114970606259527907)
            ·
              refine ⟨35779819672455909389291861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23853213114970606259527907 35779819672455909389291861)
              ·
                refine ⟨104823690446648172038941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35779819672455909389291861 104823690446648172038941)
                ·
                  rfl

theorem cell20_688984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_688984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_688984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_688984 prefixEnd_688984 := by exact prefixLift 688984
  have htrace : WordTrace (prefixWord ++ tailWord_688984) baseStart_688984 baseEnd_688984 := by
    simpa [prefixWord, tailWord_688984, baseEnd_688984] using wordTrace_append hprefix tailTrace_688984
  have hstable : (prefixWord ++ tailWord_688984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688984).length < 2 ^ (prefixWord ++ tailWord_688984).sum := by decide
  have hdescent : baseEnd_688984 < baseStart_688984 := by decide
  rcases family_descends (prefixWord ++ tailWord_688984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689032 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_689032 : Nat := 118140960795 + 689032 * 2 ^ 59
def prefixEnd_689032 : Nat := 4983230072969 + 3 ^ 40 * 689032 * 2
def baseEnd_689032 : Nat := 314492979847869682516627

theorem tailTrace_689032 : CollatzResearch.WordTrace tailWord_689032 prefixEnd_689032 314492979847869682516627 := by
  unfold tailWord_689032
  simp only [CollatzResearch.WordTrace]
  refine ⟨12565530819881108070970675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16754041093174810761294233 12565530819881108070970675)
  ·
    refine ⟨18848296229821662106456013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12565530819881108070970675 18848296229821662106456013)
    ·
      refine ⟨7068111086183123289921005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18848296229821662106456013 7068111086183123289921005)
      ·
        refine ⟨2650541657318671233720377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7068111086183123289921005 2650541657318671233720377)
        ·
          refine ⟨1987906242989003425290283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2650541657318671233720377 1987906242989003425290283)
          ·
            refine ⟨2981859364483505137935425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987906242989003425290283 2981859364483505137935425)
            ·
              refine ⟨2236394523362628853451569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981859364483505137935425 2236394523362628853451569)
              ·
                refine ⟨1677295892521971640088677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236394523362628853451569 1677295892521971640088677)
                ·
                  refine ⟨314492979847869682516627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677295892521971640088677 314492979847869682516627)
                  ·
                    rfl

theorem cell20_689032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_689032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689032 prefixEnd_689032 := by exact prefixLift 689032
  have htrace : WordTrace (prefixWord ++ tailWord_689032) baseStart_689032 baseEnd_689032 := by
    simpa [prefixWord, tailWord_689032, baseEnd_689032] using wordTrace_append hprefix tailTrace_689032
  have hstable : (prefixWord ++ tailWord_689032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689032).length < 2 ^ (prefixWord ++ tailWord_689032).sum := by decide
  have hdescent : baseEnd_689032 < baseStart_689032 := by decide
  rcases family_descends (prefixWord ++ tailWord_689032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689076 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_689076 : Nat := 118140960795 + 689076 * 2 ^ 59
def prefixEnd_689076 : Nat := 4983230072969 + 3 ^ 40 * 689076 * 2
def baseEnd_689076 : Nat := 314513062646801085049781

theorem tailTrace_689076 : CollatzResearch.WordTrace tailWord_689076 prefixEnd_689076 314513062646801085049781 := by
  unfold tailWord_689076
  simp only [CollatzResearch.WordTrace]
  refine ⟨12566333225801405828271541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16755110967735207771028721 12566333225801405828271541)
  ·
    refine ⟨1178093739918881796400457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12566333225801405828271541 1178093739918881796400457)
    ·
      refine ⟨883570304939161347300343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1178093739918881796400457 883570304939161347300343)
      ·
        refine ⟨1325355457408742020950515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883570304939161347300343 1325355457408742020950515)
        ·
          refine ⟨1988033186113113031425773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325355457408742020950515 1988033186113113031425773)
          ·
            refine ⟨745512444792417386784665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1988033186113113031425773 745512444792417386784665)
            ·
              refine ⟨559134333594313040088499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745512444792417386784665 559134333594313040088499)
              ·
                refine ⟨838701500391469560132749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559134333594313040088499 838701500391469560132749)
                ·
                  refine ⟨314513062646801085049781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838701500391469560132749 314513062646801085049781)
                  ·
                    rfl

theorem cell20_689076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_689076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689076 prefixEnd_689076 := by exact prefixLift 689076
  have htrace : WordTrace (prefixWord ++ tailWord_689076) baseStart_689076 baseEnd_689076 := by
    simpa [prefixWord, tailWord_689076, baseEnd_689076] using wordTrace_append hprefix tailTrace_689076
  have hstable : (prefixWord ++ tailWord_689076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689076).length < 2 ^ (prefixWord ++ tailWord_689076).sum := by decide
  have hdescent : baseEnd_689076 < baseStart_689076 := by decide
  rcases family_descends (prefixWord ++ tailWord_689076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689077 : List Nat := [1, 3, 3, 2, 1, 1, 4, 5]
def baseStart_689077 : Nat := 118140960795 + 689077 * 2 ^ 59
def prefixEnd_689077 : Nat := 4983230072969 + 3 ^ 40 * 689077 * 2
def baseEnd_689077 : Nat := 104837839691349842005481

theorem tailTrace_689077 : CollatzResearch.WordTrace tailWord_689077 prefixEnd_689077 104837839691349842005481 := by
  unfold tailWord_689077
  simp only [CollatzResearch.WordTrace]
  refine ⟨25132702924599188827329485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16755135283066125884886323 25132702924599188827329485)
  ·
    refine ⟨9424763596724695810248557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25132702924599188827329485 9424763596724695810248557)
    ·
      refine ⟨3534286348771760928843209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9424763596724695810248557 3534286348771760928843209)
      ·
        refine ⟨2650714761578820696632407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3534286348771760928843209 2650714761578820696632407)
        ·
          refine ⟨3976072142368231044948611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650714761578820696632407 3976072142368231044948611)
          ·
            refine ⟨5964108213552346567422917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3976072142368231044948611 5964108213552346567422917)
            ·
              refine ⟨1118270290041064981391797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5964108213552346567422917 1118270290041064981391797)
              ·
                refine ⟨104837839691349842005481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1118270290041064981391797 104837839691349842005481)
                ·
                  rfl

theorem cell20_689077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_689077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689077 prefixEnd_689077 := by exact prefixLift 689077
  have htrace : WordTrace (prefixWord ++ tailWord_689077) baseStart_689077 baseEnd_689077 := by
    simpa [prefixWord, tailWord_689077, baseEnd_689077] using wordTrace_append hprefix tailTrace_689077
  have hstable : (prefixWord ++ tailWord_689077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689077).length < 2 ^ (prefixWord ++ tailWord_689077).sum := by decide
  have hdescent : baseEnd_689077 < baseStart_689077 := by decide
  rcases family_descends (prefixWord ++ tailWord_689077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689080 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_689080 : Nat := 118140960795 + 689080 * 2 ^ 59
def prefixEnd_689080 : Nat := 4983230072969 + 3 ^ 40 * 689080 * 2
def baseEnd_689080 : Nat := 314514888355794848916431

theorem tailTrace_689080 : CollatzResearch.WordTrace tailWord_689080 prefixEnd_689080 314514888355794848916431 := by
  unfold tailWord_689080
  simp only [CollatzResearch.WordTrace]
  refine ⟨12566406171794160169844347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16755208229058880226459129 12566406171794160169844347)
  ·
    refine ⟨18849609257691240254766521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12566406171794160169844347 18849609257691240254766521)
    ·
      refine ⟨14137206943268430191074891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18849609257691240254766521 14137206943268430191074891)
      ·
        refine ⟨21205810414902645286612337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14137206943268430191074891 21205810414902645286612337)
        ·
          refine ⟨15904357811176983964959253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21205810414902645286612337 15904357811176983964959253)
          ·
            refine ⟨745516772398921123357465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15904357811176983964959253 745516772398921123357465)
            ·
              refine ⟨559137579299190842518099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745516772398921123357465 559137579299190842518099)
              ·
                refine ⟨838706368948786263777149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559137579299190842518099 838706368948786263777149)
                ·
                  refine ⟨314514888355794848916431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838706368948786263777149 314514888355794848916431)
                  ·
                    rfl

theorem cell20_689080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_689080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689080 prefixEnd_689080 := by exact prefixLift 689080
  have htrace : WordTrace (prefixWord ++ tailWord_689080) baseStart_689080 baseEnd_689080 := by
    simpa [prefixWord, tailWord_689080, baseEnd_689080] using wordTrace_append hprefix tailTrace_689080
  have hstable : (prefixWord ++ tailWord_689080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689080).length < 2 ^ (prefixWord ++ tailWord_689080).sum := by decide
  have hdescent : baseEnd_689080 < baseStart_689080 := by decide
  rcases family_descends (prefixWord ++ tailWord_689080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689163 : List Nat := [1, 1, 1, 1, 6, 3, 2, 3, 2]
def baseStart_689163 : Nat := 118140960795 + 689163 * 2 ^ 59
def prefixEnd_689163 : Nat := 4983230072969 + 3 ^ 40 * 689163 * 2
def baseEnd_689163 : Nat := 314552771817415449149425

theorem tailTrace_689163 : CollatzResearch.WordTrace tailWord_689163 prefixEnd_689163 314552771817415449149425 := by
  unfold tailWord_689163
  simp only [CollatzResearch.WordTrace]
  refine ⟨25135839602287625514960143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16757226401525083676640095 25135839602287625514960143)
  ·
    refine ⟨37703759403431438272440215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25135839602287625514960143 37703759403431438272440215)
    ·
      refine ⟨56555639105147157408660323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37703759403431438272440215 56555639105147157408660323)
      ·
        refine ⟨84833458657720736112990485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56555639105147157408660323 84833458657720736112990485)
        ·
          refine ⟨3976568374580659505296429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84833458657720736112990485 3976568374580659505296429)
          ·
            refine ⟨1491213140467747314486161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3976568374580659505296429 1491213140467747314486161)
            ·
              refine ⟨1118409855350810485864621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491213140467747314486161 1118409855350810485864621)
              ·
                refine ⟨419403695756553932199233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1118409855350810485864621 419403695756553932199233)
                ·
                  refine ⟨314552771817415449149425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419403695756553932199233 314552771817415449149425)
                  ·
                    rfl

theorem cell20_689163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 2].length) (baseStart_689163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689163 prefixEnd_689163 := by exact prefixLift 689163
  have htrace : WordTrace (prefixWord ++ tailWord_689163) baseStart_689163 baseEnd_689163 := by
    simpa [prefixWord, tailWord_689163, baseEnd_689163] using wordTrace_append hprefix tailTrace_689163
  have hstable : (prefixWord ++ tailWord_689163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689163).length < 2 ^ (prefixWord ++ tailWord_689163).sum := by decide
  have hdescent : baseEnd_689163 < baseStart_689163 := by decide
  rcases family_descends (prefixWord ++ tailWord_689163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689208 : List Nat := [2, 1, 2, 1, 5, 3, 2, 4]
def baseStart_689208 : Nat := 118140960795 + 689208 * 2 ^ 59
def prefixEnd_689208 : Nat := 4983230072969 + 3 ^ 40 * 689208 * 2
def baseEnd_689208 : Nat := 104857770347865097549747

theorem tailTrace_689208 : CollatzResearch.WordTrace tailWord_689208 prefixEnd_689208 104857770347865097549747 := by
  unfold tailWord_689208
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568740443562299100174139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16758320591416398800232185 12568740443562299100174139)
  ·
    refine ⟨18853110665343448650261209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12568740443562299100174139 18853110665343448650261209)
    ·
      refine ⟨14139832999007586487695907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18853110665343448650261209 14139832999007586487695907)
      ·
        refine ⟨21209749498511379731543861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14139832999007586487695907 21209749498511379731543861)
        ·
          refine ⟨1988414015485441849832237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21209749498511379731543861 1988414015485441849832237)
          ·
            refine ⟨745655255807040693687089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1988414015485441849832237 745655255807040693687089)
            ·
              refine ⟨559241441855280520265317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745655255807040693687089 559241441855280520265317)
              ·
                refine ⟨104857770347865097549747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559241441855280520265317 104857770347865097549747)
                ·
                  rfl

theorem cell20_689208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_689208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689208 prefixEnd_689208 := by exact prefixLift 689208
  have htrace : WordTrace (prefixWord ++ tailWord_689208) baseStart_689208 baseEnd_689208 := by
    simpa [prefixWord, tailWord_689208, baseEnd_689208] using wordTrace_append hprefix tailTrace_689208
  have hstable : (prefixWord ++ tailWord_689208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689208).length < 2 ^ (prefixWord ++ tailWord_689208).sum := by decide
  have hdescent : baseEnd_689208 < baseStart_689208 := by decide
  rcases family_descends (prefixWord ++ tailWord_689208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689219 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_689219 : Nat := 118140960795 + 689219 * 2 ^ 59
def prefixEnd_689219 : Nat := 4983230072969 + 3 ^ 40 * 689219 * 2
def baseEnd_689219 : Nat := 314578331743328143282529

theorem tailTrace_689219 : CollatzResearch.WordTrace tailWord_689219 prefixEnd_689219 314578331743328143282529 := by
  unfold tailWord_689219
  simp only [CollatzResearch.WordTrace]
  refine ⟨25137882090084747078998711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16758588060056498052665807 25137882090084747078998711)
  ·
    refine ⟨37706823135127120618498067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25137882090084747078998711 37706823135127120618498067)
    ·
      refine ⟨56560234702690680927747101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37706823135127120618498067 56560234702690680927747101)
      ·
        refine ⟨21210088013509005347905163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56560234702690680927747101 21210088013509005347905163)
        ·
          refine ⟨31815132020263508021857745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21210088013509005347905163 31815132020263508021857745)
          ·
            refine ⟨23861349015197631016393309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31815132020263508021857745 23861349015197631016393309)
            ·
              refine ⟨8948005880699111631147491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23861349015197631016393309 8948005880699111631147491)
              ·
                refine ⟨13422008821048667446721237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8948005880699111631147491 13422008821048667446721237)
                ·
                  refine ⟨314578331743328143282529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13422008821048667446721237 314578331743328143282529)
                  ·
                    rfl

theorem cell20_689219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_689219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689219 prefixEnd_689219 := by exact prefixLift 689219
  have htrace : WordTrace (prefixWord ++ tailWord_689219) baseStart_689219 baseEnd_689219 := by
    simpa [prefixWord, tailWord_689219, baseEnd_689219] using wordTrace_append hprefix tailTrace_689219
  have hstable : (prefixWord ++ tailWord_689219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689219).length < 2 ^ (prefixWord ++ tailWord_689219).sum := by decide
  have hdescent : baseEnd_689219 < baseStart_689219 := by decide
  rcases family_descends (prefixWord ++ tailWord_689219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689229 : List Nat := [1, 6, 1, 1, 1, 2, 8]
def baseStart_689229 : Nat := 118140960795 + 689229 * 2 ^ 59
def prefixEnd_689229 : Nat := 4983230072969 + 3 ^ 40 * 689229 * 2
def baseEnd_689229 : Nat := 34953655112868061438795

theorem tailTrace_689229 : CollatzResearch.WordTrace tailWord_689229 prefixEnd_689229 34953655112868061438795 := by
  unfold tailWord_689229
  simp only [CollatzResearch.WordTrace]
  refine ⟨25138246820048518786862741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16758831213365679191241827 25138246820048518786862741)
  ·
    refine ⟨1178355319689774318134191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25138246820048518786862741 1178355319689774318134191)
    ·
      refine ⟨1767532979534661477201287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178355319689774318134191 1767532979534661477201287)
      ·
        refine ⟨2651299469301992215801931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767532979534661477201287 2651299469301992215801931)
        ·
          refine ⟨3976949203952988323702897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651299469301992215801931 3976949203952988323702897)
          ·
            refine ⟨2982711902964741242777173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3976949203952988323702897 2982711902964741242777173)
            ·
              refine ⟨34953655112868061438795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2982711902964741242777173 34953655112868061438795)
              ·
                rfl

theorem cell20_689229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_689229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689229 prefixEnd_689229 := by exact prefixLift 689229
  have htrace : WordTrace (prefixWord ++ tailWord_689229) baseStart_689229 baseEnd_689229 := by
    simpa [prefixWord, tailWord_689229, baseEnd_689229] using wordTrace_append hprefix tailTrace_689229
  have hstable : (prefixWord ++ tailWord_689229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689229).length < 2 ^ (prefixWord ++ tailWord_689229).sum := by decide
  have hdescent : baseEnd_689229 < baseStart_689229 := by decide
  rcases family_descends (prefixWord ++ tailWord_689229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689236 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_689236 : Nat := 118140960795 + 689236 * 2 ^ 59
def prefixEnd_689236 : Nat := 4983230072969 + 3 ^ 40 * 689236 * 2
def baseEnd_689236 : Nat := 314586091006551639715793

theorem tailTrace_689236 : CollatzResearch.WordTrace tailWord_689236 prefixEnd_689236 314586091006551639715793 := by
  unfold tailWord_689236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569251065511579491183781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16759001420682105988245041 12569251065511579491183781)
  ·
    refine ⟨2356734574783421154596959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12569251065511579491183781 2356734574783421154596959)
    ·
      refine ⟨3535101862175131731895439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356734574783421154596959 3535101862175131731895439)
      ·
        refine ⟨5302652793262697597843159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3535101862175131731895439 5302652793262697597843159)
        ·
          refine ⟨7953979189894046396764739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5302652793262697597843159 7953979189894046396764739)
          ·
            refine ⟨11930968784841069595147109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7953979189894046396764739 11930968784841069595147109)
            ·
              refine ⟨2237056647157700549090083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11930968784841069595147109 2237056647157700549090083)
              ·
                refine ⟨3355584970736550823635125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237056647157700549090083 3355584970736550823635125)
                ·
                  refine ⟨314586091006551639715793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355584970736550823635125 314586091006551639715793)
                  ·
                    rfl

theorem cell20_689236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_689236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689236 prefixEnd_689236 := by exact prefixLift 689236
  have htrace : WordTrace (prefixWord ++ tailWord_689236) baseStart_689236 baseEnd_689236 := by
    simpa [prefixWord, tailWord_689236, baseEnd_689236] using wordTrace_append hprefix tailTrace_689236
  have hstable : (prefixWord ++ tailWord_689236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689236).length < 2 ^ (prefixWord ++ tailWord_689236).sum := by decide
  have hdescent : baseEnd_689236 < baseStart_689236 := by decide
  rcases family_descends (prefixWord ++ tailWord_689236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689288 : List Nat := [2, 1, 3, 4, 10]
def baseStart_689288 : Nat := 118140960795 + 689288 * 2 ^ 59
def prefixEnd_689288 : Nat := 4983230072969 + 3 ^ 40 * 689288 * 2
def baseEnd_689288 : Nat := 3884071916339142839287

theorem tailTrace_689288 : CollatzResearch.WordTrace tailWord_689288 prefixEnd_689288 3884071916339142839287 := by
  unfold tailWord_689288
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570199363417385931630259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16760265817889847908840345 12570199363417385931630259)
  ·
    refine ⟨18855299045126078897445389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12570199363417385931630259 18855299045126078897445389)
    ·
      refine ⟨7070737141922279586542021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18855299045126078897445389 7070737141922279586542021)
      ·
        refine ⟨1325763214110427422476629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7070737141922279586542021 1325763214110427422476629)
        ·
          refine ⟨3884071916339142839287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1325763214110427422476629 3884071916339142839287)
          ·
            rfl

theorem cell20_689288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 10].length) (baseStart_689288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689288 prefixEnd_689288 := by exact prefixLift 689288
  have htrace : WordTrace (prefixWord ++ tailWord_689288) baseStart_689288 baseEnd_689288 := by
    simpa [prefixWord, tailWord_689288, baseEnd_689288] using wordTrace_append hprefix tailTrace_689288
  have hstable : (prefixWord ++ tailWord_689288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689288).length < 2 ^ (prefixWord ++ tailWord_689288).sum := by decide
  have hdescent : baseEnd_689288 < baseStart_689288 := by decide
  rcases family_descends (prefixWord ++ tailWord_689288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689294 : List Nat := [4, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_689294 : Nat := 118140960795 + 689294 * 2 ^ 59
def prefixEnd_689294 : Nat := 4983230072969 + 3 ^ 40 * 689294 * 2
def baseEnd_689294 : Nat := 314612563786961215782223

theorem tailTrace_689294 : CollatzResearch.WordTrace tailWord_689294 prefixEnd_689294 314612563786961215782223 := by
  unfold tailWord_689294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142577195601629360997367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16760411709875356591985957 3142577195601629360997367)
  ·
    refine ⟨4713865793402444041496051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3142577195601629360997367 4713865793402444041496051)
    ·
      refine ⟨7070798690103666062244077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4713865793402444041496051 7070798690103666062244077)
      ·
        refine ⟨2651549508788874773341529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7070798690103666062244077 2651549508788874773341529)
        ·
          refine ⟨1988662131591656080006147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2651549508788874773341529 1988662131591656080006147)
          ·
            refine ⟨2982993197387484120009221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988662131591656080006147 2982993197387484120009221)
            ·
              refine ⟨559311224510153272501729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2982993197387484120009221 559311224510153272501729)
              ·
                refine ⟨419483418382614954376297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559311224510153272501729 419483418382614954376297)
                ·
                  refine ⟨314612563786961215782223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419483418382614954376297 314612563786961215782223)
                  ·
                    rfl

theorem cell20_689294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_689294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689294 prefixEnd_689294 := by exact prefixLift 689294
  have htrace : WordTrace (prefixWord ++ tailWord_689294) baseStart_689294 baseEnd_689294 := by
    simpa [prefixWord, tailWord_689294, baseEnd_689294] using wordTrace_append hprefix tailTrace_689294
  have hstable : (prefixWord ++ tailWord_689294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689294).length < 2 ^ (prefixWord ++ tailWord_689294).sum := by decide
  have hdescent : baseEnd_689294 < baseStart_689294 := by decide
  rcases family_descends (prefixWord ++ tailWord_689294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689312 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_689312 : Nat := 118140960795 + 689312 * 2 ^ 59
def prefixEnd_689312 : Nat := 4983230072969 + 3 ^ 40 * 689312 * 2
def baseEnd_689312 : Nat := 314620779477433153182149

theorem tailTrace_689312 : CollatzResearch.WordTrace tailWord_689312 prefixEnd_689312 314620779477433153182149 := by
  unfold tailWord_689312
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570637039373911981067095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16760849385831882641422793 12570637039373911981067095)
  ·
    refine ⟨18855955559060867971600643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12570637039373911981067095 18855955559060867971600643)
    ·
      refine ⟨28283933338591301957400965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18855955559060867971600643 28283933338591301957400965)
      ·
        refine ⟨5303237500985869117012681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28283933338591301957400965 5303237500985869117012681)
        ·
          refine ⟨3977428125739401837759511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5303237500985869117012681 3977428125739401837759511)
          ·
            refine ⟨5966142188609102756639267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977428125739401837759511 5966142188609102756639267)
            ·
              refine ⟨8949213282913654134958901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5966142188609102756639267 8949213282913654134958901)
              ·
                refine ⟨838988745273155075152397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8949213282913654134958901 838988745273155075152397)
                ·
                  refine ⟨314620779477433153182149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 838988745273155075152397 314620779477433153182149)
                  ·
                    rfl

theorem cell20_689312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_689312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689312 prefixEnd_689312 := by exact prefixLift 689312
  have htrace : WordTrace (prefixWord ++ tailWord_689312) baseStart_689312 baseEnd_689312 := by
    simpa [prefixWord, tailWord_689312, baseEnd_689312] using wordTrace_append hprefix tailTrace_689312
  have hstable : (prefixWord ++ tailWord_689312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689312).length < 2 ^ (prefixWord ++ tailWord_689312).sum := by decide
  have hdescent : baseEnd_689312 < baseStart_689312 := by decide
  rcases family_descends (prefixWord ++ tailWord_689312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689381 : List Nat := [1, 3, 1, 4, 3, 1, 1, 6]
def baseStart_689381 : Nat := 118140960795 + 689381 * 2 ^ 59
def prefixEnd_689381 : Nat := 4983230072969 + 3 ^ 40 * 689381 * 2
def baseEnd_689381 : Nat := 104884090985858526627289

theorem tailTrace_689381 : CollatzResearch.WordTrace tailWord_689381 prefixEnd_689381 104884090985858526627289 := by
  unfold tailWord_689381
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143790715497848746395997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16762527143665232497597331 25143790715497848746395997)
  ·
    refine ⟨9428921518311693279898499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25143790715497848746395997 9428921518311693279898499)
    ·
      refine ⟨14143382277467539919847749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9428921518311693279898499 14143382277467539919847749)
      ·
        refine ⟨2651884177025163734971453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14143382277467539919847749 2651884177025163734971453)
        ·
          refine ⟨994456566384436400614295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2651884177025163734971453 994456566384436400614295)
          ·
            refine ⟨1491684849576654600921443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994456566384436400614295 1491684849576654600921443)
            ·
              refine ⟨2237527274364981901382165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491684849576654600921443 2237527274364981901382165)
              ·
                refine ⟨104884090985858526627289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2237527274364981901382165 104884090985858526627289)
                ·
                  rfl

theorem cell20_689381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_689381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689381 prefixEnd_689381 := by exact prefixLift 689381
  have htrace : WordTrace (prefixWord ++ tailWord_689381) baseStart_689381 baseEnd_689381 := by
    simpa [prefixWord, tailWord_689381, baseEnd_689381] using wordTrace_append hprefix tailTrace_689381
  have hstable : (prefixWord ++ tailWord_689381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689381).length < 2 ^ (prefixWord ++ tailWord_689381).sum := by decide
  have hdescent : baseEnd_689381 < baseStart_689381 := by decide
  rcases family_descends (prefixWord ++ tailWord_689381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689412 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_689412 : Nat := 118140960795 + 689412 * 2 ^ 59
def prefixEnd_689412 : Nat := 4983230072969 + 3 ^ 40 * 689412 * 2
def baseEnd_689412 : Nat := 314666422202277249848407

theorem tailTrace_689412 : CollatzResearch.WordTrace tailWord_689412 prefixEnd_689412 314666422202277249848407 := by
  unfold tailWord_689412
  simp only [CollatzResearch.WordTrace]
  refine ⟨12572460689192770520387245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16763280918923694027182993 12572460689192770520387245)
  ·
    refine ⟨4714672758447288945145217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12572460689192770520387245 4714672758447288945145217)
    ·
      refine ⟨3536004568835466708858913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4714672758447288945145217 3536004568835466708858913)
      ·
        refine ⟨2652003426626600031644185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3536004568835466708858913 2652003426626600031644185)
        ·
          refine ⟨1989002569969950023733139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2652003426626600031644185 1989002569969950023733139)
          ·
            refine ⟨2983503854954925035599709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989002569969950023733139 2983503854954925035599709)
            ·
              refine ⟨1118813945608096888349891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2983503854954925035599709 1118813945608096888349891)
              ·
                refine ⟨1678220918412145332524837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118813945608096888349891 1678220918412145332524837)
                ·
                  refine ⟨314666422202277249848407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678220918412145332524837 314666422202277249848407)
                  ·
                    rfl

theorem cell20_689412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_689412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689412 prefixEnd_689412 := by exact prefixLift 689412
  have htrace : WordTrace (prefixWord ++ tailWord_689412) baseStart_689412 baseEnd_689412 := by
    simpa [prefixWord, tailWord_689412, baseEnd_689412] using wordTrace_append hprefix tailTrace_689412
  have hstable : (prefixWord ++ tailWord_689412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689412).length < 2 ^ (prefixWord ++ tailWord_689412).sum := by decide
  have hdescent : baseEnd_689412 < baseStart_689412 := by decide
  rcases family_descends (prefixWord ++ tailWord_689412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689422 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_689422 : Nat := 118140960795 + 689422 * 2 ^ 59
def prefixEnd_689422 : Nat := 4983230072969 + 3 ^ 40 * 689422 * 2
def baseEnd_689422 : Nat := 314670986474761659515033

theorem tailTrace_689422 : CollatzResearch.WordTrace tailWord_689422 prefixEnd_689422 314670986474761659515033 := by
  unfold tailWord_689422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143160763543664093579815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16763524072232875165759013 3143160763543664093579815)
  ·
    refine ⟨4714741145315496140369723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3143160763543664093579815 4714741145315496140369723)
    ·
      refine ⟨7072111717973244210554585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4714741145315496140369723 7072111717973244210554585)
      ·
        refine ⟨5304083788479933157915939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7072111717973244210554585 5304083788479933157915939)
        ·
          refine ⟨7956125682719899736873909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304083788479933157915939 7956125682719899736873909)
          ·
            refine ⟨745886782754990600331929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7956125682719899736873909 745886782754990600331929)
            ·
              refine ⟨559415087066242950248947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745886782754990600331929 559415087066242950248947)
              ·
                refine ⟨839122630599364425373421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559415087066242950248947 839122630599364425373421)
                ·
                  refine ⟨314670986474761659515033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839122630599364425373421 314670986474761659515033)
                  ·
                    rfl

theorem cell20_689422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_689422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689422 prefixEnd_689422 := by exact prefixLift 689422
  have htrace : WordTrace (prefixWord ++ tailWord_689422) baseStart_689422 baseEnd_689422 := by
    simpa [prefixWord, tailWord_689422, baseEnd_689422] using wordTrace_append hprefix tailTrace_689422
  have hstable : (prefixWord ++ tailWord_689422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689422).length < 2 ^ (prefixWord ++ tailWord_689422).sum := by decide
  have hdescent : baseEnd_689422 < baseStart_689422 := by decide
  rcases family_descends (prefixWord ++ tailWord_689422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689495 : List Nat := [1, 1, 3, 2, 3, 3, 3, 4]
def baseStart_689495 : Nat := 118140960795 + 689495 * 2 ^ 59
def prefixEnd_689495 : Nat := 4983230072969 + 3 ^ 40 * 689495 * 2
def baseEnd_689495 : Nat := 104901435221299283360467

theorem tailTrace_689495 : CollatzResearch.WordTrace tailWord_689495 prefixEnd_689495 104901435221299283360467 := by
  unfold tailWord_689495
  simp only [CollatzResearch.WordTrace]
  refine ⟨25147948637084846216045939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765299091389897477363959 25147948637084846216045939)
  ·
    refine ⟨37721922955627269324068909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25147948637084846216045939 37721922955627269324068909)
    ·
      refine ⟨14145721108360225996525841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37721922955627269324068909 14145721108360225996525841)
      ·
        refine ⟨10609290831270169497394381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14145721108360225996525841 10609290831270169497394381)
        ·
          refine ⟨3978484061726313561522893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10609290831270169497394381 3978484061726313561522893)
          ·
            refine ⟨1491931523147367585571085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3978484061726313561522893 1491931523147367585571085)
            ·
              refine ⟨559474321180262844589157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1491931523147367585571085 559474321180262844589157)
              ·
                refine ⟨104901435221299283360467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559474321180262844589157 104901435221299283360467)
                ·
                  rfl

theorem cell20_689495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_689495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689495 prefixEnd_689495 := by exact prefixLift 689495
  have htrace : WordTrace (prefixWord ++ tailWord_689495) baseStart_689495 baseEnd_689495 := by
    simpa [prefixWord, tailWord_689495, baseEnd_689495] using wordTrace_append hprefix tailTrace_689495
  have hstable : (prefixWord ++ tailWord_689495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689495).length < 2 ^ (prefixWord ++ tailWord_689495).sum := by decide
  have hdescent : baseEnd_689495 < baseStart_689495 := by decide
  rcases family_descends (prefixWord ++ tailWord_689495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689516 : List Nat := [2, 2, 1, 1, 5, 2, 7]
def baseStart_689516 : Nat := 118140960795 + 689516 * 2 ^ 59
def prefixEnd_689516 : Nat := 4983230072969 + 3 ^ 40 * 689516 * 2
def baseEnd_689516 : Nat := 34968210070679456709035

theorem tailTrace_689516 : CollatzResearch.WordTrace tailWord_689516 prefixEnd_689516 34968210070679456709035 := by
  unfold tailWord_689516
  simp only [CollatzResearch.WordTrace]
  refine ⟨12574357285004383401280201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16765809713339177868373601 12574357285004383401280201)
  ·
    refine ⟨9430767963753287550960151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12574357285004383401280201 9430767963753287550960151)
    ·
      refine ⟨14146151945629931326440227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9430767963753287550960151 14146151945629931326440227)
      ·
        refine ⟨21219227918444896989660341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14146151945629931326440227 21219227918444896989660341)
        ·
          refine ⟨1989302617354209092780657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21219227918444896989660341 1989302617354209092780657)
          ·
            refine ⟨1491976963015656819585493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1989302617354209092780657 1491976963015656819585493)
            ·
              refine ⟨34968210070679456709035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1491976963015656819585493 34968210070679456709035)
              ·
                rfl

theorem cell20_689516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 7].length) (baseStart_689516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689516 prefixEnd_689516 := by exact prefixLift 689516
  have htrace : WordTrace (prefixWord ++ tailWord_689516) baseStart_689516 baseEnd_689516 := by
    simpa [prefixWord, tailWord_689516, baseEnd_689516] using wordTrace_append hprefix tailTrace_689516
  have hstable : (prefixWord ++ tailWord_689516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689516).length < 2 ^ (prefixWord ++ tailWord_689516).sum := by decide
  have hdescent : baseEnd_689516 < baseStart_689516 := by decide
  rcases family_descends (prefixWord ++ tailWord_689516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689530 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_689530 : Nat := 118140960795 + 689530 * 2 ^ 59
def prefixEnd_689530 : Nat := 4983230072969 + 3 ^ 40 * 689530 * 2
def baseEnd_689530 : Nat := 314720280617593283914591

theorem tailTrace_689530 : CollatzResearch.WordTrace tailWord_689530 prefixEnd_689530 314720280617593283914591 := by
  unfold tailWord_689530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287306297989511798392511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16766150127972031462380029 6287306297989511798392511)
  ·
    refine ⟨9430959446984267697588767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6287306297989511798392511 9430959446984267697588767)
    ·
      refine ⟨14146439170476401546383151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9430959446984267697588767 14146439170476401546383151)
      ·
        refine ⟨21219658755714602319574727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14146439170476401546383151 21219658755714602319574727)
        ·
          refine ⟨31829488133571903479362091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21219658755714602319574727 31829488133571903479362091)
          ·
            refine ⟨47744232200357855219043137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31829488133571903479362091 47744232200357855219043137)
            ·
              refine ⟨35808174150268391414282353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47744232200357855219043137 35808174150268391414282353)
              ·
                refine ⟨26856130612701293560711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35808174150268391414282353 26856130612701293560711765)
                ·
                  refine ⟨314720280617593283914591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26856130612701293560711765 314720280617593283914591)
                  ·
                    rfl

theorem cell20_689530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_689530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689530 prefixEnd_689530 := by exact prefixLift 689530
  have htrace : WordTrace (prefixWord ++ tailWord_689530) baseStart_689530 baseEnd_689530 := by
    simpa [prefixWord, tailWord_689530, baseEnd_689530] using wordTrace_append hprefix tailTrace_689530
  have hstable : (prefixWord ++ tailWord_689530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689530).length < 2 ^ (prefixWord ++ tailWord_689530).sum := by decide
  have hdescent : baseEnd_689530 < baseStart_689530 := by decide
  rcases family_descends (prefixWord ++ tailWord_689530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689560 : List Nat := [2, 1, 2, 5, 2, 2, 1, 3, 2]
def baseStart_689560 : Nat := 118140960795 + 689560 * 2 ^ 59
def prefixEnd_689560 : Nat := 4983230072969 + 3 ^ 40 * 689560 * 2
def baseEnd_689560 : Nat := 314733973435046512914469

theorem tailTrace_689560 : CollatzResearch.WordTrace tailWord_689560 prefixEnd_689560 314733973435046512914469 := by
  unfold tailWord_689560
  simp only [CollatzResearch.WordTrace]
  refine ⟨12575159690924681158581067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16766879587899574878108089 12575159690924681158581067)
  ·
    refine ⟨18862739536387021737871601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12575159690924681158581067 18862739536387021737871601)
    ·
      refine ⟨14147054652290266303403701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18862739536387021737871601 14147054652290266303403701)
      ·
        refine ⟨1326286373652212465944097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14147054652290266303403701 1326286373652212465944097)
        ·
          refine ⟨994714780239159349458073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326286373652212465944097 994714780239159349458073)
          ·
            refine ⟨746036085179369512093555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994714780239159349458073 746036085179369512093555)
            ·
              refine ⟨1119054127769054268140333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746036085179369512093555 1119054127769054268140333)
              ·
                refine ⟨419645297913395350552625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119054127769054268140333 419645297913395350552625)
                ·
                  refine ⟨314733973435046512914469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419645297913395350552625 314733973435046512914469)
                  ·
                    rfl

theorem cell20_689560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_689560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689560 prefixEnd_689560 := by exact prefixLift 689560
  have htrace : WordTrace (prefixWord ++ tailWord_689560) baseStart_689560 baseEnd_689560 := by
    simpa [prefixWord, tailWord_689560, baseEnd_689560] using wordTrace_append hprefix tailTrace_689560
  have hstable : (prefixWord ++ tailWord_689560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689560).length < 2 ^ (prefixWord ++ tailWord_689560).sum := by decide
  have hdescent : baseEnd_689560 < baseStart_689560 := by decide
  rcases family_descends (prefixWord ++ tailWord_689560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689561 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_689561 : Nat := 118140960795 + 689561 * 2 ^ 59
def prefixEnd_689561 : Nat := 4983230072969 + 3 ^ 40 * 689561 * 2
def baseEnd_689561 : Nat := 314734429862294953881131

theorem tailTrace_689561 : CollatzResearch.WordTrace tailWord_689561 prefixEnd_689561 314734429862294953881131 := by
  unfold tailWord_689561
  simp only [CollatzResearch.WordTrace]
  refine ⟨25150355854845739487948537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16766903903230492991965691 25150355854845739487948537)
  ·
    refine ⟨18862766891134304615961403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25150355854845739487948537 18862766891134304615961403)
    ·
      refine ⟨28294150336701456923942105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18862766891134304615961403 28294150336701456923942105)
      ·
        refine ⟨21220612752526092692956579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28294150336701456923942105 21220612752526092692956579)
        ·
          refine ⟨31830919128789139039434869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21220612752526092692956579 31830919128789139039434869)
          ·
            refine ⟨2984148668323981784947019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31830919128789139039434869 2984148668323981784947019)
            ·
              refine ⟨4476223002485972677420529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984148668323981784947019 4476223002485972677420529)
              ·
                refine ⟨3357167251864479508065397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4476223002485972677420529 3357167251864479508065397)
                ·
                  refine ⟨314734429862294953881131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3357167251864479508065397 314734429862294953881131)
                  ·
                    rfl

theorem cell20_689561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_689561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689561 prefixEnd_689561 := by exact prefixLift 689561
  have htrace : WordTrace (prefixWord ++ tailWord_689561) baseStart_689561 baseEnd_689561 := by
    simpa [prefixWord, tailWord_689561, baseEnd_689561] using wordTrace_append hprefix tailTrace_689561
  have hstable : (prefixWord ++ tailWord_689561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689561).length < 2 ^ (prefixWord ++ tailWord_689561).sum := by decide
  have hdescent : baseEnd_689561 < baseStart_689561 := by decide
  rcases family_descends (prefixWord ++ tailWord_689561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689581 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 4]
def baseStart_689581 : Nat := 118140960795 + 689581 * 2 ^ 59
def prefixEnd_689581 : Nat := 4983230072969 + 3 ^ 40 * 689581 * 2
def baseEnd_689581 : Nat := 314743558407263773214383

theorem tailTrace_689581 : CollatzResearch.WordTrace tailWord_689581 prefixEnd_689581 314743558407263773214383 := by
  unfold tailWord_689581
  simp only [CollatzResearch.WordTrace]
  refine ⟨25151085314773282903676597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16767390209848855269117731 25151085314773282903676597)
  ·
    refine ⟨2357914248259995272219681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25151085314773282903676597 2357914248259995272219681)
    ·
      refine ⟨1768435686194996454164761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2357914248259995272219681 1768435686194996454164761)
      ·
        refine ⟨1326326764646247340623571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1768435686194996454164761 1326326764646247340623571)
        ·
          refine ⟨1989490146969371010935357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326326764646247340623571 1989490146969371010935357)
          ·
            refine ⟨746058805113514129100759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1989490146969371010935357 746058805113514129100759)
            ·
              refine ⟨1119088207670271193651139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746058805113514129100759 1119088207670271193651139)
              ·
                refine ⟨1678632311505406790476709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119088207670271193651139 1678632311505406790476709)
                ·
                  refine ⟨314743558407263773214383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678632311505406790476709 314743558407263773214383)
                  ·
                    rfl

theorem cell20_689581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_689581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689581 prefixEnd_689581 := by exact prefixLift 689581
  have htrace : WordTrace (prefixWord ++ tailWord_689581) baseStart_689581 baseEnd_689581 := by
    simpa [prefixWord, tailWord_689581, baseEnd_689581] using wordTrace_append hprefix tailTrace_689581
  have hstable : (prefixWord ++ tailWord_689581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689581).length < 2 ^ (prefixWord ++ tailWord_689581).sum := by decide
  have hdescent : baseEnd_689581 < baseStart_689581 := by decide
  rcases family_descends (prefixWord ++ tailWord_689581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689640 : List Nat := [2, 1, 4, 1, 1, 2, 3, 4, 2]
def baseStart_689640 : Nat := 118140960795 + 689640 * 2 ^ 59
def prefixEnd_689640 : Nat := 4983230072969 + 3 ^ 40 * 689640 * 2
def baseEnd_689640 : Nat := 314770487614921790247475

theorem tailTrace_689640 : CollatzResearch.WordTrace tailWord_689640 prefixEnd_689640 314770487614921790247475 := by
  unfold tailWord_689640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12576618610779767990037187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16768824814373023986716249 12576618610779767990037187)
  ·
    refine ⟨18864927916169651985055781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12576618610779767990037187 18864927916169651985055781)
    ·
      refine ⟨3537173984281809747197959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18864927916169651985055781 3537173984281809747197959)
      ·
        refine ⟨5305760976422714620796939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537173984281809747197959 5305760976422714620796939)
        ·
          refine ⟨7958641464634071931195409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5305760976422714620796939 7958641464634071931195409)
          ·
            refine ⟨5968981098475553948396557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7958641464634071931195409 5968981098475553948396557)
            ·
              refine ⟨2238367911928332730648709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5968981098475553948396557 2238367911928332730648709)
              ·
                refine ⟨419693983486562386996633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2238367911928332730648709 419693983486562386996633)
                ·
                  refine ⟨314770487614921790247475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419693983486562386996633 314770487614921790247475)
                  ·
                    rfl

theorem cell20_689640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_689640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689640 prefixEnd_689640 := by exact prefixLift 689640
  have htrace : WordTrace (prefixWord ++ tailWord_689640) baseStart_689640 baseEnd_689640 := by
    simpa [prefixWord, tailWord_689640, baseEnd_689640] using wordTrace_append hprefix tailTrace_689640
  have hstable : (prefixWord ++ tailWord_689640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689640).length < 2 ^ (prefixWord ++ tailWord_689640).sum := by decide
  have hdescent : baseEnd_689640 < baseStart_689640 := by decide
  rcases family_descends (prefixWord ++ tailWord_689640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689651 : List Nat := [1, 1, 1, 2, 2, 2, 2, 9]
def baseStart_689651 : Nat := 118140960795 + 689651 * 2 ^ 59
def prefixEnd_689651 : Nat := 4983230072969 + 3 ^ 40 * 689651 * 2
def baseEnd_689651 : Nat := 104925169438218213626921

theorem tailTrace_689651 : CollatzResearch.WordTrace tailWord_689651 prefixEnd_689651 104925169438218213626921 := by
  unfold tailWord_689651
  simp only [CollatzResearch.WordTrace]
  refine ⟨25153638424519684858724807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16769092283013123239149871 25153638424519684858724807)
  ·
    refine ⟨37730457636779527288087211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25153638424519684858724807 37730457636779527288087211)
    ·
      refine ⟨56595686455169290932130817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37730457636779527288087211 56595686455169290932130817)
      ·
        refine ⟨42446764841376968199098113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56595686455169290932130817 42446764841376968199098113)
        ·
          refine ⟨31835073631032726149323585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42446764841376968199098113 31835073631032726149323585)
          ·
            refine ⟨23876305223274544611992689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31835073631032726149323585 23876305223274544611992689)
            ·
              refine ⟨17907228917455908458994517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23876305223274544611992689 17907228917455908458994517)
              ·
                refine ⟨104925169438218213626921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17907228917455908458994517 104925169438218213626921)
                ·
                  rfl

theorem cell20_689651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_689651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689651 prefixEnd_689651 := by exact prefixLift 689651
  have htrace : WordTrace (prefixWord ++ tailWord_689651) baseStart_689651 baseEnd_689651 := by
    simpa [prefixWord, tailWord_689651, baseEnd_689651] using wordTrace_append hprefix tailTrace_689651
  have hstable : (prefixWord ++ tailWord_689651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689651).length < 2 ^ (prefixWord ++ tailWord_689651).sum := by decide
  have hdescent : baseEnd_689651 < baseStart_689651 := by decide
  rcases family_descends (prefixWord ++ tailWord_689651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689661 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_689661 : Nat := 118140960795 + 689661 * 2 ^ 59
def prefixEnd_689661 : Nat := 4983230072969 + 3 ^ 40 * 689661 * 2
def baseEnd_689661 : Nat := 314780072587139050547389

theorem tailTrace_689661 : CollatzResearch.WordTrace tailWord_689661 prefixEnd_689661 314780072587139050547389 := by
  unfold tailWord_689661
  simp only [CollatzResearch.WordTrace]
  refine ⟨25154003154483456566588837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16769335436322304377725891 25154003154483456566588837)
  ·
    refine ⟨4716375591465648106235407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25154003154483456566588837 4716375591465648106235407)
    ·
      refine ⟨7074563387198472159353111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4716375591465648106235407 7074563387198472159353111)
      ·
        refine ⟨10611845080797708239029667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7074563387198472159353111 10611845080797708239029667)
        ·
          refine ⟨15917767621196562358544501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10611845080797708239029667 15917767621196562358544501)
          ·
            refine ⟨1492290714487177721113547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15917767621196562358544501 1492290714487177721113547)
            ·
              refine ⟨2238436071730766581670321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492290714487177721113547 2238436071730766581670321)
              ·
                refine ⟨1678827053798074936252741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238436071730766581670321 1678827053798074936252741)
                ·
                  refine ⟨314780072587139050547389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678827053798074936252741 314780072587139050547389)
                  ·
                    rfl

theorem cell20_689661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_689661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689661 prefixEnd_689661 := by exact prefixLift 689661
  have htrace : WordTrace (prefixWord ++ tailWord_689661) baseStart_689661 baseEnd_689661 := by
    simpa [prefixWord, tailWord_689661, baseEnd_689661] using wordTrace_append hprefix tailTrace_689661
  have hstable : (prefixWord ++ tailWord_689661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689661).length < 2 ^ (prefixWord ++ tailWord_689661).sum := by decide
  have hdescent : baseEnd_689661 < baseStart_689661 := by decide
  rcases family_descends (prefixWord ++ tailWord_689661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689670 : List Nat := [6, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_689670 : Nat := 118140960795 + 689670 * 2 ^ 59
def prefixEnd_689670 : Nat := 4983230072969 + 3 ^ 40 * 689670 * 2
def baseEnd_689670 : Nat := 314784180432375019247353

theorem tailTrace_689670 : CollatzResearch.WordTrace tailWord_689670 prefixEnd_689670 314784180432375019247353 := by
  unfold tailWord_689670
  simp only [CollatzResearch.WordTrace]
  refine ⟨786072856607839096989577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16769554274300567402444309 786072856607839096989577)
  ·
    refine ⟨589554642455879322742183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 786072856607839096989577 589554642455879322742183)
    ·
      refine ⟨884331963683818984113275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 589554642455879322742183 884331963683818984113275)
      ·
        refine ⟨1326497945525728476169913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884331963683818984113275 1326497945525728476169913)
        ·
          refine ⟨994873459144296357127435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326497945525728476169913 994873459144296357127435)
          ·
            refine ⟨1492310188716444535691153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994873459144296357127435 1492310188716444535691153)
            ·
              refine ⟨1119232641537333401768365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492310188716444535691153 1119232641537333401768365)
              ·
                refine ⟨419712240576500025663137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119232641537333401768365 419712240576500025663137)
                ·
                  refine ⟨314784180432375019247353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419712240576500025663137 314784180432375019247353)
                  ·
                    rfl

theorem cell20_689670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_689670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689670 prefixEnd_689670 := by exact prefixLift 689670
  have htrace : WordTrace (prefixWord ++ tailWord_689670) baseStart_689670 baseEnd_689670 := by
    simpa [prefixWord, tailWord_689670, baseEnd_689670] using wordTrace_append hprefix tailTrace_689670
  have hstable : (prefixWord ++ tailWord_689670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689670).length < 2 ^ (prefixWord ++ tailWord_689670).sum := by decide
  have hdescent : baseEnd_689670 < baseStart_689670 := by decide
  rcases family_descends (prefixWord ++ tailWord_689670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689688 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 3]
def baseStart_689688 : Nat := 118140960795 + 689688 * 2 ^ 59
def prefixEnd_689688 : Nat := 4983230072969 + 3 ^ 40 * 689688 * 2
def baseEnd_689688 : Nat := 314792396122846956647279

theorem tailTrace_689688 : CollatzResearch.WordTrace tailWord_689688 prefixEnd_689688 314792396122846956647279 := by
  unfold tailWord_689688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12577493962692820088910859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16769991950257093451881145 12577493962692820088910859)
  ·
    refine ⟨18866240944039230133366289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12577493962692820088910859 18866240944039230133366289)
    ·
      refine ⟨14149680708029422600024717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18866240944039230133366289 14149680708029422600024717)
      ·
        refine ⟨5306130265511033475009269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14149680708029422600024717 5306130265511033475009269)
        ·
          refine ⟨497449712391659388282119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5306130265511033475009269 497449712391659388282119)
          ·
            refine ⟨746174568587489082423179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497449712391659388282119 746174568587489082423179)
            ·
              refine ⟨1119261852881233623634769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746174568587489082423179 1119261852881233623634769)
              ·
                refine ⟨839446389660925217726077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119261852881233623634769 839446389660925217726077)
                ·
                  refine ⟨314792396122846956647279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839446389660925217726077 314792396122846956647279)
                  ·
                    rfl

theorem cell20_689688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_689688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689688 prefixEnd_689688 := by exact prefixLift 689688
  have htrace : WordTrace (prefixWord ++ tailWord_689688) baseStart_689688 baseEnd_689688 := by
    simpa [prefixWord, tailWord_689688, baseEnd_689688] using wordTrace_append hprefix tailTrace_689688
  have hstable : (prefixWord ++ tailWord_689688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689688).length < 2 ^ (prefixWord ++ tailWord_689688).sum := by decide
  have hdescent : baseEnd_689688 < baseStart_689688 := by decide
  rcases family_descends (prefixWord ++ tailWord_689688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689706 : List Nat := [3, 1, 4, 1, 1, 1, 2, 7]
def baseStart_689706 : Nat := 118140960795 + 689706 * 2 ^ 59
def prefixEnd_689706 : Nat := 4983230072969 + 3 ^ 40 * 689706 * 2
def baseEnd_689706 : Nat := 104933537271106298015735

theorem tailTrace_689706 : CollatzResearch.WordTrace tailWord_689706 prefixEnd_689706 104933537271106298015735 := by
  unfold tailWord_689706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288911109830107312994243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16770429626213619501317981 6288911109830107312994243)
  ·
    refine ⟨9433366664745160969491365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6288911109830107312994243 9433366664745160969491365)
    ·
      refine ⟨1768756249639717681779631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9433366664745160969491365 1768756249639717681779631)
      ·
        refine ⟨2653134374459576522669447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768756249639717681779631 2653134374459576522669447)
        ·
          refine ⟨3979701561689364784004171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653134374459576522669447 3979701561689364784004171)
          ·
            refine ⟨5969552342534047176006257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979701561689364784004171 5969552342534047176006257)
            ·
              refine ⟨4477164256900535382004693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5969552342534047176006257 4477164256900535382004693)
              ·
                refine ⟨104933537271106298015735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4477164256900535382004693 104933537271106298015735)
                ·
                  rfl

theorem cell20_689706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_689706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689706 prefixEnd_689706 := by exact prefixLift 689706
  have htrace : WordTrace (prefixWord ++ tailWord_689706) baseStart_689706 baseEnd_689706 := by
    simpa [prefixWord, tailWord_689706, baseEnd_689706] using wordTrace_append hprefix tailTrace_689706
  have hstable : (prefixWord ++ tailWord_689706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689706).length < 2 ^ (prefixWord ++ tailWord_689706).sum := by decide
  have hdescent : baseEnd_689706 < baseStart_689706 := by decide
  rcases family_descends (prefixWord ++ tailWord_689706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689751 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_689751 : Nat := 118140960795 + 689751 * 2 ^ 59
def prefixEnd_689751 : Nat := 4983230072969 + 3 ^ 40 * 689751 * 2
def baseEnd_689751 : Nat := 314821151039498737547021

theorem tailTrace_689751 : CollatzResearch.WordTrace tailWord_689751 prefixEnd_689751 314821151039498737547021 := by
  unfold tailWord_689751
  simp only [CollatzResearch.WordTrace]
  refine ⟨25157285724157401937365107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16771523816104934624910071 25157285724157401937365107)
  ·
    refine ⟨37735928586236102906047661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25157285724157401937365107 37735928586236102906047661)
    ·
      refine ⟨14150973219838538589767873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37735928586236102906047661 14150973219838538589767873)
      ·
        refine ⟨10613229914878903942325905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14150973219838538589767873 10613229914878903942325905)
        ·
          refine ⟨7959922436159177956744429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10613229914878903942325905 7959922436159177956744429)
          ·
            refine ⟨2984970913559691733779161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7959922436159177956744429 2984970913559691733779161)
            ·
              refine ⟨2238728185169768800334371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984970913559691733779161 2238728185169768800334371)
              ·
                refine ⟨3358092277754653200501557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238728185169768800334371 3358092277754653200501557)
                ·
                  refine ⟨314821151039498737547021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3358092277754653200501557 314821151039498737547021)
                  ·
                    rfl

theorem cell20_689751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_689751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689751 prefixEnd_689751 := by exact prefixLift 689751
  have htrace : WordTrace (prefixWord ++ tailWord_689751) baseStart_689751 baseEnd_689751 := by
    simpa [prefixWord, tailWord_689751, baseEnd_689751] using wordTrace_append hprefix tailTrace_689751
  have hstable : (prefixWord ++ tailWord_689751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689751).length < 2 ^ (prefixWord ++ tailWord_689751).sum := by decide
  have hdescent : baseEnd_689751 < baseStart_689751 := by decide
  rcases family_descends (prefixWord ++ tailWord_689751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689806 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_689806 : Nat := 118140960795 + 689806 * 2 ^ 59
def prefixEnd_689806 : Nat := 4983230072969 + 3 ^ 40 * 689806 * 2
def baseEnd_689806 : Nat := 314846254538162990713463

theorem tailTrace_689806 : CollatzResearch.WordTrace tailWord_689806 prefixEnd_689806 314846254538162990713463 := by
  unfold tailWord_689806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144911467369768291327159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16772861159305430887078181 3144911467369768291327159)
  ·
    refine ⟨4717367201054652436990739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3144911467369768291327159 4717367201054652436990739)
    ·
      refine ⟨7076050801581978655486109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4717367201054652436990739 7076050801581978655486109)
      ·
        refine ⟨2653519050593241995807291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7076050801581978655486109 2653519050593241995807291)
        ·
          refine ⟨3980278575889862993710937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653519050593241995807291 3980278575889862993710937)
          ·
            refine ⟨2985208931917397245283203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3980278575889862993710937 2985208931917397245283203)
            ·
              refine ⟨4477813397876095867924805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985208931917397245283203 4477813397876095867924805)
              ·
                refine ⟨839590012101767975235901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4477813397876095867924805 839590012101767975235901)
                ·
                  refine ⟨314846254538162990713463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839590012101767975235901 314846254538162990713463)
                  ·
                    rfl

theorem cell20_689806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_689806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689806 prefixEnd_689806 := by exact prefixLift 689806
  have htrace : WordTrace (prefixWord ++ tailWord_689806) baseStart_689806 baseEnd_689806 := by
    simpa [prefixWord, tailWord_689806, baseEnd_689806] using wordTrace_append hprefix tailTrace_689806
  have hstable : (prefixWord ++ tailWord_689806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689806).length < 2 ^ (prefixWord ++ tailWord_689806).sum := by decide
  have hdescent : baseEnd_689806 < baseStart_689806 := by decide
  rcases family_descends (prefixWord ++ tailWord_689806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689827 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 3]
def baseStart_689827 : Nat := 118140960795 + 689827 * 2 ^ 59
def prefixEnd_689827 : Nat := 4983230072969 + 3 ^ 40 * 689827 * 2
def baseEnd_689827 : Nat := 314855839510380251013377

theorem tailTrace_689827 : CollatzResearch.WordTrace tailWord_689827 prefixEnd_689827 314855839510380251013377 := by
  unfold tailWord_689827
  simp only [CollatzResearch.WordTrace]
  refine ⟨25160057671882066917131735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16773371781254711278087823 25160057671882066917131735)
  ·
    refine ⟨37740086507823100375697603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25160057671882066917131735 37740086507823100375697603)
    ·
      refine ⟨56610129761734650563546405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37740086507823100375697603 56610129761734650563546405)
      ·
        refine ⟨10614399330325246980664951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56610129761734650563546405 10614399330325246980664951)
        ·
          refine ⟨15921598995487870470997427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614399330325246980664951 15921598995487870470997427)
          ·
            refine ⟨23882398493231805706496141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921598995487870470997427 23882398493231805706496141)
            ·
              refine ⟨8955899434961927139936053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23882398493231805706496141 8955899434961927139936053)
              ·
                refine ⟨839615572027680669369005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8955899434961927139936053 839615572027680669369005)
                ·
                  refine ⟨314855839510380251013377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839615572027680669369005 314855839510380251013377)
                  ·
                    rfl

theorem cell20_689827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_689827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689827 prefixEnd_689827 := by exact prefixLift 689827
  have htrace : WordTrace (prefixWord ++ tailWord_689827) baseStart_689827 baseEnd_689827 := by
    simpa [prefixWord, tailWord_689827, baseEnd_689827] using wordTrace_append hprefix tailTrace_689827
  have hstable : (prefixWord ++ tailWord_689827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689827).length < 2 ^ (prefixWord ++ tailWord_689827).sum := by decide
  have hdescent : baseEnd_689827 < baseStart_689827 := by decide
  rcases family_descends (prefixWord ++ tailWord_689827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689837 : List Nat := [1, 5, 2, 1, 1, 1, 5, 4]
def baseStart_689837 : Nat := 118140960795 + 689837 * 2 ^ 59
def prefixEnd_689837 : Nat := 4983230072969 + 3 ^ 40 * 689837 * 2
def baseEnd_689837 : Nat := 104953467927621553560001

theorem tailTrace_689837 : CollatzResearch.WordTrace tailWord_689837 prefixEnd_689837 104953467927621553560001 := by
  unfold tailWord_689837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25160422401845838624995765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16773614934563892416663843 25160422401845838624995765)
  ·
    refine ⟨2358789600173047371093353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25160422401845838624995765 2358789600173047371093353)
    ·
      refine ⟨1769092200129785528320015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2358789600173047371093353 1769092200129785528320015)
      ·
        refine ⟨2653638300194678292480023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769092200129785528320015 2653638300194678292480023)
        ·
          refine ⟨3980457450292017438720035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653638300194678292480023 3980457450292017438720035)
          ·
            refine ⟨5970686175438026158080053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980457450292017438720035 5970686175438026158080053)
            ·
              refine ⟨559751828947314952320005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5970686175438026158080053 559751828947314952320005)
              ·
                refine ⟨104953467927621553560001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559751828947314952320005 104953467927621553560001)
                ·
                  rfl

theorem cell20_689837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_689837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689837 prefixEnd_689837 := by exact prefixLift 689837
  have htrace : WordTrace (prefixWord ++ tailWord_689837) baseStart_689837 baseEnd_689837 := by
    simpa [prefixWord, tailWord_689837, baseEnd_689837] using wordTrace_append hprefix tailTrace_689837
  have hstable : (prefixWord ++ tailWord_689837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689837).length < 2 ^ (prefixWord ++ tailWord_689837).sum := by decide
  have hdescent : baseEnd_689837 < baseStart_689837 := by decide
  rcases family_descends (prefixWord ++ tailWord_689837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689868 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_689868 : Nat := 118140960795 + 689868 * 2 ^ 59
def prefixEnd_689868 : Nat := 4983230072969 + 3 ^ 40 * 689868 * 2
def baseEnd_689868 : Nat := 314874553027566330646543

theorem tailTrace_689868 : CollatzResearch.WordTrace tailWord_689868 prefixEnd_689868 314874553027566330646543 := by
  unfold tailWord_689868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12580776532366765459687129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16774368709822353946249505 12580776532366765459687129)
  ·
    refine ⟨9435582399275074094765347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12580776532366765459687129 9435582399275074094765347)
    ·
      refine ⟨14153373598912611142148021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9435582399275074094765347 14153373598912611142148021)
      ·
        refine ⟨1326878774898057294576377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14153373598912611142148021 1326878774898057294576377)
        ·
          refine ⟨995159081173542970932283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326878774898057294576377 995159081173542970932283)
          ·
            refine ⟨1492738621760314456398425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995159081173542970932283 1492738621760314456398425)
            ·
              refine ⟨1119553966320235842298819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492738621760314456398425 1119553966320235842298819)
              ·
                refine ⟨1679330949480353763448229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119553966320235842298819 1679330949480353763448229)
                ·
                  refine ⟨314874553027566330646543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679330949480353763448229 314874553027566330646543)
                  ·
                    rfl

theorem cell20_689868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_689868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689868 prefixEnd_689868 := by exact prefixLift 689868
  have htrace : WordTrace (prefixWord ++ tailWord_689868) baseStart_689868 baseEnd_689868 := by
    simpa [prefixWord, tailWord_689868, baseEnd_689868] using wordTrace_append hprefix tailTrace_689868
  have hstable : (prefixWord ++ tailWord_689868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689868).length < 2 ^ (prefixWord ++ tailWord_689868).sum := by decide
  have hdescent : baseEnd_689868 < baseStart_689868 := by decide
  rcases family_descends (prefixWord ++ tailWord_689868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689879 : List Nat := [1, 1, 3, 2, 1, 3, 2, 7]
def baseStart_689879 : Nat := 118140960795 + 689879 * 2 ^ 59
def prefixEnd_689879 : Nat := 4983230072969 + 3 ^ 40 * 689879 * 2
def baseEnd_689879 : Nat := 104959857909099727093277

theorem tailTrace_689879 : CollatzResearch.WordTrace tailWord_689879 prefixEnd_689879 104959857909099727093277 := by
  unfold tailWord_689879
  simp only [CollatzResearch.WordTrace]
  refine ⟨25161954267693679798024691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16774636178462453198683127 25161954267693679798024691)
  ·
    refine ⟨37742931401540519697037037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25161954267693679798024691 37742931401540519697037037)
    ·
      refine ⟨14153599275577694886388889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37742931401540519697037037 14153599275577694886388889)
      ·
        refine ⟨10615199456683271164791667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14153599275577694886388889 10615199456683271164791667)
        ·
          refine ⟨15922799185024906747187501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10615199456683271164791667 15922799185024906747187501)
          ·
            refine ⟨5971049694384340030195313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15922799185024906747187501 5971049694384340030195313)
            ·
              refine ⟨4478287270788255022646485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971049694384340030195313 4478287270788255022646485)
              ·
                refine ⟨104959857909099727093277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4478287270788255022646485 104959857909099727093277)
                ·
                  rfl

theorem cell20_689879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_689879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689879 prefixEnd_689879 := by exact prefixLift 689879
  have htrace : WordTrace (prefixWord ++ tailWord_689879) baseStart_689879 baseEnd_689879 := by
    simpa [prefixWord, tailWord_689879, baseEnd_689879] using wordTrace_append hprefix tailTrace_689879
  have hstable : (prefixWord ++ tailWord_689879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689879).length < 2 ^ (prefixWord ++ tailWord_689879).sum := by decide
  have hdescent : baseEnd_689879 < baseStart_689879 := by decide
  rcases family_descends (prefixWord ++ tailWord_689879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689896 : List Nat := [2, 1, 4, 1, 3, 2, 1, 6]
def baseStart_689896 : Nat := 118140960795 + 689896 * 2 ^ 59
def prefixEnd_689896 : Nat := 4983230072969 + 3 ^ 40 * 689896 * 2
def baseEnd_689896 : Nat := 104962444330174225904365

theorem tailTrace_689896 : CollatzResearch.WordTrace tailWord_689896 prefixEnd_689896 104962444330174225904365 := by
  unfold tailWord_689896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12581287154316045850696771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16775049539088061134262361 12581287154316045850696771)
  ·
    refine ⟨18871930731474068776045157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12581287154316045850696771 18871930731474068776045157)
    ·
      refine ⟨3538487012151387895508467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18871930731474068776045157 3538487012151387895508467)
      ·
        refine ⟨5307730518227081843262701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3538487012151387895508467 5307730518227081843262701)
        ·
          refine ⟨1990398944335155691223513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5307730518227081843262701 1990398944335155691223513)
          ·
            refine ⟨1492799208251366768417635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1990398944335155691223513 1492799208251366768417635)
            ·
              refine ⟨2239198812377050152626453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492799208251366768417635 2239198812377050152626453)
              ·
                refine ⟨104962444330174225904365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2239198812377050152626453 104962444330174225904365)
                ·
                  rfl

theorem cell20_689896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_689896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689896 prefixEnd_689896 := by exact prefixLift 689896
  have htrace : WordTrace (prefixWord ++ tailWord_689896) baseStart_689896 baseEnd_689896 := by
    simpa [prefixWord, tailWord_689896, baseEnd_689896] using wordTrace_append hprefix tailTrace_689896
  have hstable : (prefixWord ++ tailWord_689896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689896).length < 2 ^ (prefixWord ++ tailWord_689896).sum := by decide
  have hdescent : baseEnd_689896 < baseStart_689896 := by decide
  rcases family_descends (prefixWord ++ tailWord_689896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689948 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_689948 : Nat := 118140960795 + 689948 * 2 ^ 59
def prefixEnd_689948 : Nat := 4983230072969 + 3 ^ 40 * 689948 * 2
def baseEnd_689948 : Nat := 314911067207441607979549

theorem tailTrace_689948 : CollatzResearch.WordTrace tailWord_689948 prefixEnd_689948 314911067207441607979549 := by
  unfold tailWord_689948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12582235452221852291143249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16776313936295803054857665 12582235452221852291143249)
  ·
    refine ⟨9436676589166389218357437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12582235452221852291143249 9436676589166389218357437)
    ·
      refine ⟨3538753720937395956884039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9436676589166389218357437 3538753720937395956884039)
      ·
        refine ⟨5308130581406093935326059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3538753720937395956884039 5308130581406093935326059)
        ·
          refine ⟨7962195872109140902989089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308130581406093935326059 7962195872109140902989089)
          ·
            refine ⟨5971646904081855677241817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7962195872109140902989089 5971646904081855677241817)
            ·
              refine ⟨4478735178061391757931363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971646904081855677241817 4478735178061391757931363)
              ·
                refine ⟨6718102767092087636897045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478735178061391757931363 6718102767092087636897045)
                ·
                  refine ⟨314911067207441607979549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6718102767092087636897045 314911067207441607979549)
                  ·
                    rfl

theorem cell20_689948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_689948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689948 prefixEnd_689948 := by exact prefixLift 689948
  have htrace : WordTrace (prefixWord ++ tailWord_689948) baseStart_689948 baseEnd_689948 := by
    simpa [prefixWord, tailWord_689948, baseEnd_689948] using wordTrace_append hprefix tailTrace_689948
  have hstable : (prefixWord ++ tailWord_689948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689948).length < 2 ^ (prefixWord ++ tailWord_689948).sum := by decide
  have hdescent : baseEnd_689948 < baseStart_689948 := by decide
  rcases family_descends (prefixWord ++ tailWord_689948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689955 : List Nat := [1, 1, 1, 4, 2, 1, 4, 6]
def baseStart_689955 : Nat := 118140960795 + 689955 * 2 ^ 59
def prefixEnd_689955 : Nat := 4983230072969 + 3 ^ 40 * 689955 * 2
def baseEnd_689955 : Nat := 104971420732726898248729

theorem tailTrace_689955 : CollatzResearch.WordTrace tailWord_689955 prefixEnd_689955 104971420732726898248729 := by
  unfold tailWord_689955
  simp only [CollatzResearch.WordTrace]
  refine ⟨25164726215418344777791319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16776484143612229851860879 25164726215418344777791319)
  ·
    refine ⟨37747089323127517166686979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25164726215418344777791319 37747089323127517166686979)
    ·
      refine ⟨56620633984691275750030469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37747089323127517166686979 56620633984691275750030469)
      ·
        refine ⟨10616368872129614203130713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56620633984691275750030469 10616368872129614203130713)
        ·
          refine ⟨7962276654097210652348035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10616368872129614203130713 7962276654097210652348035)
          ·
            refine ⟨11943414981145815978522053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7962276654097210652348035 11943414981145815978522053)
            ·
              refine ⟨2239390308964840495972885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11943414981145815978522053 2239390308964840495972885)
              ·
                refine ⟨104971420732726898248729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2239390308964840495972885 104971420732726898248729)
                ·
                  rfl

theorem cell20_689955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_689955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689955 prefixEnd_689955 := by exact prefixLift 689955
  have htrace : WordTrace (prefixWord ++ tailWord_689955) baseStart_689955 baseEnd_689955 := by
    simpa [prefixWord, tailWord_689955, baseEnd_689955] using wordTrace_append hprefix tailTrace_689955
  have hstable : (prefixWord ++ tailWord_689955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689955).length < 2 ^ (prefixWord ++ tailWord_689955).sum := by decide
  have hdescent : baseEnd_689955 < baseStart_689955 := by decide
  rcases family_descends (prefixWord ++ tailWord_689955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689972 : List Nat := [2, 5, 1, 1, 2, 9]
def baseStart_689972 : Nat := 118140960795 + 689972 * 2 ^ 59
def prefixEnd_689972 : Nat := 4983230072969 + 3 ^ 40 * 689972 * 2
def baseEnd_689972 : Nat := 11663778572644599673313

theorem tailTrace_689972 : CollatzResearch.WordTrace tailWord_689972 prefixEnd_689972 11663778572644599673313 := by
  unfold tailWord_689972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12582673128178378340580085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16776897504237837787440113 12582673128178378340580085)
  ·
    refine ⟨1179625605766722969429383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12582673128178378340580085 1179625605766722969429383)
    ·
      refine ⟨1769438408650084454144075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179625605766722969429383 1769438408650084454144075)
      ·
        refine ⟨2654157612975126681216113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769438408650084454144075 2654157612975126681216113)
        ·
          refine ⟨1990618209731345010912085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2654157612975126681216113 1990618209731345010912085)
          ·
            refine ⟨11663778572644599673313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1990618209731345010912085 11663778572644599673313)
            ·
              rfl

theorem cell20_689972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 9].length) (baseStart_689972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_689972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_689972 prefixEnd_689972 := by exact prefixLift 689972
  have htrace : WordTrace (prefixWord ++ tailWord_689972) baseStart_689972 baseEnd_689972 := by
    simpa [prefixWord, tailWord_689972, baseEnd_689972] using wordTrace_append hprefix tailTrace_689972
  have hstable : (prefixWord ++ tailWord_689972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689972).length < 2 ^ (prefixWord ++ tailWord_689972).sum := by decide
  have hdescent : baseEnd_689972 < baseStart_689972 := by decide
  rcases family_descends (prefixWord ++ tailWord_689972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690000 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_690000 : Nat := 118140960795 + 690000 * 2 ^ 59
def prefixEnd_690000 : Nat := 4983230072969 + 3 ^ 40 * 690000 * 2
def baseEnd_690000 : Nat := 314934801424360538246003

theorem tailTrace_690000 : CollatzResearch.WordTrace tailWord_690000 prefixEnd_690000 314934801424360538246003 := by
  unfold tailWord_690000
  simp only [CollatzResearch.WordTrace]
  refine ⟨12583183750127658731589727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16777578333503544975452969 12583183750127658731589727)
  ·
    refine ⟨18874775625191488097384591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12583183750127658731589727 18874775625191488097384591)
    ·
      refine ⟨28312163437787232146076887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18874775625191488097384591 28312163437787232146076887)
      ·
        refine ⟨42468245156680848219115331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28312163437787232146076887 42468245156680848219115331)
        ·
          refine ⟨63702367735021272328672997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42468245156680848219115331 63702367735021272328672997)
          ·
            refine ⟨11944193950316488561626187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63702367735021272328672997 11944193950316488561626187)
            ·
              refine ⟨17916290925474732842439281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11944193950316488561626187 17916290925474732842439281)
              ·
                refine ⟨13437218194106049631829461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17916290925474732842439281 13437218194106049631829461)
                ·
                  refine ⟨314934801424360538246003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13437218194106049631829461 314934801424360538246003)
                  ·
                    rfl

theorem cell20_690000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_690000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690000 prefixEnd_690000 := by exact prefixLift 690000
  have htrace : WordTrace (prefixWord ++ tailWord_690000) baseStart_690000 baseEnd_690000 := by
    simpa [prefixWord, tailWord_690000, baseEnd_690000] using wordTrace_append hprefix tailTrace_690000
  have hstable : (prefixWord ++ tailWord_690000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690000).length < 2 ^ (prefixWord ++ tailWord_690000).sum := by decide
  have hdescent : baseEnd_690000 < baseStart_690000 := by decide
  rcases family_descends (prefixWord ++ tailWord_690000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690010 : List Nat := [3, 1, 1, 2, 1, 3, 5, 4]
def baseStart_690010 : Nat := 118140960795 + 690010 * 2 ^ 59
def prefixEnd_690010 : Nat := 4983230072969 + 3 ^ 40 * 690010 * 2
def baseEnd_690010 : Nat := 104979788565614982637543

theorem tailTrace_690010 : CollatzResearch.WordTrace tailWord_690010 prefixEnd_690010 104979788565614982637543 := by
  unfold tailWord_690010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291683057554772292760871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16777821486812726114028989 6291683057554772292760871)
  ·
    refine ⟨9437524586332158439141307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6291683057554772292760871 9437524586332158439141307)
    ·
      refine ⟨14156286879498237658711961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9437524586332158439141307 14156286879498237658711961)
      ·
        refine ⟨10617215159623678244033971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14156286879498237658711961 10617215159623678244033971)
        ·
          refine ⟨15925822739435517366050957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10617215159623678244033971 15925822739435517366050957)
          ·
            refine ⟨5972183527288319012269109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15925822739435517366050957 5972183527288319012269109)
            ·
              refine ⟨559892205683279907400229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5972183527288319012269109 559892205683279907400229)
              ·
                refine ⟨104979788565614982637543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559892205683279907400229 104979788565614982637543)
                ·
                  rfl

theorem cell20_690010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_690010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690010 prefixEnd_690010 := by exact prefixLift 690010
  have htrace : WordTrace (prefixWord ++ tailWord_690010) baseStart_690010 baseEnd_690010 := by
    simpa [prefixWord, tailWord_690010, baseEnd_690010] using wordTrace_append hprefix tailTrace_690010
  have hstable : (prefixWord ++ tailWord_690010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690010).length < 2 ^ (prefixWord ++ tailWord_690010).sum := by decide
  have hdescent : baseEnd_690010 < baseStart_690010 := by decide
  rcases family_descends (prefixWord ++ tailWord_690010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690024 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_690024 : Nat := 118140960795 + 690024 * 2 ^ 59
def prefixEnd_690024 : Nat := 4983230072969 + 3 ^ 40 * 690024 * 2
def baseEnd_690024 : Nat := 314945755678323121445905

theorem tailTrace_690024 : CollatzResearch.WordTrace tailWord_690024 prefixEnd_690024 314945755678323121445905 := by
  unfold tailWord_690024
  simp only [CollatzResearch.WordTrace]
  refine ⟨12583621426084184781026563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16778161901445579708035417 12583621426084184781026563)
  ·
    refine ⟨18875432139126277171539845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12583621426084184781026563 18875432139126277171539845)
    ·
      refine ⟨3539143526086176969663721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18875432139126277171539845 3539143526086176969663721)
      ·
        refine ⟨2654357644564632727247791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3539143526086176969663721 2654357644564632727247791)
        ·
          refine ⟨3981536466846949090871687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654357644564632727247791 3981536466846949090871687)
          ·
            refine ⟨5972304700270423636307531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981536466846949090871687 5972304700270423636307531)
            ·
              refine ⟨8958457050405635454461297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5972304700270423636307531 8958457050405635454461297)
              ·
                refine ⟨6718842787804226590845973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8958457050405635454461297 6718842787804226590845973)
                ·
                  refine ⟨314945755678323121445905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6718842787804226590845973 314945755678323121445905)
                  ·
                    rfl

theorem cell20_690024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_690024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690024 prefixEnd_690024 := by exact prefixLift 690024
  have htrace : WordTrace (prefixWord ++ tailWord_690024) baseStart_690024 baseEnd_690024 := by
    simpa [prefixWord, tailWord_690024, baseEnd_690024] using wordTrace_append hprefix tailTrace_690024
  have hstable : (prefixWord ++ tailWord_690024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690024).length < 2 ^ (prefixWord ++ tailWord_690024).sum := by decide
  have hdescent : baseEnd_690024 < baseStart_690024 := by decide
  rcases family_descends (prefixWord ++ tailWord_690024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690041 : List Nat := [1, 2, 1, 3, 2, 2, 1, 6, 2]
def baseStart_690041 : Nat := 118140960795 + 690041 * 2 ^ 59
def prefixEnd_690041 : Nat := 4983230072969 + 3 ^ 40 * 690041 * 2
def baseEnd_690041 : Nat := 314953514941546617879169

theorem tailTrace_690041 : CollatzResearch.WordTrace tailWord_690041 prefixEnd_690041 314953514941546617879169 := by
  unfold tailWord_690041
  simp only [CollatzResearch.WordTrace]
  refine ⟨25167862893106781465421977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16778575262071187643614651 25167862893106781465421977)
  ·
    refine ⟨18875897169830086099066483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25167862893106781465421977 18875897169830086099066483)
    ·
      refine ⟨28313845754745129148599725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18875897169830086099066483 28313845754745129148599725)
      ·
        refine ⟨10617692158029423430724897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28313845754745129148599725 10617692158029423430724897)
        ·
          refine ⟨7963269118522067573043673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10617692158029423430724897 7963269118522067573043673)
          ·
            refine ⟨5972451838891550679782755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7963269118522067573043673 5972451838891550679782755)
            ·
              refine ⟨8958677758337326019674133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5972451838891550679782755 8958677758337326019674133)
              ·
                refine ⟨419938019922062157172225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8958677758337326019674133 419938019922062157172225)
                ·
                  refine ⟨314953514941546617879169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419938019922062157172225 314953514941546617879169)
                  ·
                    rfl

theorem cell20_690041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_690041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690041 prefixEnd_690041 := by exact prefixLift 690041
  have htrace : WordTrace (prefixWord ++ tailWord_690041) baseStart_690041 baseEnd_690041 := by
    simpa [prefixWord, tailWord_690041, baseEnd_690041] using wordTrace_append hprefix tailTrace_690041
  have hstable : (prefixWord ++ tailWord_690041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690041).length < 2 ^ (prefixWord ++ tailWord_690041).sum := by decide
  have hdescent : baseEnd_690041 < baseStart_690041 := by decide
  rcases family_descends (prefixWord ++ tailWord_690041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690069 : List Nat := [1, 3, 2, 1, 1, 3, 3, 6]
def baseStart_690069 : Nat := 118140960795 + 690069 * 2 ^ 59
def prefixEnd_690069 : Nat := 4983230072969 + 3 ^ 40 * 690069 * 2
def baseEnd_690069 : Nat := 104988764968167654981907

theorem tailTrace_690069 : CollatzResearch.WordTrace tailWord_690069 prefixEnd_690069 104988764968167654981907 := by
  unfold tailWord_690069
  simp only [CollatzResearch.WordTrace]
  refine ⟨25168884137005342247441261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16779256091336894831627507 25168884137005342247441261)
  ·
    refine ⟨9438331551377003342790473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25168884137005342247441261 9438331551377003342790473)
    ·
      refine ⟨7078748663532752507092855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9438331551377003342790473 7078748663532752507092855)
      ·
        refine ⟨10618122995299128760639283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7078748663532752507092855 10618122995299128760639283)
        ·
          refine ⟨15927184492948693140958925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10618122995299128760639283 15927184492948693140958925)
          ·
            refine ⟨5972694184855759927859597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15927184492948693140958925 5972694184855759927859597)
            ·
              refine ⟨2239760319320909972947349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5972694184855759927859597 2239760319320909972947349)
              ·
                refine ⟨104988764968167654981907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2239760319320909972947349 104988764968167654981907)
                ·
                  rfl

theorem cell20_690069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_690069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690069 prefixEnd_690069 := by exact prefixLift 690069
  have htrace : WordTrace (prefixWord ++ tailWord_690069) baseStart_690069 baseEnd_690069 := by
    simpa [prefixWord, tailWord_690069, baseEnd_690069] using wordTrace_append hprefix tailTrace_690069
  have hstable : (prefixWord ++ tailWord_690069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690069).length < 2 ^ (prefixWord ++ tailWord_690069).sum := by decide
  have hdescent : baseEnd_690069 < baseStart_690069 := by decide
  rcases family_descends (prefixWord ++ tailWord_690069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690110 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_690110 : Nat := 118140960795 + 690110 * 2 ^ 59
def prefixEnd_690110 : Nat := 4983230072969 + 3 ^ 40 * 690110 * 2
def baseEnd_690110 : Nat := 314985008421689044578887

theorem tailTrace_690110 : CollatzResearch.WordTrace tailWord_690110 prefixEnd_690110 314985008421689044578887 := by
  unfold tailWord_690110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146297441232100781210473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16780253019904537499789189 3146297441232100781210473)
  ·
    refine ⟨2359723080924075585907855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3146297441232100781210473 2359723080924075585907855)
    ·
      refine ⟨3539584621386113378861783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359723080924075585907855 3539584621386113378861783)
      ·
        refine ⟨5309376932079170068292675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539584621386113378861783 5309376932079170068292675)
        ·
          refine ⟨7964065398118755102439013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5309376932079170068292675 7964065398118755102439013)
          ·
            refine ⟨1493262262147266581707315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7964065398118755102439013 1493262262147266581707315)
            ·
              refine ⟨2239893393220899872560973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493262262147266581707315 2239893393220899872560973)
              ·
                refine ⟨839960022457837452210365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2239893393220899872560973 839960022457837452210365)
                ·
                  refine ⟨314985008421689044578887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839960022457837452210365 314985008421689044578887)
                  ·
                    rfl

theorem cell20_690110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_690110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690110 prefixEnd_690110 := by exact prefixLift 690110
  have htrace : WordTrace (prefixWord ++ tailWord_690110) baseStart_690110 baseEnd_690110 := by
    simpa [prefixWord, tailWord_690110, baseEnd_690110] using wordTrace_append hprefix tailTrace_690110
  have hstable : (prefixWord ++ tailWord_690110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690110).length < 2 ^ (prefixWord ++ tailWord_690110).sum := by decide
  have hdescent : baseEnd_690110 < baseStart_690110 := by decide
  rcases family_descends (prefixWord ++ tailWord_690110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690169 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 3]
def baseStart_690169 : Nat := 118140960795 + 690169 * 2 ^ 59
def prefixEnd_690169 : Nat := 4983230072969 + 3 ^ 40 * 690169 * 2
def baseEnd_690169 : Nat := 315011937629347061611979

theorem tailTrace_690169 : CollatzResearch.WordTrace tailWord_690169 prefixEnd_690169 315011937629347061611979 := by
  unfold tailWord_690169
  simp only [CollatzResearch.WordTrace]
  refine ⟨25172531436643059326081561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16781687624428706217387707 25172531436643059326081561)
  ·
    refine ⟨18879398577482294494561171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25172531436643059326081561 18879398577482294494561171)
    ·
      refine ⟨28319097866223441741841757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18879398577482294494561171 28319097866223441741841757)
      ·
        refine ⟨10619661699833790653190659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28319097866223441741841757 10619661699833790653190659)
        ·
          refine ⟨15929492549750685979785989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10619661699833790653190659 15929492549750685979785989)
          ·
            refine ⟨2986779853078253621209873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15929492549750685979785989 2986779853078253621209873)
            ·
              refine ⟨2240084889808690215907405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2986779853078253621209873 2240084889808690215907405)
              ·
                refine ⟨840031833678258830965277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240084889808690215907405 840031833678258830965277)
                ·
                  refine ⟨315011937629347061611979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840031833678258830965277 315011937629347061611979)
                  ·
                    rfl

theorem cell20_690169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_690169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690169 prefixEnd_690169 := by exact prefixLift 690169
  have htrace : WordTrace (prefixWord ++ tailWord_690169) baseStart_690169 baseEnd_690169 := by
    simpa [prefixWord, tailWord_690169, baseEnd_690169] using wordTrace_append hprefix tailTrace_690169
  have hstable : (prefixWord ++ tailWord_690169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690169).length < 2 ^ (prefixWord ++ tailWord_690169).sum := by decide
  have hdescent : baseEnd_690169 < baseStart_690169 := by decide
  rcases family_descends (prefixWord ++ tailWord_690169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690224 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_690224 : Nat := 118140960795 + 690224 * 2 ^ 59
def prefixEnd_690224 : Nat := 4983230072969 + 3 ^ 40 * 690224 * 2
def baseEnd_690224 : Nat := 315037041128011314778421

theorem tailTrace_690224 : CollatzResearch.WordTrace tailWord_690224 prefixEnd_690224 315037041128011314778421 := by
  unfold tailWord_690224
  simp only [CollatzResearch.WordTrace]
  refine ⟨12587268725721901859666863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16783024967629202479555817 12587268725721901859666863)
  ·
    refine ⟨18880903088582852789500295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12587268725721901859666863 18880903088582852789500295)
    ·
      refine ⟨28321354632874279184250443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18880903088582852789500295 28321354632874279184250443)
      ·
        refine ⟨42482031949311418776375665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28321354632874279184250443 42482031949311418776375665)
        ·
          refine ⟨31861523961983564082281749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42482031949311418776375665 31861523961983564082281749)
          ·
            refine ⟨1493508935717979566356957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31861523961983564082281749 1493508935717979566356957)
            ·
              refine ⟨560065850894242337383859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493508935717979566356957 560065850894242337383859)
              ·
                refine ⟨840098776341363506075789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560065850894242337383859 840098776341363506075789)
                ·
                  refine ⟨315037041128011314778421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840098776341363506075789 315037041128011314778421)
                  ·
                    rfl

theorem cell20_690224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_690224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690224 prefixEnd_690224 := by exact prefixLift 690224
  have htrace : WordTrace (prefixWord ++ tailWord_690224) baseStart_690224 baseEnd_690224 := by
    simpa [prefixWord, tailWord_690224, baseEnd_690224] using wordTrace_append hprefix tailTrace_690224
  have hstable : (prefixWord ++ tailWord_690224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690224).length < 2 ^ (prefixWord ++ tailWord_690224).sum := by decide
  have hdescent : baseEnd_690224 < baseStart_690224 := by decide
  rcases family_descends (prefixWord ++ tailWord_690224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690266 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_690266 : Nat := 118140960795 + 690266 * 2 ^ 59
def prefixEnd_690266 : Nat := 4983230072969 + 3 ^ 40 * 690266 * 2
def baseEnd_690266 : Nat := 315056211072445835378249

theorem tailTrace_690266 : CollatzResearch.WordTrace tailWord_690266 prefixEnd_690266 315056211072445835378249 := by
  unfold tailWord_690266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294017329322911223090663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16784046211527763261575101 6294017329322911223090663)
  ·
    refine ⟨9441025993984366834635995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6294017329322911223090663 9441025993984366834635995)
    ·
      refine ⟨14161538990976550251953993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9441025993984366834635995 14161538990976550251953993)
      ·
        refine ⟨10621154243232412688965495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14161538990976550251953993 10621154243232412688965495)
        ·
          refine ⟨15931731364848619033448243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10621154243232412688965495 15931731364848619033448243)
          ·
            refine ⟨23897597047272928550172365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15931731364848619033448243 23897597047272928550172365)
            ·
              refine ⟨8961598892727348206314637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23897597047272928550172365 8961598892727348206314637)
              ·
                refine ⟨3360599584772755577367989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8961598892727348206314637 3360599584772755577367989)
                ·
                  refine ⟨315056211072445835378249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3360599584772755577367989 315056211072445835378249)
                  ·
                    rfl

theorem cell20_690266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_690266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690266 prefixEnd_690266 := by exact prefixLift 690266
  have htrace : WordTrace (prefixWord ++ tailWord_690266) baseStart_690266 baseEnd_690266 := by
    simpa [prefixWord, tailWord_690266, baseEnd_690266] using wordTrace_append hprefix tailTrace_690266
  have hstable : (prefixWord ++ tailWord_690266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690266).length < 2 ^ (prefixWord ++ tailWord_690266).sum := by decide
  have hdescent : baseEnd_690266 < baseStart_690266 := by decide
  rcases family_descends (prefixWord ++ tailWord_690266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690297 : List Nat := [1, 2, 1, 3, 4, 1, 2, 6]
def baseStart_690297 : Nat := 118140960795 + 690297 * 2 ^ 59
def prefixEnd_690297 : Nat := 4983230072969 + 3 ^ 40 * 690297 * 2
def baseEnd_690297 : Nat := 105023453439049168448263

theorem tailTrace_690297 : CollatzResearch.WordTrace tailWord_690297 prefixEnd_690297 105023453439049168448263 := by
  unfold tailWord_690297
  simp only [CollatzResearch.WordTrace]
  refine ⟨25177199980179337186741145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16784799986786224791160763 25177199980179337186741145)
  ·
    refine ⟨18882899985134502890055859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25177199980179337186741145 18882899985134502890055859)
    ·
      refine ⟨28324349977701754335083789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18882899985134502890055859 28324349977701754335083789)
      ·
        refine ⟨10621631241638157875656421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28324349977701754335083789 10621631241638157875656421)
        ·
          refine ⟨1991555857807154601685579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10621631241638157875656421 1991555857807154601685579)
          ·
            refine ⟨2987333786710731902528369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991555857807154601685579 2987333786710731902528369)
            ·
              refine ⟨2240500340033048926896277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987333786710731902528369 2240500340033048926896277)
              ·
                refine ⟨105023453439049168448263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2240500340033048926896277 105023453439049168448263)
                ·
                  rfl

theorem cell20_690297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_690297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690297 prefixEnd_690297 := by exact prefixLift 690297
  have htrace : WordTrace (prefixWord ++ tailWord_690297) baseStart_690297 baseEnd_690297 := by
    simpa [prefixWord, tailWord_690297, baseEnd_690297] using wordTrace_append hprefix tailTrace_690297
  have hstable : (prefixWord ++ tailWord_690297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690297).length < 2 ^ (prefixWord ++ tailWord_690297).sum := by decide
  have hdescent : baseEnd_690297 < baseStart_690297 := by decide
  rcases family_descends (prefixWord ++ tailWord_690297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690338 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_690338 : Nat := 118140960795 + 690338 * 2 ^ 59
def prefixEnd_690338 : Nat := 4983230072969 + 3 ^ 40 * 690338 * 2
def baseEnd_690338 : Nat := 315089073834333584977955

theorem tailTrace_690338 : CollatzResearch.WordTrace tailWord_690338 prefixEnd_690338 315089073834333584977955 := by
  unfold tailWord_690338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294673843257700297245917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16785796915353867459322445 6294673843257700297245917)
  ·
    refine ⟨2360502691221637611467219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6294673843257700297245917 2360502691221637611467219)
    ·
      refine ⟨3540754036832456417200829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360502691221637611467219 3540754036832456417200829)
      ·
        refine ⟨1327782763812171156450311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3540754036832456417200829 1327782763812171156450311)
        ·
          refine ⟨1991674145718256734675467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327782763812171156450311 1991674145718256734675467)
          ·
            refine ⟨2987511218577385102013201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991674145718256734675467 2987511218577385102013201)
            ·
              refine ⟨2240633413933038826509901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987511218577385102013201 2240633413933038826509901)
              ·
                refine ⟨840237530224889559941213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240633413933038826509901 840237530224889559941213)
                ·
                  refine ⟨315089073834333584977955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840237530224889559941213 315089073834333584977955)
                  ·
                    rfl

theorem cell20_690338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_690338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690338 prefixEnd_690338 := by exact prefixLift 690338
  have htrace : WordTrace (prefixWord ++ tailWord_690338) baseStart_690338 baseEnd_690338 := by
    simpa [prefixWord, tailWord_690338, baseEnd_690338] using wordTrace_append hprefix tailTrace_690338
  have hstable : (prefixWord ++ tailWord_690338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690338).length < 2 ^ (prefixWord ++ tailWord_690338).sum := by decide
  have hdescent : baseEnd_690338 < baseStart_690338 := by decide
  rcases family_descends (prefixWord ++ tailWord_690338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690407 : List Nat := [1, 1, 5, 3, 1, 3, 2, 4]
def baseStart_690407 : Nat := 118140960795 + 690407 * 2 ^ 59
def prefixEnd_690407 : Nat := 4983230072969 + 3 ^ 40 * 690407 * 2
def baseEnd_690407 : Nat := 105040189104825337225891

theorem tailTrace_690407 : CollatzResearch.WordTrace tailWord_690407 prefixEnd_690407 105040189104825337225891 := by
  unfold tailWord_690407
  simp only [CollatzResearch.WordTrace]
  refine ⟨25181212009780825973245475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16787474673187217315496983 25181212009780825973245475)
  ·
    refine ⟨37771818014671238959868213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25181212009780825973245475 37771818014671238959868213)
    ·
      refine ⟨3541107938875428652487645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37771818014671238959868213 3541107938875428652487645)
      ·
        refine ⟨1327915477078285744682867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3541107938875428652487645 1327915477078285744682867)
        ·
          refine ⟨1991873215617428617024301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327915477078285744682867 1991873215617428617024301)
          ·
            refine ⟨746952455856535731384113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1991873215617428617024301 746952455856535731384113)
            ·
              refine ⟨560214341892401798538085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746952455856535731384113 560214341892401798538085)
              ·
                refine ⟨105040189104825337225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560214341892401798538085 105040189104825337225891)
                ·
                  rfl

theorem cell20_690407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_690407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690407 prefixEnd_690407 := by exact prefixLift 690407
  have htrace : WordTrace (prefixWord ++ tailWord_690407) baseStart_690407 baseEnd_690407 := by
    simpa [prefixWord, tailWord_690407, baseEnd_690407] using wordTrace_append hprefix tailTrace_690407
  have hstable : (prefixWord ++ tailWord_690407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690407).length < 2 ^ (prefixWord ++ tailWord_690407).sum := by decide
  have hdescent : baseEnd_690407 < baseStart_690407 := by decide
  rcases family_descends (prefixWord ++ tailWord_690407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690432 : List Nat := [2, 1, 1, 2, 1, 1, 12]
def baseStart_690432 : Nat := 118140960795 + 690432 * 2 ^ 59
def prefixEnd_690432 : Nat := 4983230072969 + 3 ^ 40 * 690432 * 2
def baseEnd_690432 : Nat := 35014664221743003982693

theorem tailTrace_690432 : CollatzResearch.WordTrace tailWord_690432 prefixEnd_690432 35014664221743003982693 := by
  unfold tailWord_690432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591061917345127621452775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16788082556460170161937033 12591061917345127621452775)
  ·
    refine ⟨18886592876017691432179163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12591061917345127621452775 18886592876017691432179163)
    ·
      refine ⟨28329889314026537148268745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18886592876017691432179163 28329889314026537148268745)
      ·
        refine ⟨21247416985519902861201559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28329889314026537148268745 21247416985519902861201559)
        ·
          refine ⟨31871125478279854291802339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21247416985519902861201559 31871125478279854291802339)
          ·
            refine ⟨47806688217419781437703509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31871125478279854291802339 47806688217419781437703509)
            ·
              refine ⟨35014664221743003982693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47806688217419781437703509 35014664221743003982693)
              ·
                rfl

theorem cell20_690432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 12].length) (baseStart_690432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690432 prefixEnd_690432 := by exact prefixLift 690432
  have htrace : WordTrace (prefixWord ++ tailWord_690432) baseStart_690432 baseEnd_690432 := by
    simpa [prefixWord, tailWord_690432, baseEnd_690432] using wordTrace_append hprefix tailTrace_690432
  have hstable : (prefixWord ++ tailWord_690432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690432).length < 2 ^ (prefixWord ++ tailWord_690432).sum := by decide
  have hdescent : baseEnd_690432 < baseStart_690432 := by decide
  rcases family_descends (prefixWord ++ tailWord_690432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690442 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_690442 : Nat := 118140960795 + 690442 * 2 ^ 59
def prefixEnd_690442 : Nat := 4983230072969 + 3 ^ 40 * 690442 * 2
def baseEnd_690442 : Nat := 315136542268171445510863

theorem tailTrace_690442 : CollatzResearch.WordTrace tailWord_690442 prefixEnd_690442 315136542268171445510863 := by
  unfold tailWord_690442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295622141163506737692395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16788325709769351300513053 6295622141163506737692395)
  ·
    refine ⟨9443433211745260106538593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6295622141163506737692395 9443433211745260106538593)
    ·
      refine ⟨7082574908808945079903945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9443433211745260106538593 7082574908808945079903945)
      ·
        refine ⟨5311931181606708809927959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7082574908808945079903945 5311931181606708809927959)
        ·
          refine ⟨7967896772410063214891939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5311931181606708809927959 7967896772410063214891939)
          ·
            refine ⟨11951845158615094822337909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7967896772410063214891939 11951845158615094822337909)
            ·
              refine ⟨1120485483620165139594179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11951845158615094822337909 1120485483620165139594179)
              ·
                refine ⟨1680728225430247709391269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120485483620165139594179 1680728225430247709391269)
                ·
                  refine ⟨315136542268171445510863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1680728225430247709391269 315136542268171445510863)
                  ·
                    rfl

theorem cell20_690442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_690442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690442 prefixEnd_690442 := by exact prefixLift 690442
  have htrace : WordTrace (prefixWord ++ tailWord_690442) baseStart_690442 baseEnd_690442 := by
    simpa [prefixWord, tailWord_690442, baseEnd_690442] using wordTrace_append hprefix tailTrace_690442
  have hstable : (prefixWord ++ tailWord_690442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690442).length < 2 ^ (prefixWord ++ tailWord_690442).sum := by decide
  have hdescent : baseEnd_690442 < baseStart_690442 := by decide
  rcases family_descends (prefixWord ++ tailWord_690442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690449 : List Nat := [1, 2, 2, 1, 1, 6, 2, 5]
def baseStart_690449 : Nat := 118140960795 + 690449 * 2 ^ 59
def prefixEnd_690449 : Nat := 4983230072969 + 3 ^ 40 * 690449 * 2
def baseEnd_690449 : Nat := 105046579086303510759167

theorem tailTrace_690449 : CollatzResearch.WordTrace tailWord_690449 prefixEnd_690449 105046579086303510759167 := by
  unfold tailWord_690449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25182743875628667146274401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16788495917085778097516267 25182743875628667146274401)
  ·
    refine ⟨18887057906721500359705801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25182743875628667146274401 18887057906721500359705801)
    ·
      refine ⟨14165293430041125269779351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18887057906721500359705801 14165293430041125269779351)
      ·
        refine ⟨21247940145061687904669027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14165293430041125269779351 21247940145061687904669027)
        ·
          refine ⟨31871910217592531857003541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21247940145061687904669027 31871910217592531857003541)
          ·
            refine ⟨1493995791449649930797041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31871910217592531857003541 1493995791449649930797041)
            ·
              refine ⟨1120496843587237448097781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493995791449649930797041 1120496843587237448097781)
              ·
                refine ⟨105046579086303510759167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1120496843587237448097781 105046579086303510759167)
                ·
                  rfl

theorem cell20_690449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_690449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690449 prefixEnd_690449 := by exact prefixLift 690449
  have htrace : WordTrace (prefixWord ++ tailWord_690449) baseStart_690449 baseEnd_690449 := by
    simpa [prefixWord, tailWord_690449, baseEnd_690449] using wordTrace_append hprefix tailTrace_690449
  have hstable : (prefixWord ++ tailWord_690449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690449).length < 2 ^ (prefixWord ++ tailWord_690449).sum := by decide
  have hdescent : baseEnd_690449 < baseStart_690449 := by decide
  rcases family_descends (prefixWord ++ tailWord_690449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690500 : List Nat := [2, 3, 4, 1, 3, 1, 1, 5]
def baseStart_690500 : Nat := 118140960795 + 690500 * 2 ^ 59
def prefixEnd_690500 : Nat := 4983230072969 + 3 ^ 40 * 690500 * 2
def baseEnd_690500 : Nat := 105054338349527007192431

theorem tailTrace_690500 : CollatzResearch.WordTrace tailWord_690500 prefixEnd_690500 105054338349527007192431 := by
  unfold tailWord_690500
  simp only [CollatzResearch.WordTrace]
  refine ⟨12592301999221951428190477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16789735998962601904253969 12592301999221951428190477)
  ·
    refine ⟨4722113249708231785571429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12592301999221951428190477 4722113249708231785571429)
    ·
      refine ⟨885396234320293459794643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4722113249708231785571429 885396234320293459794643)
      ·
        refine ⟨1328094351480440189691965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885396234320293459794643 1328094351480440189691965)
        ·
          refine ⟨498035381805165071134487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1328094351480440189691965 498035381805165071134487)
          ·
            refine ⟨747053072707747606701731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498035381805165071134487 747053072707747606701731)
            ·
              refine ⟨1120579609061621410052597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747053072707747606701731 1120579609061621410052597)
              ·
                refine ⟨105054338349527007192431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1120579609061621410052597 105054338349527007192431)
                ·
                  rfl

theorem cell20_690500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_690500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690500 prefixEnd_690500 := by exact prefixLift 690500
  have htrace : WordTrace (prefixWord ++ tailWord_690500) baseStart_690500 baseEnd_690500 := by
    simpa [prefixWord, tailWord_690500, baseEnd_690500] using wordTrace_append hprefix tailTrace_690500
  have hstable : (prefixWord ++ tailWord_690500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690500).length < 2 ^ (prefixWord ++ tailWord_690500).sum := by decide
  have hdescent : baseEnd_690500 < baseStart_690500 := by decide
  rcases family_descends (prefixWord ++ tailWord_690500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690532 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_690532 : Nat := 118140960795 + 690532 * 2 ^ 59
def prefixEnd_690532 : Nat := 4983230072969 + 3 ^ 40 * 690532 * 2
def baseEnd_690532 : Nat := 315177620720531132510495

theorem tailTrace_690532 : CollatzResearch.WordTrace tailWord_690532 prefixEnd_690532 315177620720531132510495 := by
  unfold tailWord_690532
  simp only [CollatzResearch.WordTrace]
  refine ⟨12592885567163986160772925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16790514089551981547697233 12592885567163986160772925)
  ·
    refine ⟨4722332087686494810289847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12592885567163986160772925 4722332087686494810289847)
    ·
      refine ⟨7083498131529742215434771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4722332087686494810289847 7083498131529742215434771)
      ·
        refine ⟨10625247197294613323152157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7083498131529742215434771 10625247197294613323152157)
        ·
          refine ⟨3984467698985479996182059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10625247197294613323152157 3984467698985479996182059)
          ·
            refine ⟨5976701548478219994273089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984467698985479996182059 5976701548478219994273089)
            ·
              refine ⟨4482526161358664995704817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5976701548478219994273089 4482526161358664995704817)
              ·
                refine ⟨3361894621018998746778613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4482526161358664995704817 3361894621018998746778613)
                ·
                  refine ⟨315177620720531132510495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3361894621018998746778613 315177620720531132510495)
                  ·
                    rfl

theorem cell20_690532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_690532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690532 prefixEnd_690532 := by exact prefixLift 690532
  have htrace : WordTrace (prefixWord ++ tailWord_690532) baseStart_690532 baseEnd_690532 := by
    simpa [prefixWord, tailWord_690532, baseEnd_690532] using wordTrace_append hprefix tailTrace_690532
  have hstable : (prefixWord ++ tailWord_690532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690532).length < 2 ^ (prefixWord ++ tailWord_690532).sum := by decide
  have hdescent : baseEnd_690532 < baseStart_690532 := by decide
  rcases family_descends (prefixWord ++ tailWord_690532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690535 : List Nat := [1, 1, 5, 1, 3, 1, 1, 5, 2]
def baseStart_690535 : Nat := 118140960795 + 690535 * 2 ^ 59
def prefixEnd_690535 : Nat := 4983230072969 + 3 ^ 40 * 690535 * 2
def baseEnd_690535 : Nat := 315178990002276455410483

theorem tailTrace_690535 : CollatzResearch.WordTrace tailWord_690535 prefixEnd_690535 315178990002276455410483 := by
  unfold tailWord_690535
  simp only [CollatzResearch.WordTrace]
  refine ⟨25185880553317103833905059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16790587035544735889270039 25185880553317103833905059)
  ·
    refine ⟨37778820829975655750857589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25185880553317103833905059 37778820829975655750857589)
    ·
      refine ⟨3541764452810217726642899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37778820829975655750857589 3541764452810217726642899)
      ·
        refine ⟨5312646679215326589964349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3541764452810217726642899 5312646679215326589964349)
        ·
          refine ⟨1992242504705747471236631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5312646679215326589964349 1992242504705747471236631)
          ·
            refine ⟨2988363757058621206854947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992242504705747471236631 2988363757058621206854947)
            ·
              refine ⟨4482545635587931810282421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2988363757058621206854947 4482545635587931810282421)
              ·
                refine ⟨420238653336368607213977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4482545635587931810282421 420238653336368607213977)
                ·
                  refine ⟨315178990002276455410483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420238653336368607213977 315178990002276455410483)
                  ·
                    rfl

theorem cell20_690535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 2].length) (baseStart_690535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690535 prefixEnd_690535 := by exact prefixLift 690535
  have htrace : WordTrace (prefixWord ++ tailWord_690535) baseStart_690535 baseEnd_690535 := by
    simpa [prefixWord, tailWord_690535, baseEnd_690535] using wordTrace_append hprefix tailTrace_690535
  have hstable : (prefixWord ++ tailWord_690535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690535).length < 2 ^ (prefixWord ++ tailWord_690535).sum := by decide
  have hdescent : baseEnd_690535 < baseStart_690535 := by decide
  rcases family_descends (prefixWord ++ tailWord_690535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690549 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_690549 : Nat := 118140960795 + 690549 * 2 ^ 59
def prefixEnd_690549 : Nat := 4983230072969 + 3 ^ 40 * 690549 * 2
def baseEnd_690549 : Nat := 315185379983754628943759

theorem tailTrace_690549 : CollatzResearch.WordTrace tailWord_690549 prefixEnd_690549 315185379983754628943759 := by
  unfold tailWord_690549
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186391175266384224914701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16790927450177589483276467 25186391175266384224914701)
  ·
    refine ⟨9444896690724894084343013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25186391175266384224914701 9444896690724894084343013)
    ·
      refine ⟨1770918129510917640814315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9444896690724894084343013 1770918129510917640814315)
      ·
        refine ⟨2656377194266376461221473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770918129510917640814315 2656377194266376461221473)
        ·
          refine ⟨1992282895699782345916105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2656377194266376461221473 1992282895699782345916105)
          ·
            refine ⟨1494212171774836759437079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992282895699782345916105 1494212171774836759437079)
            ·
              refine ⟨2241318257662255139155619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494212171774836759437079 2241318257662255139155619)
              ·
                refine ⟨3361977386493382708733429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241318257662255139155619 3361977386493382708733429)
                ·
                  refine ⟨315185379983754628943759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3361977386493382708733429 315185379983754628943759)
                  ·
                    rfl

theorem cell20_690549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_690549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690549 prefixEnd_690549 := by exact prefixLift 690549
  have htrace : WordTrace (prefixWord ++ tailWord_690549) baseStart_690549 baseEnd_690549 := by
    simpa [prefixWord, tailWord_690549, baseEnd_690549] using wordTrace_append hprefix tailTrace_690549
  have hstable : (prefixWord ++ tailWord_690549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690549).length < 2 ^ (prefixWord ++ tailWord_690549).sum := by decide
  have hdescent : baseEnd_690549 < baseStart_690549 := by decide
  rcases family_descends (prefixWord ++ tailWord_690549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690562 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_690562 : Nat := 118140960795 + 690562 * 2 ^ 59
def prefixEnd_690562 : Nat := 4983230072969 + 3 ^ 40 * 690562 * 2
def baseEnd_690562 : Nat := 315191313537984361510373

theorem tailTrace_690562 : CollatzResearch.WordTrace tailWord_690562 prefixEnd_690562 315191313537984361510373 := by
  unfold tailWord_690562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6296716331054821861284485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16791243549479524963425293 6296716331054821861284485)
  ·
    refine ⟨1180634312072779098990841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6296716331054821861284485 1180634312072779098990841)
    ·
      refine ⟨885475734054584324243131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1180634312072779098990841 885475734054584324243131)
      ·
        refine ⟨1328213601081876486364697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885475734054584324243131 1328213601081876486364697)
        ·
          refine ⟨996160200811407364773523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1328213601081876486364697 996160200811407364773523)
          ·
            refine ⟨1494240301217111047160285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996160200811407364773523 1494240301217111047160285)
            ·
              refine ⟨560340112956416642685107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1494240301217111047160285 560340112956416642685107)
              ·
                refine ⟨840510169434624964027661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560340112956416642685107 840510169434624964027661)
                ·
                  refine ⟨315191313537984361510373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840510169434624964027661 315191313537984361510373)
                  ·
                    rfl

theorem cell20_690562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_690562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690562 prefixEnd_690562 := by exact prefixLift 690562
  have htrace : WordTrace (prefixWord ++ tailWord_690562) baseStart_690562 baseEnd_690562 := by
    simpa [prefixWord, tailWord_690562, baseEnd_690562] using wordTrace_append hprefix tailTrace_690562
  have hstable : (prefixWord ++ tailWord_690562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690562).length < 2 ^ (prefixWord ++ tailWord_690562).sum := by decide
  have hdescent : baseEnd_690562 < baseStart_690562 := by decide
  rcases family_descends (prefixWord ++ tailWord_690562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690580 : List Nat := [2, 4, 2, 1, 3, 1, 1, 6]
def baseStart_690580 : Nat := 118140960795 + 690580 * 2 ^ 59
def prefixEnd_690580 : Nat := 4983230072969 + 3 ^ 40 * 690580 * 2
def baseEnd_690580 : Nat := 105066509742818766303433

theorem tailTrace_690580 : CollatzResearch.WordTrace tailWord_690580 prefixEnd_690580 105066509742818766303433 := by
  unfold tailWord_690580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12593760919077038259646597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16791681225436051012862129 12593760919077038259646597)
  ·
    refine ⟨2361330172326944673683737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12593760919077038259646597 2361330172326944673683737)
    ·
      refine ⟨1770997629245208505262803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2361330172326944673683737 1770997629245208505262803)
      ·
        refine ⟨2656496443867812757894205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770997629245208505262803 2656496443867812757894205)
        ·
          refine ⟨996186166450429784210327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2656496443867812757894205 996186166450429784210327)
          ·
            refine ⟨1494279249675644676315491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996186166450429784210327 1494279249675644676315491)
            ·
              refine ⟨2241418874513467014473237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494279249675644676315491 2241418874513467014473237)
              ·
                refine ⟨105066509742818766303433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2241418874513467014473237 105066509742818766303433)
                ·
                  rfl

theorem cell20_690580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_690580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690580 prefixEnd_690580 := by exact prefixLift 690580
  have htrace : WordTrace (prefixWord ++ tailWord_690580) baseStart_690580 baseEnd_690580 := by
    simpa [prefixWord, tailWord_690580, baseEnd_690580] using wordTrace_append hprefix tailTrace_690580
  have hstable : (prefixWord ++ tailWord_690580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690580).length < 2 ^ (prefixWord ++ tailWord_690580).sum := by decide
  have hdescent : baseEnd_690580 < baseStart_690580 := by decide
  rcases family_descends (prefixWord ++ tailWord_690580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690582 : List Nat := [5, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_690582 : Nat := 118140960795 + 690582 * 2 ^ 59
def prefixEnd_690582 : Nat := 4983230072969 + 3 ^ 40 * 690582 * 2
def baseEnd_690582 : Nat := 315200442082953180843625

theorem tailTrace_690582 : CollatzResearch.WordTrace tailWord_690582 prefixEnd_690582 315200442082953180843625 := by
  unfold tailWord_690582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574224674009176928804125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16791729856097887240577333 1574224674009176928804125)
  ·
    refine ⟨590334252753441348301547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1574224674009176928804125 590334252753441348301547)
    ·
      refine ⟨885501379130162022452321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590334252753441348301547 885501379130162022452321)
      ·
        refine ⟨664126034347621516839241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 885501379130162022452321 664126034347621516839241)
        ·
          refine ⟨498094525760716137629431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664126034347621516839241 498094525760716137629431)
          ·
            refine ⟨747141788641074206444147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498094525760716137629431 747141788641074206444147)
            ·
              refine ⟨1120712682961611309666221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747141788641074206444147 1120712682961611309666221)
              ·
                refine ⟨420267256110604241124833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1120712682961611309666221 420267256110604241124833)
                ·
                  refine ⟨315200442082953180843625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420267256110604241124833 315200442082953180843625)
                  ·
                    rfl

theorem cell20_690582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_690582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690582 prefixEnd_690582 := by exact prefixLift 690582
  have htrace : WordTrace (prefixWord ++ tailWord_690582) baseStart_690582 baseEnd_690582 := by
    simpa [prefixWord, tailWord_690582, baseEnd_690582] using wordTrace_append hprefix tailTrace_690582
  have hstable : (prefixWord ++ tailWord_690582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690582).length < 2 ^ (prefixWord ++ tailWord_690582).sum := by decide
  have hdescent : baseEnd_690582 < baseStart_690582 := by decide
  rcases family_descends (prefixWord ++ tailWord_690582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690663 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 3]
def baseStart_690663 : Nat := 118140960795 + 690663 * 2 ^ 59
def prefixEnd_690663 : Nat := 4983230072969 + 3 ^ 40 * 690663 * 2
def baseEnd_690663 : Nat := 315237412690076899143293

theorem tailTrace_690663 : CollatzResearch.WordTrace tailWord_690663 prefixEnd_690663 315237412690076899143293 := by
  unfold tailWord_690663
  simp only [CollatzResearch.WordTrace]
  refine ⟨25190549096853381694564643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16793699397902254463043095 25190549096853381694564643)
  ·
    refine ⟨37785823645280072541846965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25190549096853381694564643 37785823645280072541846965)
    ·
      refine ⟨3542420966745006800798153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37785823645280072541846965 3542420966745006800798153)
      ·
        refine ⟨2656815725058755100598615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3542420966745006800798153 2656815725058755100598615)
        ·
          refine ⟨3985223587588132650897923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656815725058755100598615 3985223587588132650897923)
          ·
            refine ⟨5977835381382198976346885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985223587588132650897923 5977835381382198976346885)
            ·
              refine ⟨1120844134009162308065041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5977835381382198976346885 1120844134009162308065041)
              ·
                refine ⟨840633100506871731048781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120844134009162308065041 840633100506871731048781)
                ·
                  refine ⟨315237412690076899143293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840633100506871731048781 315237412690076899143293)
                  ·
                    rfl

theorem cell20_690663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_690663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690663 prefixEnd_690663 := by exact prefixLift 690663
  have htrace : WordTrace (prefixWord ++ tailWord_690663) baseStart_690663 baseEnd_690663 := by
    simpa [prefixWord, tailWord_690663, baseEnd_690663] using wordTrace_append hprefix tailTrace_690663
  have hstable : (prefixWord ++ tailWord_690663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690663).length < 2 ^ (prefixWord ++ tailWord_690663).sum := by decide
  have hdescent : baseEnd_690663 < baseStart_690663 := by decide
  rcases family_descends (prefixWord ++ tailWord_690663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690666 : List Nat := [3, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_690666 : Nat := 118140960795 + 690666 * 2 ^ 59
def prefixEnd_690666 : Nat := 4983230072969 + 3 ^ 40 * 690666 * 2
def baseEnd_690666 : Nat := 315238781971822222043281

theorem tailTrace_690666 : CollatzResearch.WordTrace tailWord_690666 prefixEnd_690666 315238781971822222043281 := by
  unfold tailWord_690666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297664628960628301730963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16793772343895008804615901 6297664628960628301730963)
  ·
    refine ⟨9446496943440942452596445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6297664628960628301730963 9446496943440942452596445)
    ·
      refine ⟨3542436353790353419723667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9446496943440942452596445 3542436353790353419723667)
      ·
        refine ⟨5313654530685530129585501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542436353790353419723667 5313654530685530129585501)
        ·
          refine ⟨1992620449007073798594563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5313654530685530129585501 1992620449007073798594563)
          ·
            refine ⟨2988930673510610697891845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992620449007073798594563 2988930673510610697891845)
            ·
              refine ⟨560424501283239505854721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2988930673510610697891845 560424501283239505854721)
              ·
                refine ⟨420318375962429629391041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560424501283239505854721 420318375962429629391041)
                ·
                  refine ⟨315238781971822222043281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420318375962429629391041 315238781971822222043281)
                  ·
                    rfl

theorem cell20_690666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_690666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690666 prefixEnd_690666 := by exact prefixLift 690666
  have htrace : WordTrace (prefixWord ++ tailWord_690666) baseStart_690666 baseEnd_690666 := by
    simpa [prefixWord, tailWord_690666, baseEnd_690666] using wordTrace_append hprefix tailTrace_690666
  have hstable : (prefixWord ++ tailWord_690666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690666).length < 2 ^ (prefixWord ++ tailWord_690666).sum := by decide
  have hdescent : baseEnd_690666 < baseStart_690666 := by decide
  rcases family_descends (prefixWord ++ tailWord_690666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690691 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_690691 : Nat := 118140960795 + 690691 * 2 ^ 59
def prefixEnd_690691 : Nat := 4983230072969 + 3 ^ 40 * 690691 * 2
def baseEnd_690691 : Nat := 315250192653033246209845

theorem tailTrace_690691 : CollatzResearch.WordTrace tailWord_690691 prefixEnd_690691 315250192653033246209845 := by
  unfold tailWord_690691
  simp only [CollatzResearch.WordTrace]
  refine ⟨25191570340751942476583927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16794380227167961651055951 25191570340751942476583927)
  ·
    refine ⟨37787355511127913714875891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25191570340751942476583927 37787355511127913714875891)
    ·
      refine ⟨56681033266691870572313837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37787355511127913714875891 56681033266691870572313837)
      ·
        refine ⟨21255387475009451464617689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56681033266691870572313837 21255387475009451464617689)
        ·
          refine ⟨15941540606257088598463267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21255387475009451464617689 15941540606257088598463267)
          ·
            refine ⟨23912310909385632897694901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15941540606257088598463267 23912310909385632897694901)
            ·
              refine ⟨2241779147754903084158897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23912310909385632897694901 2241779147754903084158897)
              ·
                refine ⟨1681334360816177313119173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241779147754903084158897 1681334360816177313119173)
                ·
                  refine ⟨315250192653033246209845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681334360816177313119173 315250192653033246209845)
                  ·
                    rfl

theorem cell20_690691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_690691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690691 prefixEnd_690691 := by exact prefixLift 690691
  have htrace : WordTrace (prefixWord ++ tailWord_690691) baseStart_690691 baseEnd_690691 := by
    simpa [prefixWord, tailWord_690691, baseEnd_690691] using wordTrace_append hprefix tailTrace_690691
  have hstable : (prefixWord ++ tailWord_690691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690691).length < 2 ^ (prefixWord ++ tailWord_690691).sum := by decide
  have hdescent : baseEnd_690691 < baseStart_690691 := by decide
  rcases family_descends (prefixWord ++ tailWord_690691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690739 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 3]
def baseStart_690739 : Nat := 118140960795 + 690739 * 2 ^ 59
def prefixEnd_690739 : Nat := 4983230072969 + 3 ^ 40 * 690739 * 2
def baseEnd_690739 : Nat := 315272101160958412609649

theorem tailTrace_690739 : CollatzResearch.WordTrace tailWord_690739 prefixEnd_690739 315272101160958412609649 := by
  unfold tailWord_690739
  simp only [CollatzResearch.WordTrace]
  refine ⟨25193321044578046674331271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16795547363052031116220847 25193321044578046674331271)
  ·
    refine ⟨37789981566867070011496907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25193321044578046674331271 37789981566867070011496907)
    ·
      refine ⟨56684972350300605017245361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37789981566867070011496907 56684972350300605017245361)
      ·
        refine ⟨42513729262725453762934021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56684972350300605017245361 42513729262725453762934021)
        ·
          refine ⟨7971324236761022580550129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42513729262725453762934021 7971324236761022580550129)
          ·
            refine ⟨5978493177570766935412597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7971324236761022580550129 5978493177570766935412597)
            ·
              refine ⟨560483735397259400194931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5978493177570766935412597 560483735397259400194931)
              ·
                refine ⟨840725603095889100292397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560483735397259400194931 840725603095889100292397)
                ·
                  refine ⟨315272101160958412609649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840725603095889100292397 315272101160958412609649)
                  ·
                    rfl

theorem cell20_690739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 3].length) (baseStart_690739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690739 prefixEnd_690739 := by exact prefixLift 690739
  have htrace : WordTrace (prefixWord ++ tailWord_690739) baseStart_690739 baseEnd_690739 := by
    simpa [prefixWord, tailWord_690739, baseEnd_690739] using wordTrace_append hprefix tailTrace_690739
  have hstable : (prefixWord ++ tailWord_690739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690739).length < 2 ^ (prefixWord ++ tailWord_690739).sum := by decide
  have hdescent : baseEnd_690739 < baseStart_690739 := by decide
  rcases family_descends (prefixWord ++ tailWord_690739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690753 : List Nat := [1, 2, 5, 1, 1, 3, 1, 6]
def baseStart_690753 : Nat := 118140960795 + 690753 * 2 ^ 59
def prefixEnd_690753 : Nat := 4983230072969 + 3 ^ 40 * 690753 * 2
def baseEnd_690753 : Nat := 105092830380812195380975

theorem tailTrace_690753 : CollatzResearch.WordTrace tailWord_690753 prefixEnd_690753 105092830380812195380975 := by
  unfold tailWord_690753
  simp only [CollatzResearch.WordTrace]
  refine ⟨25193831666527327065340913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16795887777684884710227275 25193831666527327065340913)
  ·
    refine ⟨18895373749895495299005685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25193831666527327065340913 18895373749895495299005685)
    ·
      refine ⟨1771441289052702684281783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18895373749895495299005685 1771441289052702684281783)
      ·
        refine ⟨2657161933579054026422675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771441289052702684281783 2657161933579054026422675)
        ·
          refine ⟨3985742900368581039634013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657161933579054026422675 3985742900368581039634013)
          ·
            refine ⟨1494653587638217889862755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3985742900368581039634013 1494653587638217889862755)
            ·
              refine ⟨2241980381457326834794133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494653587638217889862755 2241980381457326834794133)
              ·
                refine ⟨105092830380812195380975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2241980381457326834794133 105092830380812195380975)
                ·
                  rfl

theorem cell20_690753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_690753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690753 prefixEnd_690753 := by exact prefixLift 690753
  have htrace : WordTrace (prefixWord ++ tailWord_690753) baseStart_690753 baseEnd_690753 := by
    simpa [prefixWord, tailWord_690753, baseEnd_690753] using wordTrace_append hprefix tailTrace_690753
  have hstable : (prefixWord ++ tailWord_690753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690753).length < 2 ^ (prefixWord ++ tailWord_690753).sum := by decide
  have hdescent : baseEnd_690753 < baseStart_690753 := by decide
  rcases family_descends (prefixWord ++ tailWord_690753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690780 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 4]
def baseStart_690780 : Nat := 118140960795 + 690780 * 2 ^ 59
def prefixEnd_690780 : Nat := 4983230072969 + 3 ^ 40 * 690780 * 2
def baseEnd_690780 : Nat := 315290814678144492242815

theorem tailTrace_690780 : CollatzResearch.WordTrace tailWord_690780 prefixEnd_690780 315290814678144492242815 := by
  unfold tailWord_690780
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597408218714755338286897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16796544291619673784382529 12597408218714755338286897)
  ·
    refine ⟨9448056164036066503715173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12597408218714755338286897 9448056164036066503715173)
    ·
      refine ⟨1771510530756762469446595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9448056164036066503715173 1771510530756762469446595)
      ·
        refine ⟨2657265796135143704169893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771510530756762469446595 2657265796135143704169893)
        ·
          refine ⟨498237336775339444531855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2657265796135143704169893 498237336775339444531855)
          ·
            refine ⟨747356005163009166797783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498237336775339444531855 747356005163009166797783)
            ·
              refine ⟨1121034007744513750196675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747356005163009166797783 1121034007744513750196675)
              ·
                refine ⟨1681551011616770625295013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121034007744513750196675 1681551011616770625295013)
                ·
                  refine ⟨315290814678144492242815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681551011616770625295013 315290814678144492242815)
                  ·
                    rfl

theorem cell20_690780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_690780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690780 prefixEnd_690780 := by exact prefixLift 690780
  have htrace : WordTrace (prefixWord ++ tailWord_690780) baseStart_690780 baseEnd_690780 := by
    simpa [prefixWord, tailWord_690780, baseEnd_690780] using wordTrace_append hprefix tailTrace_690780
  have hstable : (prefixWord ++ tailWord_690780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690780).length < 2 ^ (prefixWord ++ tailWord_690780).sum := by decide
  have hdescent : baseEnd_690780 < baseStart_690780 := by decide
  rcases family_descends (prefixWord ++ tailWord_690780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690784 : List Nat := [2, 1, 1, 3, 2, 1, 2, 6, 2]
def baseStart_690784 : Nat := 118140960795 + 690784 * 2 ^ 59
def prefixEnd_690784 : Nat := 4983230072969 + 3 ^ 40 * 690784 * 2
def baseEnd_690784 : Nat := 315292640387138256109465

theorem tailTrace_690784 : CollatzResearch.WordTrace tailWord_690784 prefixEnd_690784 315292640387138256109465 := by
  unfold tailWord_690784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597481164707509679859703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16796641552943346239812937 12597481164707509679859703)
  ·
    refine ⟨18896221747061264519789555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12597481164707509679859703 18896221747061264519789555)
    ·
      refine ⟨28344332620591896779684333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18896221747061264519789555 28344332620591896779684333)
      ·
        refine ⟨10629124732721961292381625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28344332620591896779684333 10629124732721961292381625)
        ·
          refine ⟨7971843549541470969286219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10629124732721961292381625 7971843549541470969286219)
          ·
            refine ⟨11957765324312206453929329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7971843549541470969286219 11957765324312206453929329)
            ·
              refine ⟨8968323993234154840446997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11957765324312206453929329 8968323993234154840446997)
              ·
                refine ⟨420390187182851008145953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8968323993234154840446997 420390187182851008145953)
                ·
                  refine ⟨315292640387138256109465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420390187182851008145953 315292640387138256109465)
                  ·
                    rfl

theorem cell20_690784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_690784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690784 prefixEnd_690784 := by exact prefixLift 690784
  have htrace : WordTrace (prefixWord ++ tailWord_690784) baseStart_690784 baseEnd_690784 := by
    simpa [prefixWord, tailWord_690784, baseEnd_690784] using wordTrace_append hprefix tailTrace_690784
  have hstable : (prefixWord ++ tailWord_690784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690784).length < 2 ^ (prefixWord ++ tailWord_690784).sum := by decide
  have hdescent : baseEnd_690784 < baseStart_690784 := by decide
  rcases family_descends (prefixWord ++ tailWord_690784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690812 : List Nat := [2, 2, 2, 1, 1, 2, 4, 6]
def baseStart_690812 : Nat := 118140960795 + 690812 * 2 ^ 59
def prefixEnd_690812 : Nat := 4983230072969 + 3 ^ 40 * 690812 * 2
def baseEnd_690812 : Nat := 105101806783364867725339

theorem tailTrace_690812 : CollatzResearch.WordTrace tailWord_690812 prefixEnd_690812 105101806783364867725339 := by
  unfold tailWord_690812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597991786656790070869345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16797322382209053427825793 12597991786656790070869345)
  ·
    refine ⟨9448493839992592553152009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12597991786656790070869345 9448493839992592553152009)
    ·
      refine ⟨7086370379994444414864007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9448493839992592553152009 7086370379994444414864007)
      ·
        refine ⟨10629555569991666622296011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086370379994444414864007 10629555569991666622296011)
        ·
          refine ⟨15944333354987499933444017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10629555569991666622296011 15944333354987499933444017)
          ·
            refine ⟨11958250016240624950083013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15944333354987499933444017 11958250016240624950083013)
            ·
              refine ⟨2242171878045117178140565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11958250016240624950083013 2242171878045117178140565)
              ·
                refine ⟨105101806783364867725339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2242171878045117178140565 105101806783364867725339)
                ·
                  rfl

theorem cell20_690812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_690812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690812 prefixEnd_690812 := by exact prefixLift 690812
  have htrace : WordTrace (prefixWord ++ tailWord_690812) baseStart_690812 baseEnd_690812 := by
    simpa [prefixWord, tailWord_690812, baseEnd_690812] using wordTrace_append hprefix tailTrace_690812
  have hstable : (prefixWord ++ tailWord_690812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690812).length < 2 ^ (prefixWord ++ tailWord_690812).sum := by decide
  have hdescent : baseEnd_690812 < baseStart_690812 := by decide
  rcases family_descends (prefixWord ++ tailWord_690812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690819 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_690819 : Nat := 118140960795 + 690819 * 2 ^ 59
def prefixEnd_690819 : Nat := 4983230072969 + 3 ^ 40 * 690819 * 2
def baseEnd_690819 : Nat := 315308615340833689942655

theorem tailTrace_690819 : CollatzResearch.WordTrace tailWord_690819 prefixEnd_690819 315308615340833689942655 := by
  unfold tailWord_690819
  simp only [CollatzResearch.WordTrace]
  refine ⟨25196238884288220337243511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16797492589525480224829007 25196238884288220337243511)
  ·
    refine ⟨37794358326432330505865267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25196238884288220337243511 37794358326432330505865267)
    ·
      refine ⟨56691537489648495758797901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37794358326432330505865267 56691537489648495758797901)
      ·
        refine ⟨21259326558618185909549213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56691537489648495758797901 21259326558618185909549213)
        ·
          refine ⟨7972247459481819716080955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21259326558618185909549213 7972247459481819716080955)
          ·
            refine ⟨11958371189222729574121433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7972247459481819716080955 11958371189222729574121433)
            ·
              refine ⟨8968778391917047180591075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11958371189222729574121433 8968778391917047180591075)
              ·
                refine ⟨13453167587875570770886613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8968778391917047180591075 13453167587875570770886613)
                ·
                  refine ⟨315308615340833689942655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13453167587875570770886613 315308615340833689942655)
                  ·
                    rfl

theorem cell20_690819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_690819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690819 prefixEnd_690819 := by exact prefixLift 690819
  have htrace : WordTrace (prefixWord ++ tailWord_690819) baseStart_690819 baseEnd_690819 := by
    simpa [prefixWord, tailWord_690819, baseEnd_690819] using wordTrace_append hprefix tailTrace_690819
  have hstable : (prefixWord ++ tailWord_690819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690819).length < 2 ^ (prefixWord ++ tailWord_690819).sum := by decide
  have hdescent : baseEnd_690819 < baseStart_690819 := by decide
  rcases family_descends (prefixWord ++ tailWord_690819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690867 : List Nat := [1, 1, 1, 2, 3, 5, 3, 4]
def baseStart_690867 : Nat := 118140960795 + 690867 * 2 ^ 59
def prefixEnd_690867 : Nat := 4983230072969 + 3 ^ 40 * 690867 * 2
def baseEnd_690867 : Nat := 105110174616252952114153

theorem tailTrace_690867 : CollatzResearch.WordTrace tailWord_690867 prefixEnd_690867 105110174616252952114153 := by
  unfold tailWord_690867
  simp only [CollatzResearch.WordTrace]
  refine ⟨25197989588114324534990855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16798659725409549689993903 25197989588114324534990855)
  ·
    refine ⟨37796984382171486802486283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25197989588114324534990855 37796984382171486802486283)
    ·
      refine ⟨56695476573257230203729425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37796984382171486802486283 56695476573257230203729425)
      ·
        refine ⟨42521607429942922652797069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56695476573257230203729425 42521607429942922652797069)
        ·
          refine ⟨15945602786228595994798901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42521607429942922652797069 15945602786228595994798901)
          ·
            refine ⟨1494900261208930874512397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15945602786228595994798901 1494900261208930874512397)
            ·
              refine ⟨560587597953349077942149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1494900261208930874512397 560587597953349077942149)
              ·
                refine ⟨105110174616252952114153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560587597953349077942149 105110174616252952114153)
                ·
                  rfl

theorem cell20_690867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_690867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690867 prefixEnd_690867 := by exact prefixLift 690867
  have htrace : WordTrace (prefixWord ++ tailWord_690867) baseStart_690867 baseEnd_690867 := by
    simpa [prefixWord, tailWord_690867, baseEnd_690867] using wordTrace_append hprefix tailTrace_690867
  have hstable : (prefixWord ++ tailWord_690867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690867).length < 2 ^ (prefixWord ++ tailWord_690867).sum := by decide
  have hdescent : baseEnd_690867 < baseStart_690867 := by decide
  rcases family_descends (prefixWord ++ tailWord_690867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690877 : List Nat := [1, 4, 1, 2, 1, 4, 2, 3, 2]
def baseStart_690877 : Nat := 118140960795 + 690877 * 2 ^ 59
def prefixEnd_690877 : Nat := 4983230072969 + 3 ^ 40 * 690877 * 2
def baseEnd_690877 : Nat := 315335088121243266009085

theorem tailTrace_690877 : CollatzResearch.WordTrace tailWord_690877 prefixEnd_690877 315335088121243266009085 := by
  unfold tailWord_690877
  simp only [CollatzResearch.WordTrace]
  refine ⟨25198354318078096242854885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16798902878718730828569923 25198354318078096242854885)
  ·
    refine ⟨4724691434639643045535291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25198354318078096242854885 4724691434639643045535291)
    ·
      refine ⟨7087037151959464568302937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4724691434639643045535291 7087037151959464568302937)
      ·
        refine ⟨5315277863969598426227203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7087037151959464568302937 5315277863969598426227203)
        ·
          refine ⟨7972916795954397639340805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315277863969598426227203 7972916795954397639340805)
          ·
            refine ⟨1494921899241449557376401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7972916795954397639340805 1494921899241449557376401)
            ·
              refine ⟨1121191424431087168032301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494921899241449557376401 1121191424431087168032301)
              ·
                refine ⟨420446784161657688012113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1121191424431087168032301 420446784161657688012113)
                ·
                  refine ⟨315335088121243266009085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420446784161657688012113 315335088121243266009085)
                  ·
                    rfl

theorem cell20_690877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_690877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690877 prefixEnd_690877 := by exact prefixLift 690877
  have htrace : WordTrace (prefixWord ++ tailWord_690877) baseStart_690877 baseEnd_690877 := by
    simpa [prefixWord, tailWord_690877, baseEnd_690877] using wordTrace_append hprefix tailTrace_690877
  have hstable : (prefixWord ++ tailWord_690877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690877).length < 2 ^ (prefixWord ++ tailWord_690877).sum := by decide
  have hdescent : baseEnd_690877 < baseStart_690877 := by decide
  rcases family_descends (prefixWord ++ tailWord_690877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690888 : List Nat := [2, 1, 3, 1, 2, 4, 7]
def baseStart_690888 : Nat := 118140960795 + 690888 * 2 ^ 59
def prefixEnd_690888 : Nat := 4983230072969 + 3 ^ 40 * 690888 * 2
def baseEnd_690888 : Nat := 35037789868997346293597

theorem tailTrace_690888 : CollatzResearch.WordTrace tailWord_690888 prefixEnd_690888 35037789868997346293597 := by
  unfold tailWord_690888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599377760519122560752659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16799170347358830081003545 12599377760519122560752659)
  ·
    refine ⟨18899066640778683841128989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12599377760519122560752659 18899066640778683841128989)
    ·
      refine ⟨7087149990292006440423371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18899066640778683841128989 7087149990292006440423371)
      ·
        refine ⟨10630724985438009660635057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087149990292006440423371 10630724985438009660635057)
        ·
          refine ⟨7973043739078507245476293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10630724985438009660635057 7973043739078507245476293)
          ·
            refine ⟨1494945701077220108526805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7973043739078507245476293 1494945701077220108526805)
            ·
              refine ⟨35037789868997346293597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1494945701077220108526805 35037789868997346293597)
              ·
                rfl

theorem cell20_690888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 7].length) (baseStart_690888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690888 prefixEnd_690888 := by exact prefixLift 690888
  have htrace : WordTrace (prefixWord ++ tailWord_690888) baseStart_690888 baseEnd_690888 := by
    simpa [prefixWord, tailWord_690888, baseEnd_690888] using wordTrace_append hprefix tailTrace_690888
  have hstable : (prefixWord ++ tailWord_690888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690888).length < 2 ^ (prefixWord ++ tailWord_690888).sum := by decide
  have hdescent : baseEnd_690888 < baseStart_690888 := by decide
  rcases family_descends (prefixWord ++ tailWord_690888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690967 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 3]
def baseStart_690967 : Nat := 118140960795 + 690967 * 2 ^ 59
def prefixEnd_690967 : Nat := 4983230072969 + 3 ^ 40 * 690967 * 2
def baseEnd_690967 : Nat := 315376166573602953008717

theorem tailTrace_690967 : CollatzResearch.WordTrace tailWord_690967 prefixEnd_690967 315376166573602953008717 := by
  unfold tailWord_690967
  simp only [CollatzResearch.WordTrace]
  refine ⟨25201636887752041613631155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16801091258501361075754103 25201636887752041613631155)
  ·
    refine ⟨37802455331628062420446733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25201636887752041613631155 37802455331628062420446733)
    ·
      refine ⟨14175920749360523407667525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37802455331628062420446733 14175920749360523407667525)
      ·
        refine ⟨2657985140505098138937661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14175920749360523407667525 2657985140505098138937661)
        ·
          refine ⟨996744427689411802101623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2657985140505098138937661 996744427689411802101623)
          ·
            refine ⟨1495116641534117703152435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996744427689411802101623 1495116641534117703152435)
            ·
              refine ⟨2242674962301176554728653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495116641534117703152435 2242674962301176554728653)
              ·
                refine ⟨841003110862941208023245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2242674962301176554728653 841003110862941208023245)
                ·
                  refine ⟨315376166573602953008717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841003110862941208023245 315376166573602953008717)
                  ·
                    rfl

theorem cell20_690967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_690967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690967 prefixEnd_690967 := by exact prefixLift 690967
  have htrace : WordTrace (prefixWord ++ tailWord_690967) baseStart_690967 baseEnd_690967 := by
    simpa [prefixWord, tailWord_690967, baseEnd_690967] using wordTrace_append hprefix tailTrace_690967
  have hstable : (prefixWord ++ tailWord_690967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690967).length < 2 ^ (prefixWord ++ tailWord_690967).sum := by decide
  have hdescent : baseEnd_690967 < baseStart_690967 := by decide
  rcases family_descends (prefixWord ++ tailWord_690967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690998 : List Nat := [5, 1, 2, 2, 3, 7]
def baseStart_690998 : Nat := 118140960795 + 690998 * 2 ^ 59
def prefixEnd_690998 : Nat := 4983230072969 + 3 ^ 40 * 690998 * 2
def baseEnd_690998 : Nat := 11681122808085356406491

theorem tailTrace_690998 : CollatzResearch.WordTrace tailWord_690998 prefixEnd_690998 11681122808085356406491 := by
  unfold tailWord_690998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575172971914983369250603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16801845033759822605339765 1575172971914983369250603)
  ·
    refine ⟨2362759457872475053875905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1575172971914983369250603 2362759457872475053875905)
    ·
      refine ⟨1772069593404356290406929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2362759457872475053875905 1772069593404356290406929)
      ·
        refine ⟨1329052195053267217805197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1772069593404356290406929 1329052195053267217805197)
        ·
          refine ⟨498394573144975206676949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1329052195053267217805197 498394573144975206676949)
          ·
            refine ⟨11681122808085356406491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 498394573144975206676949 11681122808085356406491)
            ·
              rfl

theorem cell20_690998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 7].length) (baseStart_690998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_690998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_690998 prefixEnd_690998 := by exact prefixLift 690998
  have htrace : WordTrace (prefixWord ++ tailWord_690998) baseStart_690998 baseEnd_690998 := by
    simpa [prefixWord, tailWord_690998, baseEnd_690998] using wordTrace_append hprefix tailTrace_690998
  have hstable : (prefixWord ++ tailWord_690998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690998).length < 2 ^ (prefixWord ++ tailWord_690998).sum := by decide
  have hdescent : baseEnd_690998 < baseStart_690998 := by decide
  rcases family_descends (prefixWord ++ tailWord_690998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691002 : List Nat := [3, 1, 1, 1, 6, 8]
def baseStart_691002 : Nat := 118140960795 + 691002 * 2 ^ 59
def prefixEnd_691002 : Nat := 4983230072969 + 3 ^ 40 * 691002 * 2
def baseEnd_691002 : Nat := 11681190426936977290441

theorem tailTrace_691002 : CollatzResearch.WordTrace tailWord_691002 prefixEnd_691002 11681190426936977290441 := by
  unfold tailWord_691002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6300728360656310647788815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16801942295083495060770173 6300728360656310647788815)
  ·
    refine ⟨9451092540984465971683223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6300728360656310647788815 9451092540984465971683223)
    ·
      refine ⟨14176638811476698957524835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9451092540984465971683223 14176638811476698957524835)
      ·
        refine ⟨21264958217215048436287253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14176638811476698957524835 21264958217215048436287253)
        ·
          refine ⟨996794916431955395450965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21264958217215048436287253 996794916431955395450965)
          ·
            refine ⟨11681190426936977290441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 996794916431955395450965 11681190426936977290441)
            ·
              rfl

theorem cell20_691002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 8].length) (baseStart_691002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691002 prefixEnd_691002 := by exact prefixLift 691002
  have htrace : WordTrace (prefixWord ++ tailWord_691002) baseStart_691002 baseEnd_691002 := by
    simpa [prefixWord, tailWord_691002, baseEnd_691002] using wordTrace_append hprefix tailTrace_691002
  have hstable : (prefixWord ++ tailWord_691002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691002).length < 2 ^ (prefixWord ++ tailWord_691002).sum := by decide
  have hdescent : baseEnd_691002 < baseStart_691002 := by decide
  rcases family_descends (prefixWord ++ tailWord_691002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691026 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_691026 : Nat := 118140960795 + 691026 * 2 ^ 59
def prefixEnd_691026 : Nat := 4983230072969 + 3 ^ 40 * 691026 * 2
def baseEnd_691026 : Nat := 315403095781260970041809

theorem tailTrace_691026 : CollatzResearch.WordTrace tailWord_691026 prefixEnd_691026 315403095781260970041809 := by
  unfold tailWord_691026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6300947198634573672507233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16802525863025529793352621 6300947198634573672507233)
  ·
    refine ⟨4725710398975930254380425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6300947198634573672507233 4725710398975930254380425)
    ·
      refine ⟨3544282799231947690785319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4725710398975930254380425 3544282799231947690785319)
      ·
        refine ⟨5316424198847921536177979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3544282799231947690785319 5316424198847921536177979)
        ·
          refine ⟨7974636298271882304266969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316424198847921536177979 7974636298271882304266969)
          ·
            refine ⟨5980977223703911728200227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7974636298271882304266969 5980977223703911728200227)
            ·
              refine ⟨8971465835555867592300341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980977223703911728200227 8971465835555867592300341)
              ·
                refine ⟨841074922083362586778157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8971465835555867592300341 841074922083362586778157)
                ·
                  refine ⟨315403095781260970041809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841074922083362586778157 315403095781260970041809)
                  ·
                    rfl

theorem cell20_691026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_691026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691026 prefixEnd_691026 := by exact prefixLift 691026
  have htrace : WordTrace (prefixWord ++ tailWord_691026) baseStart_691026 baseEnd_691026 := by
    simpa [prefixWord, tailWord_691026, baseEnd_691026] using wordTrace_append hprefix tailTrace_691026
  have hstable : (prefixWord ++ tailWord_691026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691026).length < 2 ^ (prefixWord ++ tailWord_691026).sum := by decide
  have hdescent : baseEnd_691026 < baseStart_691026 := by decide
  rcases family_descends (prefixWord ++ tailWord_691026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691033 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_691033 : Nat := 118140960795 + 691033 * 2 ^ 59
def prefixEnd_691033 : Nat := 4983230072969 + 3 ^ 40 * 691033 * 2
def baseEnd_691033 : Nat := 315406290772000056808447

theorem tailTrace_691033 : CollatzResearch.WordTrace tailWord_691033 prefixEnd_691033 315406290772000056808447 := by
  unfold tailWord_691033
  simp only [CollatzResearch.WordTrace]
  refine ⟨25204044105512934885533753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16802696070341956590355835 25204044105512934885533753)
  ·
    refine ⟨18903033079134701164150315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25204044105512934885533753 18903033079134701164150315)
    ·
      refine ⟨28354549618702051746225473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18903033079134701164150315 28354549618702051746225473)
      ·
        refine ⟨21265912214026538809669105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28354549618702051746225473 21265912214026538809669105)
        ·
          refine ⟨15949434160519904107251829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21265912214026538809669105 15949434160519904107251829)
          ·
            refine ⟨1495259452548741010054859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15949434160519904107251829 1495259452548741010054859)
            ·
              refine ⟨2242889178823111515082289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495259452548741010054859 2242889178823111515082289)
              ·
                refine ⟨1682166884117333636311717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242889178823111515082289 1682166884117333636311717)
                ·
                  refine ⟨315406290772000056808447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682166884117333636311717 315406290772000056808447)
                  ·
                    rfl

theorem cell20_691033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_691033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691033 prefixEnd_691033 := by exact prefixLift 691033
  have htrace : WordTrace (prefixWord ++ tailWord_691033) baseStart_691033 baseEnd_691033 := by
    simpa [prefixWord, tailWord_691033, baseEnd_691033] using wordTrace_append hprefix tailTrace_691033
  have hstable : (prefixWord ++ tailWord_691033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691033).length < 2 ^ (prefixWord ++ tailWord_691033).sum := by decide
  have hdescent : baseEnd_691033 < baseStart_691033 := by decide
  rcases family_descends (prefixWord ++ tailWord_691033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691036 : List Nat := [2, 2, 4, 2, 1, 2, 3, 4]
def baseStart_691036 : Nat := 118140960795 + 691036 * 2 ^ 59
def prefixEnd_691036 : Nat := 4983230072969 + 3 ^ 40 * 691036 * 2
def baseEnd_691036 : Nat := 105135886684581793236145

theorem tailTrace_691036 : CollatzResearch.WordTrace tailWord_691036 prefixEnd_691036 105135886684581793236145 := by
  unfold tailWord_691036
  simp only [CollatzResearch.WordTrace]
  refine ⟨12602076762251033198946481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16802769016334710931928641 12602076762251033198946481)
  ·
    refine ⟨9451557571688274899209861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12602076762251033198946481 9451557571688274899209861)
    ·
      refine ⟨1772167044691551543601849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9451557571688274899209861 1772167044691551543601849)
      ·
        refine ⟨1329125283518663657701387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1772167044691551543601849 1329125283518663657701387)
        ·
          refine ⟨1993687925277995486552081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329125283518663657701387 1993687925277995486552081)
          ·
            refine ⟨1495265943958496614914061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993687925277995486552081 1495265943958496614914061)
            ·
              refine ⟨560724728984436230592773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1495265943958496614914061 560724728984436230592773)
              ·
                refine ⟨105135886684581793236145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560724728984436230592773 105135886684581793236145)
                ·
                  rfl

theorem cell20_691036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_691036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691036 prefixEnd_691036 := by exact prefixLift 691036
  have htrace : WordTrace (prefixWord ++ tailWord_691036) baseStart_691036 baseEnd_691036 := by
    simpa [prefixWord, tailWord_691036, baseEnd_691036] using wordTrace_append hprefix tailTrace_691036
  have hstable : (prefixWord ++ tailWord_691036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691036).length < 2 ^ (prefixWord ++ tailWord_691036).sum := by decide
  have hdescent : baseEnd_691036 < baseStart_691036 := by decide
  rcases family_descends (prefixWord ++ tailWord_691036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691081 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 3]
def baseStart_691081 : Nat := 118140960795 + 691081 * 2 ^ 59
def prefixEnd_691081 : Nat := 4983230072969 + 3 ^ 40 * 691081 * 2
def baseEnd_691081 : Nat := 315428199279925223208251

theorem tailTrace_691081 : CollatzResearch.WordTrace tailWord_691081 prefixEnd_691081 315428199279925223208251 := by
  unfold tailWord_691081
  simp only [CollatzResearch.WordTrace]
  refine ⟨25205794809339039083281097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16803863206226026055520731 25205794809339039083281097)
  ·
    refine ⟨18904346107004279312460823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25205794809339039083281097 18904346107004279312460823)
    ·
      refine ⟨28356519160506418968691235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18904346107004279312460823 28356519160506418968691235)
      ·
        refine ⟨42534778740759628453036853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28356519160506418968691235 42534778740759628453036853)
        ·
          refine ⟨3987635506946215167472205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42534778740759628453036853 3987635506946215167472205)
          ·
            refine ⟨1495363315104830687802077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3987635506946215167472205 1495363315104830687802077)
            ·
              refine ⟨560761243164311507925779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1495363315104830687802077 560761243164311507925779)
              ·
                refine ⟨841141864746467261888669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560761243164311507925779 841141864746467261888669)
                ·
                  refine ⟨315428199279925223208251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841141864746467261888669 315428199279925223208251)
                  ·
                    rfl

theorem cell20_691081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_691081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691081 prefixEnd_691081 := by exact prefixLift 691081
  have htrace : WordTrace (prefixWord ++ tailWord_691081) baseStart_691081 baseEnd_691081 := by
    simpa [prefixWord, tailWord_691081, baseEnd_691081] using wordTrace_append hprefix tailTrace_691081
  have hstable : (prefixWord ++ tailWord_691081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691081).length < 2 ^ (prefixWord ++ tailWord_691081).sum := by decide
  have hdescent : baseEnd_691081 < baseStart_691081 := by decide
  rcases family_descends (prefixWord ++ tailWord_691081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691105 : List Nat := [1, 2, 3, 4, 1, 1, 3, 3, 2]
def baseStart_691105 : Nat := 118140960795 + 691105 * 2 ^ 59
def prefixEnd_691105 : Nat := 4983230072969 + 3 ^ 40 * 691105 * 2
def baseEnd_691105 : Nat := 315439153533887806408153

theorem tailTrace_691105 : CollatzResearch.WordTrace tailWord_691105 prefixEnd_691105 315439153533887806408153 := by
  unfold tailWord_691105
  simp only [CollatzResearch.WordTrace]
  refine ⟨25206670161252091182154769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16804446774168060788103179 25206670161252091182154769)
  ·
    refine ⟨18905002620939068386616077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25206670161252091182154769 18905002620939068386616077)
    ·
      refine ⟨7089375982852150644981029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18905002620939068386616077 7089375982852150644981029)
      ·
        refine ⟨1329257996784778245933943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7089375982852150644981029 1329257996784778245933943)
        ·
          refine ⟨1993886995177167368900915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329257996784778245933943 1993886995177167368900915)
          ·
            refine ⟨2990830492765751053351373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993886995177167368900915 2990830492765751053351373)
            ·
              refine ⟨1121561434787156645006765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2990830492765751053351373 1121561434787156645006765)
              ·
                refine ⟨420585538045183741877537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1121561434787156645006765 420585538045183741877537)
                ·
                  refine ⟨315439153533887806408153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420585538045183741877537 315439153533887806408153)
                  ·
                    rfl

theorem cell20_691105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_691105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691105 prefixEnd_691105 := by exact prefixLift 691105
  have htrace : WordTrace (prefixWord ++ tailWord_691105) baseStart_691105 baseEnd_691105 := by
    simpa [prefixWord, tailWord_691105, baseEnd_691105] using wordTrace_append hprefix tailTrace_691105
  have hstable : (prefixWord ++ tailWord_691105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691105).length < 2 ^ (prefixWord ++ tailWord_691105).sum := by decide
  have hdescent : baseEnd_691105 < baseStart_691105 := by decide
  rcases family_descends (prefixWord ++ tailWord_691105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691133 : List Nat := [1, 4, 1, 2, 4, 1, 2, 5]
def baseStart_691133 : Nat := 118140960795 + 691133 * 2 ^ 59
def prefixEnd_691133 : Nat := 4983230072969 + 3 ^ 40 * 691133 * 2
def baseEnd_691133 : Nat := 105150644498948051158235

theorem tailTrace_691133 : CollatzResearch.WordTrace tailWord_691133 prefixEnd_691133 105150644498948051158235 := by
  unfold tailWord_691133
  simp only [CollatzResearch.WordTrace]
  refine ⟨25207691405150651964174053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16805127603433767976116035 25207691405150651964174053)
  ·
    refine ⟨4726442138465747243282635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25207691405150651964174053 4726442138465747243282635)
    ·
      refine ⟨7089663207698620864923953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726442138465747243282635 7089663207698620864923953)
      ·
        refine ⟨5317247405773965648692965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7089663207698620864923953 5317247405773965648692965)
        ·
          refine ⟨996983888582618559129931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5317247405773965648692965 996983888582618559129931)
          ·
            refine ⟨1495475832873927838694897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996983888582618559129931 1495475832873927838694897)
            ·
              refine ⟨1121606874655445879021173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495475832873927838694897 1121606874655445879021173)
              ·
                refine ⟨105150644498948051158235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1121606874655445879021173 105150644498948051158235)
                ·
                  rfl

theorem cell20_691133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_691133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691133 prefixEnd_691133 := by exact prefixLift 691133
  have htrace : WordTrace (prefixWord ++ tailWord_691133) baseStart_691133 baseEnd_691133 := by
    simpa [prefixWord, tailWord_691133, baseEnd_691133] using wordTrace_append hprefix tailTrace_691133
  have hstable : (prefixWord ++ tailWord_691133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691133).length < 2 ^ (prefixWord ++ tailWord_691133).sum := by decide
  have hdescent : baseEnd_691133 < baseStart_691133 := by decide
  rcases family_descends (prefixWord ++ tailWord_691133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691178 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_691178 : Nat := 118140960795 + 691178 * 2 ^ 59
def prefixEnd_691178 : Nat := 4983230072969 + 3 ^ 40 * 691178 * 2
def baseEnd_691178 : Nat := 315472472723023996974521

theorem tailTrace_691178 : CollatzResearch.WordTrace tailWord_691178 prefixEnd_691178 315472472723023996974521 := by
  unfold tailWord_691178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302333172496906162390547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16806221793325083099708125 6302333172496906162390547)
  ·
    refine ⟨9453499758745359243585821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6302333172496906162390547 9453499758745359243585821)
    ·
      refine ⟨3545062409529509716344683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9453499758745359243585821 3545062409529509716344683)
      ·
        refine ⟨5317593614294264574517025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545062409529509716344683 5317593614294264574517025)
        ·
          refine ⟨3988195210720698430887769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5317593614294264574517025 3988195210720698430887769)
          ·
            refine ⟨2991146408040523823165827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3988195210720698430887769 2991146408040523823165827)
            ·
              refine ⟨4486719612060785734748741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991146408040523823165827 4486719612060785734748741)
              ·
                refine ⟨841259927261397325265389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4486719612060785734748741 841259927261397325265389)
                ·
                  refine ⟨315472472723023996974521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841259927261397325265389 315472472723023996974521)
                  ·
                    rfl

theorem cell20_691178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_691178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691178 prefixEnd_691178 := by exact prefixLift 691178
  have htrace : WordTrace (prefixWord ++ tailWord_691178) baseStart_691178 baseEnd_691178 := by
    simpa [prefixWord, tailWord_691178, baseEnd_691178] using wordTrace_append hprefix tailTrace_691178
  have hstable : (prefixWord ++ tailWord_691178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691178).length < 2 ^ (prefixWord ++ tailWord_691178).sum := by decide
  have hdescent : baseEnd_691178 < baseStart_691178 := by decide
  rcases family_descends (prefixWord ++ tailWord_691178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691233 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 3]
def baseStart_691233 : Nat := 118140960795 + 691233 * 2 ^ 59
def prefixEnd_691233 : Nat := 4983230072969 + 3 ^ 40 * 691233 * 2
def baseEnd_691233 : Nat := 315497576221688250140963

theorem tailTrace_691233 : CollatzResearch.WordTrace tailWord_691233 prefixEnd_691233 315497576221688250140963 := by
  unfold tailWord_691233
  simp only [CollatzResearch.WordTrace]
  refine ⟨25211338704788369042814353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16807559136525579361876235 25211338704788369042814353)
  ·
    refine ⟨18908504028591276782110765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25211338704788369042814353 18908504028591276782110765)
    ·
      refine ⟨7090689010721728793291537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18908504028591276782110765 7090689010721728793291537)
      ·
        refine ⟨5318016758041296594968653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7090689010721728793291537 5318016758041296594968653)
        ·
          refine ⟨1994256284265486223113245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5318016758041296594968653 1994256284265486223113245)
          ·
            refine ⟨747846106599557333667467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1994256284265486223113245 747846106599557333667467)
            ·
              refine ⟨1121769159899336000501201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747846106599557333667467 1121769159899336000501201)
              ·
                refine ⟨841326869924502000375901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121769159899336000501201 841326869924502000375901)
                ·
                  refine ⟨315497576221688250140963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841326869924502000375901 315497576221688250140963)
                  ·
                    rfl

theorem cell20_691233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_691233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691233 prefixEnd_691233 := by exact prefixLift 691233
  have htrace : WordTrace (prefixWord ++ tailWord_691233) baseStart_691233 baseEnd_691233 := by
    simpa [prefixWord, tailWord_691233, baseEnd_691233] using wordTrace_append hprefix tailTrace_691233
  have hstable : (prefixWord ++ tailWord_691233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691233).length < 2 ^ (prefixWord ++ tailWord_691233).sum := by decide
  have hdescent : baseEnd_691233 < baseStart_691233 := by decide
  rcases family_descends (prefixWord ++ tailWord_691233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691237 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_691237 : Nat := 118140960795 + 691237 * 2 ^ 59
def prefixEnd_691237 : Nat := 4983230072969 + 3 ^ 40 * 691237 * 2
def baseEnd_691237 : Nat := 315499401930682014007613

theorem tailTrace_691237 : CollatzResearch.WordTrace tailWord_691237 prefixEnd_691237 315499401930682014007613 := by
  unfold tailWord_691237
  simp only [CollatzResearch.WordTrace]
  refine ⟨25211484596773877725959965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16807656397849251817306643 25211484596773877725959965)
  ·
    refine ⟨9454306723790204147234987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25211484596773877725959965 9454306723790204147234987)
    ·
      refine ⟨14181460085685306220852481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9454306723790204147234987 14181460085685306220852481)
      ·
        refine ⟨10636095064263979665639361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14181460085685306220852481 10636095064263979665639361)
        ·
          refine ⟨7977071298197984749229521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10636095064263979665639361 7977071298197984749229521)
          ·
            refine ⟨5982803473648488561922141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7977071298197984749229521 5982803473648488561922141)
            ·
              refine ⟨2243551302618183210720803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5982803473648488561922141 2243551302618183210720803)
              ·
                refine ⟨3365326953927274816081205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243551302618183210720803 3365326953927274816081205)
                ·
                  refine ⟨315499401930682014007613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3365326953927274816081205 315499401930682014007613)
                  ·
                    rfl

theorem cell20_691237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_691237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691237 prefixEnd_691237 := by exact prefixLift 691237
  have htrace : WordTrace (prefixWord ++ tailWord_691237) baseStart_691237 baseEnd_691237 := by
    simpa [prefixWord, tailWord_691237, baseEnd_691237] using wordTrace_append hprefix tailTrace_691237
  have hstable : (prefixWord ++ tailWord_691237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691237).length < 2 ^ (prefixWord ++ tailWord_691237).sum := by decide
  have hdescent : baseEnd_691237 < baseStart_691237 := by decide
  rcases family_descends (prefixWord ++ tailWord_691237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691251 : List Nat := [1, 1, 1, 2, 4, 1, 1, 9]
def baseStart_691251 : Nat := 118140960795 + 691251 * 2 ^ 59
def prefixEnd_691251 : Nat := 4983230072969 + 3 ^ 40 * 691251 * 2
def baseEnd_691251 : Nat := 105168597304053395846963

theorem tailTrace_691251 : CollatzResearch.WordTrace tailWord_691251 prefixEnd_691251 105168597304053395846963 := by
  unfold tailWord_691251
  simp only [CollatzResearch.WordTrace]
  refine ⟨25211995218723158116969607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16807996812482105411313071 25211995218723158116969607)
  ·
    refine ⟨37817992828084737175454411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25211995218723158116969607 37817992828084737175454411)
    ·
      refine ⟨56726989242127105763181617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37817992828084737175454411 56726989242127105763181617)
      ·
        refine ⟨42545241931595329322386213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56726989242127105763181617 42545241931595329322386213)
        ·
          refine ⟨7977232862174124247947415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42545241931595329322386213 7977232862174124247947415)
          ·
            refine ⟨11965849293261186371921123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7977232862174124247947415 11965849293261186371921123)
            ·
              refine ⟨17948773939891779557881685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11965849293261186371921123 17948773939891779557881685)
              ·
                refine ⟨105168597304053395846963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17948773939891779557881685 105168597304053395846963)
                ·
                  rfl

theorem cell20_691251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_691251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691251 prefixEnd_691251 := by exact prefixLift 691251
  have htrace : WordTrace (prefixWord ++ tailWord_691251) baseStart_691251 baseEnd_691251 := by
    simpa [prefixWord, tailWord_691251, baseEnd_691251] using wordTrace_append hprefix tailTrace_691251
  have hstable : (prefixWord ++ tailWord_691251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691251).length < 2 ^ (prefixWord ++ tailWord_691251).sum := by decide
  have hdescent : baseEnd_691251 < baseStart_691251 := by decide
  rcases family_descends (prefixWord ++ tailWord_691251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691261 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_691261 : Nat := 118140960795 + 691261 * 2 ^ 59
def prefixEnd_691261 : Nat := 4983230072969 + 3 ^ 40 * 691261 * 2
def baseEnd_691261 : Nat := 315510356184644597207515

theorem tailTrace_691261 : CollatzResearch.WordTrace tailWord_691261 prefixEnd_691261 315510356184644597207515 := by
  unfold tailWord_691261
  simp only [CollatzResearch.WordTrace]
  refine ⟨25212359948686929824833637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16808239965791286549889091 25212359948686929824833637)
  ·
    refine ⟨4727317490378799342156307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25212359948686929824833637 4727317490378799342156307)
    ·
      refine ⟨7090976235568199013234461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4727317490378799342156307 7090976235568199013234461)
      ·
        refine ⟨2659116088338074629962923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7090976235568199013234461 2659116088338074629962923)
        ·
          refine ⟨3988674132507111944944385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659116088338074629962923 3988674132507111944944385)
          ·
            refine ⟨2991505599380333958708289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3988674132507111944944385 2991505599380333958708289)
            ·
              refine ⟨2243629199535250469031217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2991505599380333958708289 2243629199535250469031217)
              ·
                refine ⟨1682721899651437851773413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2243629199535250469031217 1682721899651437851773413)
                ·
                  refine ⟨315510356184644597207515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682721899651437851773413 315510356184644597207515)
                  ·
                    rfl

theorem cell20_691261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_691261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691261 prefixEnd_691261 := by exact prefixLift 691261
  have htrace : WordTrace (prefixWord ++ tailWord_691261) baseStart_691261 baseEnd_691261 := by
    simpa [prefixWord, tailWord_691261, baseEnd_691261] using wordTrace_append hprefix tailTrace_691261
  have hstable : (prefixWord ++ tailWord_691261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691261).length < 2 ^ (prefixWord ++ tailWord_691261).sum := by decide
  have hdescent : baseEnd_691261 < baseStart_691261 := by decide
  rcases family_descends (prefixWord ++ tailWord_691261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691292 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_691292 : Nat := 118140960795 + 691292 * 2 ^ 59
def prefixEnd_691292 : Nat := 4983230072969 + 3 ^ 40 * 691292 * 2
def baseEnd_691292 : Nat := 315524505429346267174055

theorem tailTrace_691292 : CollatzResearch.WordTrace tailWord_691292 prefixEnd_691292 315524505429346267174055 := by
  unfold tailWord_691292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12606745305787311059606065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16808993741049748079474753 12606745305787311059606065)
  ·
    refine ⟨9455058979340483294704549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12606745305787311059606065 9455058979340483294704549)
    ·
      refine ⟨1772823558626340617757103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9455058979340483294704549 1772823558626340617757103)
      ·
        refine ⟨2659235337939510926635655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772823558626340617757103 2659235337939510926635655)
        ·
          refine ⟨3988853006909266389953483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659235337939510926635655 3988853006909266389953483)
          ·
            refine ⟨5983279510363899584930225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988853006909266389953483 5983279510363899584930225)
            ·
              refine ⟨4487459632772924688697669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983279510363899584930225 4487459632772924688697669)
              ·
                refine ⟨841398681144923379130813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4487459632772924688697669 841398681144923379130813)
                ·
                  refine ⟨315524505429346267174055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841398681144923379130813 315524505429346267174055)
                  ·
                    rfl

theorem cell20_691292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_691292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691292 prefixEnd_691292 := by exact prefixLift 691292
  have htrace : WordTrace (prefixWord ++ tailWord_691292) baseStart_691292 baseEnd_691292 := by
    simpa [prefixWord, tailWord_691292, baseEnd_691292] using wordTrace_append hprefix tailTrace_691292
  have hstable : (prefixWord ++ tailWord_691292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691292).length < 2 ^ (prefixWord ++ tailWord_691292).sum := by decide
  have hdescent : baseEnd_691292 < baseStart_691292 := by decide
  rcases family_descends (prefixWord ++ tailWord_691292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691306 : List Nat := [3, 1, 3, 2, 2, 1, 1, 7]
def baseStart_691306 : Nat := 118140960795 + 691306 * 2 ^ 59
def prefixEnd_691306 : Nat := 4983230072969 + 3 ^ 40 * 691306 * 2
def baseEnd_691306 : Nat := 105176965136941480235777

theorem tailTrace_691306 : CollatzResearch.WordTrace tailWord_691306 prefixEnd_691306 105176965136941480235777 := by
  unfold tailWord_691306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6303500308380975627555443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16809334155682601673481181 6303500308380975627555443)
  ·
    refine ⟨9455250462571463441333165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6303500308380975627555443 9455250462571463441333165)
    ·
      refine ⟨3545718923464298790499937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9455250462571463441333165 3545718923464298790499937)
      ·
        refine ⟨2659289192598224092874953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3545718923464298790499937 2659289192598224092874953)
        ·
          refine ⟨1994466894448668069656215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2659289192598224092874953 1994466894448668069656215)
          ·
            refine ⟨2991700341673002104484323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994466894448668069656215 2991700341673002104484323)
            ·
              refine ⟨4487550512509503156726485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991700341673002104484323 4487550512509503156726485)
              ·
                refine ⟨105176965136941480235777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4487550512509503156726485 105176965136941480235777)
                ·
                  rfl

theorem cell20_691306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_691306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691306 prefixEnd_691306 := by exact prefixLift 691306
  have htrace : WordTrace (prefixWord ++ tailWord_691306) baseStart_691306 baseEnd_691306 := by
    simpa [prefixWord, tailWord_691306, baseEnd_691306] using wordTrace_append hprefix tailTrace_691306
  have hstable : (prefixWord ++ tailWord_691306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691306).length < 2 ^ (prefixWord ++ tailWord_691306).sum := by decide
  have hdescent : baseEnd_691306 < baseStart_691306 := by decide
  rcases family_descends (prefixWord ++ tailWord_691306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691309 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 3]
def baseStart_691309 : Nat := 118140960795 + 691309 * 2 ^ 59
def prefixEnd_691309 : Nat := 4983230072969 + 3 ^ 40 * 691309 * 2
def baseEnd_691309 : Nat := 315532264692569763607319

theorem tailTrace_691309 : CollatzResearch.WordTrace tailWord_691309 prefixEnd_691309 315532264692569763607319 := by
  unfold tailWord_691309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25214110652513034022580981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16809407101675356015053987 25214110652513034022580981)
  ·
    refine ⟨2363822873673096939616967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25214110652513034022580981 2363822873673096939616967)
    ·
      refine ⟨3545734310509645409425451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363822873673096939616967 3545734310509645409425451)
      ·
        refine ⟨5318601465764468114138177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545734310509645409425451 5318601465764468114138177)
        ·
          refine ⟨3988951099323351085603633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5318601465764468114138177 3988951099323351085603633)
          ·
            refine ⟨2991713324492513314202725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3988951099323351085603633 2991713324492513314202725)
            ·
              refine ⟨560946248342346246413011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2991713324492513314202725 560946248342346246413011)
              ·
                refine ⟨841419372513519369619517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560946248342346246413011 841419372513519369619517)
                ·
                  refine ⟨315532264692569763607319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841419372513519369619517 315532264692569763607319)
                  ·
                    rfl

theorem cell20_691309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_691309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691309 prefixEnd_691309 := by exact prefixLift 691309
  have htrace : WordTrace (prefixWord ++ tailWord_691309) baseStart_691309 baseEnd_691309 := by
    simpa [prefixWord, tailWord_691309, baseEnd_691309] using wordTrace_append hprefix tailTrace_691309
  have hstable : (prefixWord ++ tailWord_691309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691309).length < 2 ^ (prefixWord ++ tailWord_691309).sum := by decide
  have hdescent : baseEnd_691309 < baseStart_691309 := by decide
  rcases family_descends (prefixWord ++ tailWord_691309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691320 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_691320 : Nat := 118140960795 + 691320 * 2 ^ 59
def prefixEnd_691320 : Nat := 4983230072969 + 3 ^ 40 * 691320 * 2
def baseEnd_691320 : Nat := 315537285392302614240607

theorem tailTrace_691320 : CollatzResearch.WordTrace tailWord_691320 prefixEnd_691320 315537285392302614240607 := by
  unfold tailWord_691320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12607255927736591450615707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16809674570315455267487609 12607255927736591450615707)
  ·
    refine ⟨18910883891604887175923561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12607255927736591450615707 18910883891604887175923561)
    ·
      refine ⟨14183162918703665381942671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18910883891604887175923561 14183162918703665381942671)
      ·
        refine ⟨21274744378055498072914007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14183162918703665381942671 21274744378055498072914007)
        ·
          refine ⟨31912116567083247109371011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21274744378055498072914007 31912116567083247109371011)
          ·
            refine ⟨47868174850624870664056517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31912116567083247109371011 47868174850624870664056517)
            ·
              refine ⟨8975282784492163249510597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47868174850624870664056517 8975282784492163249510597)
              ·
                refine ⟨1682865522092280609283237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8975282784492163249510597 1682865522092280609283237)
                ·
                  refine ⟨315537285392302614240607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682865522092280609283237 315537285392302614240607)
                  ·
                    rfl

theorem cell20_691320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_691320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691320 prefixEnd_691320 := by exact prefixLift 691320
  have htrace : WordTrace (prefixWord ++ tailWord_691320) baseStart_691320 baseEnd_691320 := by
    simpa [prefixWord, tailWord_691320, baseEnd_691320] using wordTrace_append hprefix tailTrace_691320
  have hstable : (prefixWord ++ tailWord_691320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691320).length < 2 ^ (prefixWord ++ tailWord_691320).sum := by decide
  have hdescent : baseEnd_691320 < baseStart_691320 := by decide
  rcases family_descends (prefixWord ++ tailWord_691320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691398 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_691398 : Nat := 118140960795 + 691398 * 2 ^ 59
def prefixEnd_691398 : Nat := 4983230072969 + 3 ^ 40 * 691398 * 2
def baseEnd_691398 : Nat := 315572886717681009640289

theorem tailTrace_691398 : CollatzResearch.WordTrace tailWord_691398 prefixEnd_691398 315572886717681009640289 := by
  unfold tailWord_691398
  simp only [CollatzResearch.WordTrace]
  refine ⟨788042398412206319455339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16811571166127068148380565 788042398412206319455339)
  ·
    refine ⟨1182063597618309479183009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 788042398412206319455339 1182063597618309479183009)
    ·
      refine ⟨886547698213732109387257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1182063597618309479183009 886547698213732109387257)
      ·
        refine ⟨664910773660299082040443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 886547698213732109387257 664910773660299082040443)
        ·
          refine ⟨997366160490448623060665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664910773660299082040443 997366160490448623060665)
          ·
            refine ⟨748024620367836467295499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997366160490448623060665 748024620367836467295499)
            ·
              refine ⟨1122036930551754700943249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748024620367836467295499 1122036930551754700943249)
              ·
                refine ⟨841527697913816025707437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122036930551754700943249 841527697913816025707437)
                ·
                  refine ⟨315572886717681009640289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841527697913816025707437 315572886717681009640289)
                  ·
                    rfl

theorem cell20_691398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_691398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691398 prefixEnd_691398 := by exact prefixLift 691398
  have htrace : WordTrace (prefixWord ++ tailWord_691398) baseStart_691398 baseEnd_691398 := by
    simpa [prefixWord, tailWord_691398, baseEnd_691398] using wordTrace_append hprefix tailTrace_691398
  have hstable : (prefixWord ++ tailWord_691398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691398).length < 2 ^ (prefixWord ++ tailWord_691398).sum := by decide
  have hdescent : baseEnd_691398 < baseStart_691398 := by decide
  rcases family_descends (prefixWord ++ tailWord_691398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691406 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_691406 : Nat := 118140960795 + 691406 * 2 ^ 59
def prefixEnd_691406 : Nat := 4983230072969 + 3 ^ 40 * 691406 * 2
def baseEnd_691406 : Nat := 315576538135668537373589

theorem tailTrace_691406 : CollatzResearch.WordTrace tailWord_691406 prefixEnd_691406 315576538135668537373589 := by
  unfold tailWord_691406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152206066645202448607759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16811765688774413059241381 3152206066645202448607759)
  ·
    refine ⟨4728309099967803672911639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3152206066645202448607759 4728309099967803672911639)
    ·
      refine ⟨7092463649951705509367459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4728309099967803672911639 7092463649951705509367459)
      ·
        refine ⟨10638695474927558264051189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7092463649951705509367459 10638695474927558264051189)
        ·
          refine ⟨997377700774458587254799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10638695474927558264051189 997377700774458587254799)
          ·
            refine ⟨1496066551161687880882199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997377700774458587254799 1496066551161687880882199)
            ·
              refine ⟨2244099826742531821323299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496066551161687880882199 2244099826742531821323299)
              ·
                refine ⟨3366149740113797731984949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244099826742531821323299 3366149740113797731984949)
                ·
                  refine ⟨315576538135668537373589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3366149740113797731984949 315576538135668537373589)
                  ·
                    rfl

theorem cell20_691406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_691406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691406 prefixEnd_691406 := by exact prefixLift 691406
  have htrace : WordTrace (prefixWord ++ tailWord_691406) baseStart_691406 baseEnd_691406 := by
    simpa [prefixWord, tailWord_691406, baseEnd_691406] using wordTrace_append hprefix tailTrace_691406
  have hstable : (prefixWord ++ tailWord_691406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691406).length < 2 ^ (prefixWord ++ tailWord_691406).sum := by decide
  have hdescent : baseEnd_691406 < baseStart_691406 := by decide
  rcases family_descends (prefixWord ++ tailWord_691406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691413 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_691413 : Nat := 118140960795 + 691413 * 2 ^ 59
def prefixEnd_691413 : Nat := 4983230072969 + 3 ^ 40 * 691413 * 2
def baseEnd_691413 : Nat := 315579733126407624140227

theorem tailTrace_691413 : CollatzResearch.WordTrace tailWord_691413 prefixEnd_691413 315579733126407624140227 := by
  unfold tailWord_691413
  simp only [CollatzResearch.WordTrace]
  refine ⟨25217903844136259784366893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16811935896090839856244595 25217903844136259784366893)
  ·
    refine ⟨9456713941551097419137585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25217903844136259784366893 9456713941551097419137585)
    ·
      refine ⟨7092535456163323064353189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9456713941551097419137585 7092535456163323064353189)
      ·
        refine ⟨1329850398030623074566223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7092535456163323064353189 1329850398030623074566223)
        ·
          refine ⟨1994775597045934611849335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329850398030623074566223 1994775597045934611849335)
          ·
            refine ⟨2992163395568901917774003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994775597045934611849335 2992163395568901917774003)
            ·
              refine ⟨4488245093353352876661005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992163395568901917774003 4488245093353352876661005)
              ·
                refine ⟨1683091910007507328747877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4488245093353352876661005 1683091910007507328747877)
                ·
                  refine ⟨315579733126407624140227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683091910007507328747877 315579733126407624140227)
                  ·
                    rfl

theorem cell20_691413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_691413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691413 prefixEnd_691413 := by exact prefixLift 691413
  have htrace : WordTrace (prefixWord ++ tailWord_691413) baseStart_691413 baseEnd_691413 := by
    simpa [prefixWord, tailWord_691413, baseEnd_691413] using wordTrace_append hprefix tailTrace_691413
  have hstable : (prefixWord ++ tailWord_691413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691413).length < 2 ^ (prefixWord ++ tailWord_691413).sum := by decide
  have hdescent : baseEnd_691413 < baseStart_691413 := by decide
  rcases family_descends (prefixWord ++ tailWord_691413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691437 : List Nat := [1, 5, 1, 2, 2, 1, 4, 4]
def baseStart_691437 : Nat := 118140960795 + 691437 * 2 ^ 59
def prefixEnd_691437 : Nat := 4983230072969 + 3 ^ 40 * 691437 * 2
def baseEnd_691437 : Nat := 105196895793456735780043

theorem tailTrace_691437 : CollatzResearch.WordTrace tailWord_691437 prefixEnd_691437 105196895793456735780043 := by
  unfold tailWord_691437
  simp only [CollatzResearch.WordTrace]
  refine ⟨25218779196049311883240565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16812519464032874588827043 25218779196049311883240565)
  ·
    refine ⟨2364260549629622989053803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25218779196049311883240565 2364260549629622989053803)
    ·
      refine ⟨3546390824444434483580705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364260549629622989053803 3546390824444434483580705)
      ·
        refine ⟨2659793118333325862685529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3546390824444434483580705 2659793118333325862685529)
        ·
          refine ⟨1994844838749994397014147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2659793118333325862685529 1994844838749994397014147)
          ·
            refine ⟨2992267258124991595521221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994844838749994397014147 2992267258124991595521221)
            ·
              refine ⟨561050110898435924160229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2992267258124991595521221 561050110898435924160229)
              ·
                refine ⟨105196895793456735780043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561050110898435924160229 105196895793456735780043)
                ·
                  rfl

theorem cell20_691437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_691437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691437 prefixEnd_691437 := by exact prefixLift 691437
  have htrace : WordTrace (prefixWord ++ tailWord_691437) baseStart_691437 baseEnd_691437 := by
    simpa [prefixWord, tailWord_691437, baseEnd_691437] using wordTrace_append hprefix tailTrace_691437
  have hstable : (prefixWord ++ tailWord_691437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691437).length < 2 ^ (prefixWord ++ tailWord_691437).sum := by decide
  have hdescent : baseEnd_691437 < baseStart_691437 := by decide
  rcases family_descends (prefixWord ++ tailWord_691437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691465 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 3]
def baseStart_691465 : Nat := 118140960795 + 691465 * 2 ^ 59
def prefixEnd_691465 : Nat := 4983230072969 + 3 ^ 40 * 691465 * 2
def baseEnd_691465 : Nat := 315603467343326554406681

theorem tailTrace_691465 : CollatzResearch.WordTrace tailWord_691465 prefixEnd_691465 315603467343326554406681 := by
  unfold tailWord_691465
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219800439947872665259849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16813200293298581776839899 25219800439947872665259849)
  ·
    refine ⟨18914850329960904498944887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25219800439947872665259849 18914850329960904498944887)
    ·
      refine ⟨28372275494941356748417331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18914850329960904498944887 28372275494941356748417331)
      ·
        refine ⟨42558413242412035122625997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28372275494941356748417331 42558413242412035122625997)
        ·
          refine ⟨15959404965904513170984749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42558413242412035122625997 15959404965904513170984749)
          ·
            refine ⟨5984776862214192439119281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15959404965904513170984749 5984776862214192439119281)
            ·
              refine ⟨4488582646660644329339461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5984776862214192439119281 4488582646660644329339461)
              ·
                refine ⟨841609246248870811751149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4488582646660644329339461 841609246248870811751149)
                ·
                  refine ⟨315603467343326554406681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841609246248870811751149 315603467343326554406681)
                  ·
                    rfl

theorem cell20_691465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_691465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691465 prefixEnd_691465 := by exact prefixLift 691465
  have htrace : WordTrace (prefixWord ++ tailWord_691465) baseStart_691465 baseEnd_691465 := by
    simpa [prefixWord, tailWord_691465, baseEnd_691465] using wordTrace_append hprefix tailTrace_691465
  have hstable : (prefixWord ++ tailWord_691465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691465).length < 2 ^ (prefixWord ++ tailWord_691465).sum := by decide
  have hdescent : baseEnd_691465 < baseStart_691465 := by decide
  rcases family_descends (prefixWord ++ tailWord_691465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691474 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_691474 : Nat := 118140960795 + 691474 * 2 ^ 59
def prefixEnd_691474 : Nat := 4983230072969 + 3 ^ 40 * 691474 * 2
def baseEnd_691474 : Nat := 315607575188562523106645

theorem tailTrace_691474 : CollatzResearch.WordTrace tailWord_691474 prefixEnd_691474 315607575188562523106645 := by
  unfold tailWord_691474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6305032174228816800584369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16813419131276844801558317 6305032174228816800584369)
  ·
    refine ⟨4728774130671612600438277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6305032174228816800584369 4728774130671612600438277)
    ·
      refine ⟨886645149500927362582177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4728774130671612600438277 886645149500927362582177)
      ·
        refine ⟨664983862125695521936633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 886645149500927362582177 664983862125695521936633)
        ·
          refine ⟨498737896594271641452475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664983862125695521936633 498737896594271641452475)
          ·
            refine ⟨748106844891407462178713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498737896594271641452475 748106844891407462178713)
            ·
              refine ⟨561080133668555596634035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748106844891407462178713 561080133668555596634035)
              ·
                refine ⟨841620200502833394951053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561080133668555596634035 841620200502833394951053)
                ·
                  refine ⟨315607575188562523106645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841620200502833394951053 315607575188562523106645)
                  ·
                    rfl

theorem cell20_691474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_691474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691474 prefixEnd_691474 := by exact prefixLift 691474
  have htrace : WordTrace (prefixWord ++ tailWord_691474) baseStart_691474 baseEnd_691474 := by
    simpa [prefixWord, tailWord_691474, baseEnd_691474] using wordTrace_append hprefix tailTrace_691474
  have hstable : (prefixWord ++ tailWord_691474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691474).length < 2 ^ (prefixWord ++ tailWord_691474).sum := by decide
  have hdescent : baseEnd_691474 < baseStart_691474 := by decide
  rcases family_descends (prefixWord ++ tailWord_691474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691482 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_691482 : Nat := 118140960795 + 691482 * 2 ^ 59
def prefixEnd_691482 : Nat := 4983230072969 + 3 ^ 40 * 691482 * 2
def baseEnd_691482 : Nat := 315611226606550050839945

theorem tailTrace_691482 : CollatzResearch.WordTrace tailWord_691482 prefixEnd_691482 315611226606550050839945 := by
  unfold tailWord_691482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6305105120221571142157175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16813613653924189712419133 6305105120221571142157175)
  ·
    refine ⟨9457657680332356713235763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6305105120221571142157175 9457657680332356713235763)
    ·
      refine ⟨14186486520498535069853645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9457657680332356713235763 14186486520498535069853645)
      ·
        refine ⟨5319932445186950651195117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14186486520498535069853645 5319932445186950651195117)
        ·
          refine ⟨1994974666945106494198169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5319932445186950651195117 1994974666945106494198169)
          ·
            refine ⟨1496231000208829870648627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994974666945106494198169 1496231000208829870648627)
            ·
              refine ⟨2244346500313244805972941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496231000208829870648627 2244346500313244805972941)
              ·
                refine ⟨841629937617466802239853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2244346500313244805972941 841629937617466802239853)
                ·
                  refine ⟨315611226606550050839945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841629937617466802239853 315611226606550050839945)
                  ·
                    rfl

theorem cell20_691482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_691482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691482 prefixEnd_691482 := by exact prefixLift 691482
  have htrace : WordTrace (prefixWord ++ tailWord_691482) baseStart_691482 baseEnd_691482 := by
    simpa [prefixWord, tailWord_691482, baseEnd_691482] using wordTrace_append hprefix tailTrace_691482
  have hstable : (prefixWord ++ tailWord_691482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691482).length < 2 ^ (prefixWord ++ tailWord_691482).sum := by decide
  have hdescent : baseEnd_691482 < baseStart_691482 := by decide
  rcases family_descends (prefixWord ++ tailWord_691482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691496 : List Nat := [2, 1, 5, 1, 2, 1, 2, 6]
def baseStart_691496 : Nat := 118140960795 + 691496 * 2 ^ 59
def prefixEnd_691496 : Nat := 4983230072969 + 3 ^ 40 * 691496 * 2
def baseEnd_691496 : Nat := 105205872196009408124407

theorem tailTrace_691496 : CollatzResearch.WordTrace tailWord_691496 prefixEnd_691496 105205872196009408124407 := by
  unfold tailWord_691496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610465551417782479819171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16813954068557043306425561 12610465551417782479819171)
  ·
    refine ⟨18915698327126673719728757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12610465551417782479819171 18915698327126673719728757)
    ·
      refine ⟨1773346718168125661224571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18915698327126673719728757 1773346718168125661224571)
      ·
        refine ⟨2660020077252188491836857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773346718168125661224571 2660020077252188491836857)
        ·
          refine ⟨1995015057939141368877643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2660020077252188491836857 1995015057939141368877643)
          ·
            refine ⟨2992522586908712053316465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995015057939141368877643 2992522586908712053316465)
            ·
              refine ⟨2244391940181534039987349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992522586908712053316465 2244391940181534039987349)
              ·
                refine ⟨105205872196009408124407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2244391940181534039987349 105205872196009408124407)
                ·
                  rfl

theorem cell20_691496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_691496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691496 prefixEnd_691496 := by exact prefixLift 691496
  have htrace : WordTrace (prefixWord ++ tailWord_691496) baseStart_691496 baseEnd_691496 := by
    simpa [prefixWord, tailWord_691496, baseEnd_691496] using wordTrace_append hprefix tailTrace_691496
  have hstable : (prefixWord ++ tailWord_691496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691496).length < 2 ^ (prefixWord ++ tailWord_691496).sum := by decide
  have hdescent : baseEnd_691496 < baseStart_691496 := by decide
  rcases family_descends (prefixWord ++ tailWord_691496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691526 : List Nat := [6, 1, 1, 3, 2, 1, 1, 5]
def baseStart_691526 : Nat := 118140960795 + 691526 * 2 ^ 59
def prefixEnd_691526 : Nat := 4983230072969 + 3 ^ 40 * 691526 * 2
def baseEnd_691526 : Nat := 105210436468493817791033

theorem tailTrace_691526 : CollatzResearch.WordTrace tailWord_691526 prefixEnd_691526 105210436468493817791033 := by
  unfold tailWord_691526
  simp only [CollatzResearch.WordTrace]
  refine ⟨788188290397715002600951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16814683528484586722153621 788188290397715002600951)
  ·
    refine ⟨1182282435596572503901427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 788188290397715002600951 1182282435596572503901427)
    ·
      refine ⟨1773423653394858755852141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182282435596572503901427 1773423653394858755852141)
      ·
        refine ⟨665033870023072033444553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1773423653394858755852141 665033870023072033444553)
        ·
          refine ⟨498775402517304025083415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665033870023072033444553 498775402517304025083415)
          ·
            refine ⟨748163103775956037625123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498775402517304025083415 748163103775956037625123)
            ·
              refine ⟨1122244655663934056437685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748163103775956037625123 1122244655663934056437685)
              ·
                refine ⟨105210436468493817791033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1122244655663934056437685 105210436468493817791033)
                ·
                  rfl

theorem cell20_691526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_691526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691526 prefixEnd_691526 := by exact prefixLift 691526
  have htrace : WordTrace (prefixWord ++ tailWord_691526) baseStart_691526 baseEnd_691526 := by
    simpa [prefixWord, tailWord_691526, baseEnd_691526] using wordTrace_append hprefix tailTrace_691526
  have hstable : (prefixWord ++ tailWord_691526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691526).length < 2 ^ (prefixWord ++ tailWord_691526).sum := by decide
  have hdescent : baseEnd_691526 < baseStart_691526 := by decide
  rcases family_descends (prefixWord ++ tailWord_691526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691596 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_691596 : Nat := 118140960795 + 691596 * 2 ^ 59
def prefixEnd_691596 : Nat := 4983230072969 + 3 ^ 40 * 691596 * 2
def baseEnd_691596 : Nat := 315663259312872321039479

theorem tailTrace_691596 : CollatzResearch.WordTrace tailWord_691596 prefixEnd_691596 315663259312872321039479 := by
  unfold tailWord_691596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12612289201236641019139321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16816385601648854692185761 12612289201236641019139321)
  ·
    refine ⟨9459216900927480764354491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12612289201236641019139321 9459216900927480764354491)
    ·
      refine ⟨14188825351391221146531737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9459216900927480764354491 14188825351391221146531737)
      ·
        refine ⟨10641619013543415859898803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14188825351391221146531737 10641619013543415859898803)
        ·
          refine ⟨15962428520315123789848205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641619013543415859898803 15962428520315123789848205)
          ·
            refine ⟨5985910695118171421193077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15962428520315123789848205 5985910695118171421193077)
            ·
              refine ⟨561179127667328570736851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5985910695118171421193077 561179127667328570736851)
              ·
                refine ⟨841768691500992856105277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561179127667328570736851 841768691500992856105277)
                ·
                  refine ⟨315663259312872321039479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841768691500992856105277 315663259312872321039479)
                  ·
                    rfl

theorem cell20_691596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_691596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691596 prefixEnd_691596 := by exact prefixLift 691596
  have htrace : WordTrace (prefixWord ++ tailWord_691596) baseStart_691596 baseEnd_691596 := by
    simpa [prefixWord, tailWord_691596, baseEnd_691596] using wordTrace_append hprefix tailTrace_691596
  have hstable : (prefixWord ++ tailWord_691596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691596).length < 2 ^ (prefixWord ++ tailWord_691596).sum := by decide
  have hdescent : baseEnd_691596 < baseStart_691596 := by decide
  rcases family_descends (prefixWord ++ tailWord_691596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691637 : List Nat := [1, 3, 3, 2, 2, 2, 3, 2, 2]
def baseStart_691637 : Nat := 118140960795 + 691637 * 2 ^ 59
def prefixEnd_691637 : Nat := 4983230072969 + 3 ^ 40 * 691637 * 2
def baseEnd_691637 : Nat := 315681972830058400672645

theorem tailTrace_691637 : CollatzResearch.WordTrace tailWord_691637 prefixEnd_691637 315681972830058400672645 := by
  unfold tailWord_691637
  simp only [CollatzResearch.WordTrace]
  refine ⟨25226073795324746040521165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16817382530216497360347443 25226073795324746040521165)
  ·
    refine ⟨9459777673246779765195437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25226073795324746040521165 9459777673246779765195437)
    ·
      refine ⟨3547416627467542411948289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9459777673246779765195437 3547416627467542411948289)
      ·
        refine ⟨2660562470600656808961217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3547416627467542411948289 2660562470600656808961217)
        ·
          refine ⟨1995421852950492606720913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2660562470600656808961217 1995421852950492606720913)
          ·
            refine ⟨1496566389712869455040685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1995421852950492606720913 1496566389712869455040685)
            ·
              refine ⟨561212396142326045640257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1496566389712869455040685 561212396142326045640257)
              ·
                refine ⟨420909297106744534230193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561212396142326045640257 420909297106744534230193)
                ·
                  refine ⟨315681972830058400672645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420909297106744534230193 315681972830058400672645)
                  ·
                    rfl

theorem cell20_691637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_691637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691637 prefixEnd_691637 := by exact prefixLift 691637
  have htrace : WordTrace (prefixWord ++ tailWord_691637) baseStart_691637 baseEnd_691637 := by
    simpa [prefixWord, tailWord_691637, baseEnd_691637] using wordTrace_append hprefix tailTrace_691637
  have hstable : (prefixWord ++ tailWord_691637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691637).length < 2 ^ (prefixWord ++ tailWord_691637).sum := by decide
  have hdescent : baseEnd_691637 < baseStart_691637 := by decide
  rcases family_descends (prefixWord ++ tailWord_691637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691655 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 3]
def baseStart_691655 : Nat := 118140960795 + 691655 * 2 ^ 59
def prefixEnd_691655 : Nat := 4983230072969 + 3 ^ 40 * 691655 * 2
def baseEnd_691655 : Nat := 315690188520530338072571

theorem tailTrace_691655 : CollatzResearch.WordTrace tailWord_691655 prefixEnd_691655 315690188520530338072571 := by
  unfold tailWord_691655
  simp only [CollatzResearch.WordTrace]
  refine ⟨25226730309259535114676419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16817820206173023409784279 25226730309259535114676419)
  ·
    refine ⟨37840095463889302672014629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25226730309259535114676419 37840095463889302672014629)
    ·
      refine ⟨7095017899479244251002743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37840095463889302672014629 7095017899479244251002743)
      ·
        refine ⟨10642526849218866376504115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7095017899479244251002743 10642526849218866376504115)
        ·
          refine ⟨15963790273828299564756173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10642526849218866376504115 15963790273828299564756173)
          ·
            refine ⟨5986421352685612336783565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15963790273828299564756173 5986421352685612336783565)
            ·
              refine ⟨2244908007257104626293837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5986421352685612336783565 2244908007257104626293837)
              ·
                refine ⟨841840502721414234860189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2244908007257104626293837 841840502721414234860189)
                ·
                  refine ⟨315690188520530338072571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841840502721414234860189 315690188520530338072571)
                  ·
                    rfl

theorem cell20_691655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_691655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691655 prefixEnd_691655 := by exact prefixLift 691655
  have htrace : WordTrace (prefixWord ++ tailWord_691655) baseStart_691655 baseEnd_691655 := by
    simpa [prefixWord, tailWord_691655, baseEnd_691655] using wordTrace_append hprefix tailTrace_691655
  have hstable : (prefixWord ++ tailWord_691655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691655).length < 2 ^ (prefixWord ++ tailWord_691655).sum := by decide
  have hdescent : baseEnd_691655 < baseStart_691655 := by decide
  rcases family_descends (prefixWord ++ tailWord_691655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691662 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_691662 : Nat := 118140960795 + 691662 * 2 ^ 59
def prefixEnd_691662 : Nat := 4983230072969 + 3 ^ 40 * 691662 * 2
def baseEnd_691662 : Nat := 315693383511269424839209

theorem tailTrace_691662 : CollatzResearch.WordTrace tailWord_691662 prefixEnd_691662 315693383511269424839209 := by
  unfold tailWord_691662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153373202529271913772655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16817990413489450206787493 3153373202529271913772655)
  ·
    refine ⟨4730059803793907870658983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3153373202529271913772655 4730059803793907870658983)
    ·
      refine ⟨7095089705690861805988475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4730059803793907870658983 7095089705690861805988475)
      ·
        refine ⟨10642634558536292708982713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7095089705690861805988475 10642634558536292708982713)
        ·
          refine ⟨7981975918902219531737035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10642634558536292708982713 7981975918902219531737035)
          ·
            refine ⟨11972963878353329297605553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981975918902219531737035 11972963878353329297605553)
            ·
              refine ⟨8979722908764996973204165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11972963878353329297605553 8979722908764996973204165)
              ·
                refine ⟨1683698045393436932475781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8979722908764996973204165 1683698045393436932475781)
                ·
                  refine ⟨315693383511269424839209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683698045393436932475781 315693383511269424839209)
                  ·
                    rfl

theorem cell20_691662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_691662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691662 prefixEnd_691662 := by exact prefixLift 691662
  have htrace : WordTrace (prefixWord ++ tailWord_691662) baseStart_691662 baseEnd_691662 := by
    simpa [prefixWord, tailWord_691662, baseEnd_691662] using wordTrace_append hprefix tailTrace_691662
  have hstable : (prefixWord ++ tailWord_691662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691662).length < 2 ^ (prefixWord ++ tailWord_691662).sum := by decide
  have hdescent : baseEnd_691662 < baseStart_691662 := by decide
  rcases family_descends (prefixWord ++ tailWord_691662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691669 : List Nat := [1, 3, 2, 3, 1, 1, 1, 8]
def baseStart_691669 : Nat := 118140960795 + 691669 * 2 ^ 59
def prefixEnd_691669 : Nat := 4983230072969 + 3 ^ 40 * 691669 * 2
def baseEnd_691669 : Nat := 105232192834002837201949

theorem tailTrace_691669 : CollatzResearch.WordTrace tailWord_691669 prefixEnd_691669 105232192834002837201949 := by
  unfold tailWord_691669
  simp only [CollatzResearch.WordTrace]
  refine ⟨25227240931208815505686061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16818160620805877003790707 25227240931208815505686061)
  ·
    refine ⟨9460215349203305814632273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25227240931208815505686061 9460215349203305814632273)
    ·
      refine ⟨7095161511902479360974205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9460215349203305814632273 7095161511902479360974205)
      ·
        refine ⟨2660685566963429760365327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7095161511902479360974205 2660685566963429760365327)
        ·
          refine ⟨3991028350445144640547991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660685566963429760365327 3991028350445144640547991)
          ·
            refine ⟨5986542525667716960821987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991028350445144640547991 5986542525667716960821987)
            ·
              refine ⟨8979813788501575441232981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986542525667716960821987 8979813788501575441232981)
              ·
                refine ⟨105232192834002837201949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8979813788501575441232981 105232192834002837201949)
                ·
                  rfl

theorem cell20_691669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_691669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691669 prefixEnd_691669 := by exact prefixLift 691669
  have htrace : WordTrace (prefixWord ++ tailWord_691669) baseStart_691669 baseEnd_691669 := by
    simpa [prefixWord, tailWord_691669, baseEnd_691669] using wordTrace_append hprefix tailTrace_691669
  have hstable : (prefixWord ++ tailWord_691669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691669).length < 2 ^ (prefixWord ++ tailWord_691669).sum := by decide
  have hdescent : baseEnd_691669 < baseStart_691669 := by decide
  rcases family_descends (prefixWord ++ tailWord_691669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691679 : List Nat := [1, 1, 2, 3, 3, 1, 2, 5, 2]
def baseStart_691679 : Nat := 118140960795 + 691679 * 2 ^ 59
def prefixEnd_691679 : Nat := 4983230072969 + 3 ^ 40 * 691679 * 2
def baseEnd_691679 : Nat := 315701142774492921272473

theorem tailTrace_691679 : CollatzResearch.WordTrace tailWord_691679 prefixEnd_691679 315701142774492921272473 := by
  unfold tailWord_691679
  simp only [CollatzResearch.WordTrace]
  refine ⟨25227605661172587213550091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16818403774115058142366727 25227605661172587213550091)
  ·
    refine ⟨37841408491758880820325137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25227605661172587213550091 37841408491758880820325137)
    ·
      refine ⟨28381056368819160615243853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37841408491758880820325137 28381056368819160615243853)
      ·
        refine ⟨10642896138307185230716445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28381056368819160615243853 10642896138307185230716445)
        ·
          refine ⟨3991086051865194461518667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10642896138307185230716445 3991086051865194461518667)
          ·
            refine ⟨5986629077797791692278001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991086051865194461518667 5986629077797791692278001)
            ·
              refine ⟨4489971808348343769208501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5986629077797791692278001 4489971808348343769208501)
              ·
                refine ⟨420934857032657228363297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4489971808348343769208501 420934857032657228363297)
                ·
                  refine ⟨315701142774492921272473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420934857032657228363297 315701142774492921272473)
                  ·
                    rfl

theorem cell20_691679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 2].length) (baseStart_691679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691679 prefixEnd_691679 := by exact prefixLift 691679
  have htrace : WordTrace (prefixWord ++ tailWord_691679) baseStart_691679 baseEnd_691679 := by
    simpa [prefixWord, tailWord_691679, baseEnd_691679] using wordTrace_append hprefix tailTrace_691679
  have hstable : (prefixWord ++ tailWord_691679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691679).length < 2 ^ (prefixWord ++ tailWord_691679).sum := by decide
  have hdescent : baseEnd_691679 < baseStart_691679 := by decide
  rcases family_descends (prefixWord ++ tailWord_691679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691696 : List Nat := [2, 1, 1, 1, 3, 4, 4, 2, 2]
def baseStart_691696 : Nat := 118140960795 + 691696 * 2 ^ 59
def prefixEnd_691696 : Nat := 4983230072969 + 3 ^ 40 * 691696 * 2
def baseEnd_691696 : Nat := 315708902037716417705737

theorem tailTrace_691696 : CollatzResearch.WordTrace tailWord_691696 prefixEnd_691696 315708902037716417705737 := by
  unfold tailWord_691696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614112851055499558459471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16818817134740666077945961 12614112851055499558459471)
  ·
    refine ⟨18921169276583249337689207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12614112851055499558459471 18921169276583249337689207)
    ·
      refine ⟨28381753914874874006533811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18921169276583249337689207 28381753914874874006533811)
      ·
        refine ⟨42572630872312311009800717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28381753914874874006533811 42572630872312311009800717)
        ·
          refine ⟨15964736577117116628675269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42572630872312311009800717 15964736577117116628675269)
          ·
            refine ⟨2993388108209459367876613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15964736577117116628675269 2993388108209459367876613)
            ·
              refine ⟨561260270289273631476865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2993388108209459367876613 561260270289273631476865)
              ·
                refine ⟨420945202716955223607649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561260270289273631476865 420945202716955223607649)
                ·
                  refine ⟨315708902037716417705737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420945202716955223607649 315708902037716417705737)
                  ·
                    rfl

theorem cell20_691696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_691696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691696 prefixEnd_691696 := by exact prefixLift 691696
  have htrace : WordTrace (prefixWord ++ tailWord_691696) baseStart_691696 baseEnd_691696 := by
    simpa [prefixWord, tailWord_691696, baseEnd_691696] using wordTrace_append hprefix tailTrace_691696
  have hstable : (prefixWord ++ tailWord_691696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691696).length < 2 ^ (prefixWord ++ tailWord_691696).sum := by decide
  have hdescent : baseEnd_691696 < baseStart_691696 := by decide
  rcases family_descends (prefixWord ++ tailWord_691696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691745 : List Nat := [1, 2, 3, 2, 2, 3, 7]
def baseStart_691745 : Nat := 118140960795 + 691745 * 2 ^ 59
def prefixEnd_691745 : Nat := 4983230072969 + 3 ^ 40 * 691745 * 2
def baseEnd_691745 : Nat := 35081251885876669452467

theorem tailTrace_691745 : CollatzResearch.WordTrace tailWord_691745 prefixEnd_691745 35081251885876669452467 := by
  unfold tailWord_691745
  simp only [CollatzResearch.WordTrace]
  refine ⟨25230012878933480485452689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16820008585955653656968459 25230012878933480485452689)
  ·
    refine ⟨18922509659200110364089517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25230012878933480485452689 18922509659200110364089517)
    ·
      refine ⟨7095941122200041386533569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18922509659200110364089517 7095941122200041386533569)
      ·
        refine ⟨5321955841650031039900177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7095941122200041386533569 5321955841650031039900177)
        ·
          refine ⟨3991466881237523279925133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5321955841650031039900177 3991466881237523279925133)
          ·
            refine ⟨1496800080464071229971925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3991466881237523279925133 1496800080464071229971925)
            ·
              refine ⟨35081251885876669452467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1496800080464071229971925 35081251885876669452467)
              ·
                rfl

theorem cell20_691745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_691745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691745 prefixEnd_691745 := by exact prefixLift 691745
  have htrace : WordTrace (prefixWord ++ tailWord_691745) baseStart_691745 baseEnd_691745 := by
    simpa [prefixWord, tailWord_691745, baseEnd_691745] using wordTrace_append hprefix tailTrace_691745
  have hstable : (prefixWord ++ tailWord_691745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691745).length < 2 ^ (prefixWord ++ tailWord_691745).sum := by decide
  have hdescent : baseEnd_691745 < baseStart_691745 := by decide
  rcases family_descends (prefixWord ++ tailWord_691745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691824 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_691824 : Nat := 118140960795 + 691824 * 2 ^ 59
def prefixEnd_691824 : Nat := 4983230072969 + 3 ^ 40 * 691824 * 2
def baseEnd_691824 : Nat := 315767324725516861438547

theorem tailTrace_691824 : CollatzResearch.WordTrace tailWord_691824 prefixEnd_691824 315767324725516861438547 := by
  unfold tailWord_691824
  simp only [CollatzResearch.WordTrace]
  refine ⟨12616447122823638488789263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16821929497098184651719017 12616447122823638488789263)
  ·
    refine ⟨18924670684235457733183895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12616447122823638488789263 18924670684235457733183895)
    ·
      refine ⟨28387006026353186599775843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18924670684235457733183895 28387006026353186599775843)
      ·
        refine ⟨42580509039529779899663765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28387006026353186599775843 42580509039529779899663765)
        ·
          refine ⟨1995961361227958432796739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42580509039529779899663765 1995961361227958432796739)
          ·
            refine ⟨2993942041841937649195109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995961361227958432796739 2993942041841937649195109)
            ·
              refine ⟨561364132845363309224083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2993942041841937649195109 561364132845363309224083)
              ·
                refine ⟨842046199268044963836125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561364132845363309224083 842046199268044963836125)
                ·
                  refine ⟨315767324725516861438547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842046199268044963836125 315767324725516861438547)
                  ·
                    rfl

theorem cell20_691824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_691824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691824 prefixEnd_691824 := by exact prefixLift 691824
  have htrace : WordTrace (prefixWord ++ tailWord_691824) baseStart_691824 baseEnd_691824 := by
    simpa [prefixWord, tailWord_691824, baseEnd_691824] using wordTrace_append hprefix tailTrace_691824
  have hstable : (prefixWord ++ tailWord_691824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691824).length < 2 ^ (prefixWord ++ tailWord_691824).sum := by decide
  have hdescent : baseEnd_691824 < baseStart_691824 := by decide
  rcases family_descends (prefixWord ++ tailWord_691824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691835 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_691835 : Nat := 118140960795 + 691835 * 2 ^ 59
def prefixEnd_691835 : Nat := 4983230072969 + 3 ^ 40 * 691835 * 2
def baseEnd_691835 : Nat := 315772345425249712071835

theorem tailTrace_691835 : CollatzResearch.WordTrace tailWord_691835 prefixEnd_691835 315772345425249712071835 := by
  unfold tailWord_691835
  simp only [CollatzResearch.WordTrace]
  refine ⟨25233295448607425856228959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16822196965738283904152639 25233295448607425856228959)
  ·
    refine ⟨37849943172911138784343439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25233295448607425856228959 37849943172911138784343439)
    ·
      refine ⟨56774914759366708176515159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37849943172911138784343439 56774914759366708176515159)
      ·
        refine ⟨85162372139050062264772739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56774914759366708176515159 85162372139050062264772739)
        ·
          refine ⟨127743558208575093397159109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85162372139050062264772739 127743558208575093397159109)
          ·
            refine ⟨23951917164107830011967333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127743558208575093397159109 23951917164107830011967333)
            ·
              refine ⟨4490984468270218127243875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23951917164107830011967333 4490984468270218127243875)
              ·
                refine ⟨6736476702405327190865813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490984468270218127243875 6736476702405327190865813)
                ·
                  refine ⟨315772345425249712071835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6736476702405327190865813 315772345425249712071835)
                  ·
                    rfl

theorem cell20_691835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_691835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691835 prefixEnd_691835 := by exact prefixLift 691835
  have htrace : WordTrace (prefixWord ++ tailWord_691835) baseStart_691835 baseEnd_691835 := by
    simpa [prefixWord, tailWord_691835, baseEnd_691835] using wordTrace_append hprefix tailTrace_691835
  have hstable : (prefixWord ++ tailWord_691835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691835).length < 2 ^ (prefixWord ++ tailWord_691835).sum := by decide
  have hdescent : baseEnd_691835 < baseStart_691835 := by decide
  rcases family_descends (prefixWord ++ tailWord_691835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691876 : List Nat := [2, 3, 1, 2, 2, 4, 1, 5]
def baseStart_691876 : Nat := 118140960795 + 691876 * 2 ^ 59
def prefixEnd_691876 : Nat := 4983230072969 + 3 ^ 40 * 691876 * 2
def baseEnd_691876 : Nat := 105263686314145263901667

theorem tailTrace_691876 : CollatzResearch.WordTrace tailWord_691876 prefixEnd_691876 105263686314145263901667 := by
  unfold tailWord_691876
  simp only [CollatzResearch.WordTrace]
  refine ⟨12617395420729444929235741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16823193894305926572314321 12617395420729444929235741)
  ·
    refine ⟨4731523282773541848463403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12617395420729444929235741 4731523282773541848463403)
    ·
      refine ⟨7097284924160312772695105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4731523282773541848463403 7097284924160312772695105)
      ·
        refine ⟨5322963693120234579521329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7097284924160312772695105 5322963693120234579521329)
        ·
          refine ⟨3992222769840175934640997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5322963693120234579521329 3992222769840175934640997)
          ·
            refine ⟨748541769345032987745187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3992222769840175934640997 748541769345032987745187)
            ·
              refine ⟨1122812654017549481617781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748541769345032987745187 1122812654017549481617781)
              ·
                refine ⟨105263686314145263901667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1122812654017549481617781 105263686314145263901667)
                ·
                  rfl

theorem cell20_691876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_691876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691876 prefixEnd_691876 := by exact prefixLift 691876
  have htrace : WordTrace (prefixWord ++ tailWord_691876) baseStart_691876 baseEnd_691876 := by
    simpa [prefixWord, tailWord_691876, baseEnd_691876] using wordTrace_append hprefix tailTrace_691876
  have hstable : (prefixWord ++ tailWord_691876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691876).length < 2 ^ (prefixWord ++ tailWord_691876).sum := by decide
  have hdescent : baseEnd_691876 < baseStart_691876 := by decide
  rcases family_descends (prefixWord ++ tailWord_691876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691886 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_691886 : Nat := 118140960795 + 691886 * 2 ^ 59
def prefixEnd_691886 : Nat := 4983230072969 + 3 ^ 40 * 691886 * 2
def baseEnd_691886 : Nat := 315795623214920201371627

theorem tailTrace_691886 : CollatzResearch.WordTrace tailWord_691886 prefixEnd_691886 315795623214920201371627 := by
  unfold tailWord_691886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3154394446427832695791939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16823437047615107710890341 3154394446427832695791939)
  ·
    refine ⟨4731591669641749043687909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3154394446427832695791939 4731591669641749043687909)
    ·
      refine ⟨887173438057827945691483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4731591669641749043687909 887173438057827945691483)
      ·
        refine ⟨1330760157086741918537225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887173438057827945691483 1330760157086741918537225)
        ·
          refine ⟨998070117815056438902919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1330760157086741918537225 998070117815056438902919)
          ·
            refine ⟨1497105176722584658354379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998070117815056438902919 1497105176722584658354379)
            ·
              refine ⟨2245657765083876987531569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497105176722584658354379 2245657765083876987531569)
              ·
                refine ⟨1684243323812907740648677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245657765083876987531569 1684243323812907740648677)
                ·
                  refine ⟨315795623214920201371627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684243323812907740648677 315795623214920201371627)
                  ·
                    rfl

theorem cell20_691886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_691886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691886 prefixEnd_691886 := by exact prefixLift 691886
  have htrace : WordTrace (prefixWord ++ tailWord_691886) baseStart_691886 baseEnd_691886 := by
    simpa [prefixWord, tailWord_691886, baseEnd_691886] using wordTrace_append hprefix tailTrace_691886
  have hstable : (prefixWord ++ tailWord_691886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691886).length < 2 ^ (prefixWord ++ tailWord_691886).sum := by decide
  have hdescent : baseEnd_691886 < baseStart_691886 := by decide
  rcases family_descends (prefixWord ++ tailWord_691886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691893 : List Nat := [1, 3, 3, 3, 2, 1, 3, 4]
def baseStart_691893 : Nat := 118140960795 + 691893 * 2 ^ 59
def prefixEnd_691893 : Nat := 4983230072969 + 3 ^ 40 * 691893 * 2
def baseEnd_691893 : Nat := 105266272735219762712755

theorem tailTrace_691893 : CollatzResearch.WordTrace tailWord_691893 prefixEnd_691893 105266272735219762712755 := by
  unfold tailWord_691893
  simp only [CollatzResearch.WordTrace]
  refine ⟨25235410882397301761840333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16823607254931534507893555 25235410882397301761840333)
  ·
    refine ⟨9463279080898988160690125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25235410882397301761840333 9463279080898988160690125)
    ·
      refine ⟨3548729655337120560258797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9463279080898988160690125 3548729655337120560258797)
      ·
        refine ⟨1330773620751420210097049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3548729655337120560258797 1330773620751420210097049)
        ·
          refine ⟨998080215563565157572787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1330773620751420210097049 998080215563565157572787)
          ·
            refine ⟨1497120323345347736359181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998080215563565157572787 1497120323345347736359181)
            ·
              refine ⟨561420121254505401134693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1497120323345347736359181 561420121254505401134693)
              ·
                refine ⟨105266272735219762712755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561420121254505401134693 105266272735219762712755)
                ·
                  rfl

theorem cell20_691893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_691893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691893 prefixEnd_691893 := by exact prefixLift 691893
  have htrace : WordTrace (prefixWord ++ tailWord_691893) baseStart_691893 baseEnd_691893 := by
    simpa [prefixWord, tailWord_691893, baseEnd_691893] using wordTrace_append hprefix tailTrace_691893
  have hstable : (prefixWord ++ tailWord_691893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691893).length < 2 ^ (prefixWord ++ tailWord_691893).sum := by decide
  have hdescent : baseEnd_691893 < baseStart_691893 := by decide
  rcases family_descends (prefixWord ++ tailWord_691893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691904 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_691904 : Nat := 118140960795 + 691904 * 2 ^ 59
def prefixEnd_691904 : Nat := 4983230072969 + 3 ^ 40 * 691904 * 2
def baseEnd_691904 : Nat := 315803838905392138771553

theorem tailTrace_691904 : CollatzResearch.WordTrace tailWord_691904 prefixEnd_691904 315803838905392138771553 := by
  unfold tailWord_691904
  simp only [CollatzResearch.WordTrace]
  refine ⟨12617906042678725320245383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16823874723571633760327177 12617906042678725320245383)
  ·
    refine ⟨18926859064018087980368075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12617906042678725320245383 18926859064018087980368075)
    ·
      refine ⟨28390288596027131970552113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18926859064018087980368075 28390288596027131970552113)
      ·
        refine ⟨21292716447020348977914085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28390288596027131970552113 21292716447020348977914085)
        ·
          refine ⟨3992384333816315433358891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21292716447020348977914085 3992384333816315433358891)
          ·
            refine ⟨5988576500724473150038337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992384333816315433358891 5988576500724473150038337)
            ·
              refine ⟨4491432375543354862528753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5988576500724473150038337 4491432375543354862528753)
              ·
                refine ⟨3368574281657516146896565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4491432375543354862528753 3368574281657516146896565)
                ·
                  refine ⟨315803838905392138771553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3368574281657516146896565 315803838905392138771553)
                  ·
                    rfl

theorem cell20_691904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_691904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691904 prefixEnd_691904 := by exact prefixLift 691904
  have htrace : WordTrace (prefixWord ++ tailWord_691904) baseStart_691904 baseEnd_691904 := by
    simpa [prefixWord, tailWord_691904, baseEnd_691904] using wordTrace_append hprefix tailTrace_691904
  have hstable : (prefixWord ++ tailWord_691904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691904).length < 2 ^ (prefixWord ++ tailWord_691904).sum := by decide
  have hdescent : baseEnd_691904 < baseStart_691904 := by decide
  rcases family_descends (prefixWord ++ tailWord_691904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691911 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_691911 : Nat := 118140960795 + 691911 * 2 ^ 59
def prefixEnd_691911 : Nat := 4983230072969 + 3 ^ 40 * 691911 * 2
def baseEnd_691911 : Nat := 315807033896131225538191

theorem tailTrace_691911 : CollatzResearch.WordTrace tailWord_691911 prefixEnd_691911 315807033896131225538191 := by
  unfold tailWord_691911
  simp only [CollatzResearch.WordTrace]
  refine ⟨25236067396332090835995587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16824044930888060557330391 25236067396332090835995587)
  ·
    refine ⟨37854101094498136253993381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25236067396332090835995587 37854101094498136253993381)
    ·
      refine ⟨7097643955218400547623759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37854101094498136253993381 7097643955218400547623759)
      ·
        refine ⟨10646465932827600821435639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097643955218400547623759 10646465932827600821435639)
        ·
          refine ⟨15969698899241401232153459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10646465932827600821435639 15969698899241401232153459)
          ·
            refine ⟨23954548348862101848230189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15969698899241401232153459 23954548348862101848230189)
            ·
              refine ⟨8982955630823288193086321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23954548348862101848230189 8982955630823288193086321)
              ·
                refine ⟨6737216723117466144814741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8982955630823288193086321 6737216723117466144814741)
                ·
                  refine ⟨315807033896131225538191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6737216723117466144814741 315807033896131225538191)
                  ·
                    rfl

theorem cell20_691911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_691911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691911 prefixEnd_691911 := by exact prefixLift 691911
  have htrace : WordTrace (prefixWord ++ tailWord_691911) baseStart_691911 baseEnd_691911 := by
    simpa [prefixWord, tailWord_691911, baseEnd_691911] using wordTrace_append hprefix tailTrace_691911
  have hstable : (prefixWord ++ tailWord_691911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691911).length < 2 ^ (prefixWord ++ tailWord_691911).sum := by decide
  have hdescent : baseEnd_691911 < baseStart_691911 := by decide
  rcases family_descends (prefixWord ++ tailWord_691911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691917 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 3]
def baseStart_691917 : Nat := 118140960795 + 691917 * 2 ^ 59
def prefixEnd_691917 : Nat := 4983230072969 + 3 ^ 40 * 691917 * 2
def baseEnd_691917 : Nat := 315809772459621871338167

theorem tailTrace_691917 : CollatzResearch.WordTrace tailWord_691917 prefixEnd_691917 315809772459621871338167 := by
  unfold tailWord_691917
  simp only [CollatzResearch.WordTrace]
  refine ⟨25236286234310353860714005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16824190822873569240476003 25236286234310353860714005)
  ·
    refine ⟨1182950917233297837220969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25236286234310353860714005 1182950917233297837220969)
    ·
      refine ⟨887213187924973377915727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1182950917233297837220969 887213187924973377915727)
      ·
        refine ⟨1330819781887460066873591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887213187924973377915727 1330819781887460066873591)
        ·
          refine ⟨1996229672831190100310387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330819781887460066873591 1996229672831190100310387)
          ·
            refine ⟨2994344509246785150465581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996229672831190100310387 2994344509246785150465581)
            ·
              refine ⟨1122879190967544431424593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2994344509246785150465581 1122879190967544431424593)
              ·
                refine ⟨842159393225658323568445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122879190967544431424593 842159393225658323568445)
                ·
                  refine ⟨315809772459621871338167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842159393225658323568445 315809772459621871338167)
                  ·
                    rfl

theorem cell20_691917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_691917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691917 prefixEnd_691917 := by exact prefixLift 691917
  have htrace : WordTrace (prefixWord ++ tailWord_691917) baseStart_691917 baseEnd_691917 := by
    simpa [prefixWord, tailWord_691917, baseEnd_691917] using wordTrace_append hprefix tailTrace_691917
  have hstable : (prefixWord ++ tailWord_691917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691917).length < 2 ^ (prefixWord ++ tailWord_691917).sum := by decide
  have hdescent : baseEnd_691917 < baseStart_691917 := by decide
  rcases family_descends (prefixWord ++ tailWord_691917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691921 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 3]
def baseStart_691921 : Nat := 118140960795 + 691921 * 2 ^ 59
def prefixEnd_691921 : Nat := 4983230072969 + 3 ^ 40 * 691921 * 2
def baseEnd_691921 : Nat := 315811598168615635204817

theorem tailTrace_691921 : CollatzResearch.WordTrace tailWord_691921 prefixEnd_691921 315811598168615635204817 := by
  unfold tailWord_691921
  simp only [CollatzResearch.WordTrace]
  refine ⟨25236432126295862543859617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16824288084197241695906411 25236432126295862543859617)
  ·
    refine ⟨18927324094721896907894713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25236432126295862543859617 18927324094721896907894713)
    ·
      refine ⟨14195493071041422680921035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18927324094721896907894713 14195493071041422680921035)
      ·
        refine ⟨21293239606562134021381553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14195493071041422680921035 21293239606562134021381553)
        ·
          refine ⟨15969929704921600516036165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21293239606562134021381553 15969929704921600516036165)
          ·
            refine ⟨2994361819672800096756781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15969929704921600516036165 2994361819672800096756781)
            ·
              refine ⟨1122885682377300036283793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2994361819672800096756781 1122885682377300036283793)
              ·
                refine ⟨842164261782975027212845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122885682377300036283793 842164261782975027212845)
                ·
                  refine ⟨315811598168615635204817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842164261782975027212845 315811598168615635204817)
                  ·
                    rfl

theorem cell20_691921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_691921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691921 prefixEnd_691921 := by exact prefixLift 691921
  have htrace : WordTrace (prefixWord ++ tailWord_691921) baseStart_691921 baseEnd_691921 := by
    simpa [prefixWord, tailWord_691921, baseEnd_691921] using wordTrace_append hprefix tailTrace_691921
  have hstable : (prefixWord ++ tailWord_691921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691921).length < 2 ^ (prefixWord ++ tailWord_691921).sum := by decide
  have hdescent : baseEnd_691921 < baseStart_691921 := by decide
  rcases family_descends (prefixWord ++ tailWord_691921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691924 : List Nat := [2, 4, 1, 3, 1, 1, 2, 4, 2]
def baseStart_691924 : Nat := 118140960795 + 691924 * 2 ^ 59
def prefixEnd_691924 : Nat := 4983230072969 + 3 ^ 40 * 691924 * 2
def baseEnd_691924 : Nat := 315812967450360958104805

theorem tailTrace_691924 : CollatzResearch.WordTrace tailWord_691924 prefixEnd_691924 315812967450360958104805 := by
  unfold tailWord_691924
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618270772642497028109413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16824361030189996037479217 12618270772642497028109413)
  ·
    refine ⟨2365925769870468192770515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12618270772642497028109413 2365925769870468192770515)
    ·
      refine ⟨3548888654805702289155773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2365925769870468192770515 3548888654805702289155773)
      ·
        refine ⟨1330833245552138358433415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3548888654805702289155773 1330833245552138358433415)
        ·
          refine ⟨1996249868328207537650123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330833245552138358433415 1996249868328207537650123)
          ·
            refine ⟨2994374802492311306475185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996249868328207537650123 2994374802492311306475185)
            ·
              refine ⟨2245781101869233479856389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2994374802492311306475185 2245781101869233479856389)
              ·
                refine ⟨421083956600481277473073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2245781101869233479856389 421083956600481277473073)
                ·
                  refine ⟨315812967450360958104805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421083956600481277473073 315812967450360958104805)
                  ·
                    rfl

theorem cell20_691924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_691924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691924 prefixEnd_691924 := by exact prefixLift 691924
  have htrace : WordTrace (prefixWord ++ tailWord_691924) baseStart_691924 baseEnd_691924 := by
    simpa [prefixWord, tailWord_691924, baseEnd_691924] using wordTrace_append hprefix tailTrace_691924
  have hstable : (prefixWord ++ tailWord_691924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691924).length < 2 ^ (prefixWord ++ tailWord_691924).sum := by decide
  have hdescent : baseEnd_691924 < baseStart_691924 := by decide
  rcases family_descends (prefixWord ++ tailWord_691924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691928 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_691928 : Nat := 118140960795 + 691928 * 2 ^ 59
def prefixEnd_691928 : Nat := 4983230072969 + 3 ^ 40 * 691928 * 2
def baseEnd_691928 : Nat := 315814793159354721971455

theorem tailTrace_691928 : CollatzResearch.WordTrace tailWord_691928 prefixEnd_691928 315814793159354721971455 := by
  unfold tailWord_691928
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618343718635251369682219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16824458291513668492909625 12618343718635251369682219)
  ·
    refine ⟨18927515577952877054523329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12618343718635251369682219 18927515577952877054523329)
    ·
      refine ⟨14195636683464657790892497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18927515577952877054523329 14195636683464657790892497)
      ·
        refine ⟨10646727512598493343169373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14195636683464657790892497 10646727512598493343169373)
        ·
          refine ⟨3992522817224435003688515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10646727512598493343169373 3992522817224435003688515)
          ·
            refine ⟨5988784225836652505532773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992522817224435003688515 5988784225836652505532773)
            ·
              refine ⟨1122897042344372344787395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5988784225836652505532773 1122897042344372344787395)
              ·
                refine ⟨1684345563516558517181093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122897042344372344787395 1684345563516558517181093)
                ·
                  refine ⟨315814793159354721971455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684345563516558517181093 315814793159354721971455)
                  ·
                    rfl

theorem cell20_691928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_691928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691928 prefixEnd_691928 := by exact prefixLift 691928
  have htrace : WordTrace (prefixWord ++ tailWord_691928) baseStart_691928 baseEnd_691928 := by
    simpa [prefixWord, tailWord_691928, baseEnd_691928] using wordTrace_append hprefix tailTrace_691928
  have hstable : (prefixWord ++ tailWord_691928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691928).length < 2 ^ (prefixWord ++ tailWord_691928).sum := by decide
  have hdescent : baseEnd_691928 < baseStart_691928 := by decide
  rcases family_descends (prefixWord ++ tailWord_691928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691980 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_691980 : Nat := 118140960795 + 691980 * 2 ^ 59
def prefixEnd_691980 : Nat := 4983230072969 + 3 ^ 40 * 691980 * 2
def baseEnd_691980 : Nat := 315838527376273652237909

theorem tailTrace_691980 : CollatzResearch.WordTrace tailWord_691980 prefixEnd_691980 315838527376273652237909 := by
  unfold tailWord_691980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12619292016541057810128697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16825722688721410413504929 12619292016541057810128697)
  ·
    refine ⟨9464469012405793357596523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12619292016541057810128697 9464469012405793357596523)
    ·
      refine ⟨14196703518608690036394785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9464469012405793357596523 14196703518608690036394785)
      ·
        refine ⟨10647527638956517527296089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14196703518608690036394785 10647527638956517527296089)
        ·
          refine ⟨7985645729217388145472067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10647527638956517527296089 7985645729217388145472067)
          ·
            refine ⟨11978468593826082218208101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7985645729217388145472067 11978468593826082218208101)
            ·
              refine ⟨2245962861342390415914019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11978468593826082218208101 2245962861342390415914019)
              ·
                refine ⟨3368944292013585623871029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245962861342390415914019 3368944292013585623871029)
                ·
                  refine ⟨315838527376273652237909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3368944292013585623871029 315838527376273652237909)
                  ·
                    rfl

theorem cell20_691980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_691980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691980 prefixEnd_691980 := by exact prefixLift 691980
  have htrace : WordTrace (prefixWord ++ tailWord_691980) baseStart_691980 baseEnd_691980 := by
    simpa [prefixWord, tailWord_691980, baseEnd_691980] using wordTrace_append hprefix tailTrace_691980
  have hstable : (prefixWord ++ tailWord_691980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691980).length < 2 ^ (prefixWord ++ tailWord_691980).sum := by decide
  have hdescent : baseEnd_691980 < baseStart_691980 := by decide
  rcases family_descends (prefixWord ++ tailWord_691980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691987 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_691987 : Nat := 118140960795 + 691987 * 2 ^ 59
def prefixEnd_691987 : Nat := 4983230072969 + 3 ^ 40 * 691987 * 2
def baseEnd_691987 : Nat := 315841722367012739004547

theorem tailTrace_691987 : CollatzResearch.WordTrace tailWord_691987 prefixEnd_691987 315841722367012739004547 := by
  unfold tailWord_691987
  simp only [CollatzResearch.WordTrace]
  refine ⟨25238839344056755815762215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16825892896037837210508143 25238839344056755815762215)
  ·
    refine ⟨37858259016085133723643323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25238839344056755815762215 37858259016085133723643323)
    ·
      refine ⟨56787388524127700585464985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37858259016085133723643323 56787388524127700585464985)
      ·
        refine ⟨42590541393095775439098739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56787388524127700585464985 42590541393095775439098739)
        ·
          refine ⟨63885812089643663158648109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42590541393095775439098739 63885812089643663158648109)
          ·
            refine ⟨23957179533616373684493041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63885812089643663158648109 23957179533616373684493041)
            ·
              refine ⟨17967884650212280263369781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23957179533616373684493041 17967884650212280263369781)
              ·
                refine ⟨1684489185957401274690917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17967884650212280263369781 1684489185957401274690917)
                ·
                  refine ⟨315841722367012739004547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684489185957401274690917 315841722367012739004547)
                  ·
                    rfl

theorem cell20_691987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_691987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_691987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_691987 prefixEnd_691987 := by exact prefixLift 691987
  have htrace : WordTrace (prefixWord ++ tailWord_691987) baseStart_691987 baseEnd_691987 := by
    simpa [prefixWord, tailWord_691987, baseEnd_691987] using wordTrace_append hprefix tailTrace_691987
  have hstable : (prefixWord ++ tailWord_691987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691987).length < 2 ^ (prefixWord ++ tailWord_691987).sum := by decide
  have hdescent : baseEnd_691987 < baseStart_691987 := by decide
  rcases family_descends (prefixWord ++ tailWord_691987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692035 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 3]
def baseStart_692035 : Nat := 118140960795 + 692035 * 2 ^ 59
def prefixEnd_692035 : Nat := 4983230072969 + 3 ^ 40 * 692035 * 2
def baseEnd_692035 : Nat := 315863630874937905404351

theorem tailTrace_692035 : CollatzResearch.WordTrace tailWord_692035 prefixEnd_692035 315863630874937905404351 := by
  unfold tailWord_692035
  simp only [CollatzResearch.WordTrace]
  refine ⟨25240590047882860013509559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16827060031921906675673039 25240590047882860013509559)
  ·
    refine ⟨37860885071824290020264339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25240590047882860013509559 37860885071824290020264339)
    ·
      refine ⟨56791327607736435030396509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37860885071824290020264339 56791327607736435030396509)
      ·
        refine ⟨21296747852901163136398691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56791327607736435030396509 21296747852901163136398691)
        ·
          refine ⟨31945121779351744704598037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21296747852901163136398691 31945121779351744704598037)
          ·
            refine ⟨1497427583407113033028033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31945121779351744704598037 1497427583407113033028033)
            ·
              refine ⟨1123070687555334774771025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497427583407113033028033 1123070687555334774771025)
              ·
                refine ⟨842303015666501081078269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123070687555334774771025 842303015666501081078269)
                ·
                  refine ⟨315863630874937905404351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842303015666501081078269 315863630874937905404351)
                  ·
                    rfl

theorem cell20_692035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_692035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692035 prefixEnd_692035 := by exact prefixLift 692035
  have htrace : WordTrace (prefixWord ++ tailWord_692035) baseStart_692035 baseEnd_692035 := by
    simpa [prefixWord, tailWord_692035, baseEnd_692035] using wordTrace_append hprefix tailTrace_692035
  have hstable : (prefixWord ++ tailWord_692035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692035).length < 2 ^ (prefixWord ++ tailWord_692035).sum := by decide
  have hdescent : baseEnd_692035 < baseStart_692035 := by decide
  rcases family_descends (prefixWord ++ tailWord_692035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692045 : List Nat := [1, 6, 1, 2, 1, 3, 1, 5]
def baseStart_692045 : Nat := 118140960795 + 692045 * 2 ^ 59
def prefixEnd_692045 : Nat := 4983230072969 + 3 ^ 40 * 692045 * 2
def baseEnd_692045 : Nat := 105289398382474105023659

theorem tailTrace_692045 : CollatzResearch.WordTrace tailWord_692045 prefixEnd_692045 105289398382474105023659 := by
  unfold tailWord_692045
  simp only [CollatzResearch.WordTrace]
  refine ⟨25240954777846631721373589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16827303185231087814249059 25240954777846631721373589)
  ·
    refine ⟨1183169755211560861939387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25240954777846631721373589 1183169755211560861939387)
    ·
      refine ⟨1774754632817341292909081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183169755211560861939387 1774754632817341292909081)
      ·
        refine ⟨1331065974613005969681811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1774754632817341292909081 1331065974613005969681811)
        ·
          refine ⟨1996598961919508954522717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331065974613005969681811 1996598961919508954522717)
          ·
            refine ⟨748724610719815857946019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1996598961919508954522717 748724610719815857946019)
            ·
              refine ⟨1123086916079723786919029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748724610719815857946019 1123086916079723786919029)
              ·
                refine ⟨105289398382474105023659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1123086916079723786919029 105289398382474105023659)
                ·
                  rfl

theorem cell20_692045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_692045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692045 prefixEnd_692045 := by exact prefixLift 692045
  have htrace : WordTrace (prefixWord ++ tailWord_692045) baseStart_692045 baseEnd_692045 := by
    simpa [prefixWord, tailWord_692045, baseEnd_692045] using wordTrace_append hprefix tailTrace_692045
  have hstable : (prefixWord ++ tailWord_692045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692045).length < 2 ^ (prefixWord ++ tailWord_692045).sum := by decide
  have hdescent : baseEnd_692045 < baseStart_692045 := by decide
  rcases family_descends (prefixWord ++ tailWord_692045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692049 : List Nat := [1, 2, 2, 1, 5, 1, 3, 5]
def baseStart_692049 : Nat := 118140960795 + 692049 * 2 ^ 59
def prefixEnd_692049 : Nat := 4983230072969 + 3 ^ 40 * 692049 * 2
def baseEnd_692049 : Nat := 105290006952138692979209

theorem tailTrace_692049 : CollatzResearch.WordTrace tailWord_692049 prefixEnd_692049 105290006952138692979209 := by
  unfold tailWord_692049
  simp only [CollatzResearch.WordTrace]
  refine ⟨25241100669832140404519201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16827400446554760269679467 25241100669832140404519201)
  ·
    refine ⟨18930825502374105303389401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25241100669832140404519201 18930825502374105303389401)
    ·
      refine ⟨14198119126780578977542051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18930825502374105303389401 14198119126780578977542051)
      ·
        refine ⟨21297178690170868466313077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14198119126780578977542051 21297178690170868466313077)
        ·
          refine ⟨1996610502203518918716851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21297178690170868466313077 1996610502203518918716851)
          ·
            refine ⟨2994915753305278378075277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996610502203518918716851 2994915753305278378075277)
            ·
              refine ⟨1123093407489479391778229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2994915753305278378075277 1123093407489479391778229)
              ·
                refine ⟨105290006952138692979209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1123093407489479391778229 105290006952138692979209)
                ·
                  rfl

theorem cell20_692049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_692049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692049 prefixEnd_692049 := by exact prefixLift 692049
  have htrace : WordTrace (prefixWord ++ tailWord_692049) baseStart_692049 baseEnd_692049 := by
    simpa [prefixWord, tailWord_692049, baseEnd_692049] using wordTrace_append hprefix tailTrace_692049
  have hstable : (prefixWord ++ tailWord_692049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692049).length < 2 ^ (prefixWord ++ tailWord_692049).sum := by decide
  have hdescent : baseEnd_692049 < baseStart_692049 := by decide
  rcases family_descends (prefixWord ++ tailWord_692049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692063 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_692063 : Nat := 118140960795 + 692063 * 2 ^ 59
def prefixEnd_692063 : Nat := 4983230072969 + 3 ^ 40 * 692063 * 2
def baseEnd_692063 : Nat := 315876410837894252470903

theorem tailTrace_692063 : CollatzResearch.WordTrace tailWord_692063 prefixEnd_692063 315876410837894252470903 := by
  unfold tailWord_692063
  simp only [CollatzResearch.WordTrace]
  refine ⟨25241611291781420795528843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16827740861187613863685895 25241611291781420795528843)
  ·
    refine ⟨37862416937672131193293265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25241611291781420795528843 37862416937672131193293265)
    ·
      refine ⟨28396812703254098394969949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37862416937672131193293265 28396812703254098394969949)
      ·
        refine ⟨10648804763720286898113731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28396812703254098394969949 10648804763720286898113731)
        ·
          refine ⟨15973207145580430347170597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10648804763720286898113731 15973207145580430347170597)
          ·
            refine ⟨2994976339796330690094487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15973207145580430347170597 2994976339796330690094487)
            ·
              refine ⟨4492464509694496035141731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994976339796330690094487 4492464509694496035141731)
              ·
                refine ⟨6738696764541744052712597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492464509694496035141731 6738696764541744052712597)
                ·
                  refine ⟨315876410837894252470903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6738696764541744052712597 315876410837894252470903)
                  ·
                    rfl

theorem cell20_692063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_692063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692063 prefixEnd_692063 := by exact prefixLift 692063
  have htrace : WordTrace (prefixWord ++ tailWord_692063) baseStart_692063 baseEnd_692063 := by
    simpa [prefixWord, tailWord_692063, baseEnd_692063] using wordTrace_append hprefix tailTrace_692063
  have hstable : (prefixWord ++ tailWord_692063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692063).length < 2 ^ (prefixWord ++ tailWord_692063).sum := by decide
  have hdescent : baseEnd_692063 < baseStart_692063 := by decide
  rcases family_descends (prefixWord ++ tailWord_692063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692086 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_692086 : Nat := 118140960795 + 692086 * 2 ^ 59
def prefixEnd_692086 : Nat := 4983230072969 + 3 ^ 40 * 692086 * 2
def baseEnd_692086 : Nat := 315886908664608394704143

theorem tailTrace_692086 : CollatzResearch.WordTrace tailWord_692086 prefixEnd_692086 315886908664608394704143 := by
  unfold tailWord_692086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577653135668630982726007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16828300113798730482410741 1577653135668630982726007)
  ·
    refine ⟨2366479703502946474089011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1577653135668630982726007 2366479703502946474089011)
    ·
      refine ⟨3549719555254419711133517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366479703502946474089011 3549719555254419711133517)
      ·
        refine ⟨1331144833220407391675069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3549719555254419711133517 1331144833220407391675069)
        ·
          refine ⟨499179312457652771878151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1331144833220407391675069 499179312457652771878151)
          ·
            refine ⟨748768968686479157817227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499179312457652771878151 748768968686479157817227)
            ·
              refine ⟨1123153453029718736725841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748768968686479157817227 1123153453029718736725841)
              ·
                refine ⟨842365089772289052544381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123153453029718736725841 842365089772289052544381)
                ·
                  refine ⟨315886908664608394704143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842365089772289052544381 315886908664608394704143)
                  ·
                    rfl

theorem cell20_692086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_692086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692086 prefixEnd_692086 := by exact prefixLift 692086
  have htrace : WordTrace (prefixWord ++ tailWord_692086) baseStart_692086 baseEnd_692086 := by
    simpa [prefixWord, tailWord_692086, baseEnd_692086] using wordTrace_append hprefix tailTrace_692086
  have hstable : (prefixWord ++ tailWord_692086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692086).length < 2 ^ (prefixWord ++ tailWord_692086).sum := by decide
  have hdescent : baseEnd_692086 < baseStart_692086 := by decide
  rcases family_descends (prefixWord ++ tailWord_692086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692108 : List Nat := [2, 2, 1, 2, 1, 2, 1, 9]
def baseStart_692108 : Nat := 118140960795 + 692108 * 2 ^ 59
def prefixEnd_692108 : Nat := 4983230072969 + 3 ^ 40 * 692108 * 2
def baseEnd_692108 : Nat := 105298983354691365323573

theorem tailTrace_692108 : CollatzResearch.WordTrace tailWord_692108 prefixEnd_692108 105298983354691365323573 := by
  unfold tailWord_692108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12621626288309196740458489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16828835051078928987277985 12621626288309196740458489)
  ·
    refine ⟨9466219716231897555343867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12621626288309196740458489 9466219716231897555343867)
    ·
      refine ⟨14199329574347846333015801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9466219716231897555343867 14199329574347846333015801)
      ·
        refine ⟨10649497180760884749761851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14199329574347846333015801 10649497180760884749761851)
        ·
          refine ⟨15974245771141327124642777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10649497180760884749761851 15974245771141327124642777)
          ·
            refine ⟨11980684328355995343482083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15974245771141327124642777 11980684328355995343482083)
            ·
              refine ⟨17971026492533993015223125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11980684328355995343482083 17971026492533993015223125)
              ·
                refine ⟨105298983354691365323573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17971026492533993015223125 105298983354691365323573)
                ·
                  rfl

theorem cell20_692108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_692108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692108 prefixEnd_692108 := by exact prefixLift 692108
  have htrace : WordTrace (prefixWord ++ tailWord_692108) baseStart_692108 baseEnd_692108 := by
    simpa [prefixWord, tailWord_692108, baseEnd_692108] using wordTrace_append hprefix tailTrace_692108
  have hstable : (prefixWord ++ tailWord_692108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692108).length < 2 ^ (prefixWord ++ tailWord_692108).sum := by decide
  have hdescent : baseEnd_692108 < baseStart_692108 := by decide
  rcases family_descends (prefixWord ++ tailWord_692108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692125 : List Nat := [1, 4, 2, 1, 2, 3, 1, 6]
def baseStart_692125 : Nat := 118140960795 + 692125 * 2 ^ 59
def prefixEnd_692125 : Nat := 4983230072969 + 3 ^ 40 * 692125 * 2
def baseEnd_692125 : Nat := 105301569775765864134661

theorem tailTrace_692125 : CollatzResearch.WordTrace tailWord_692125 prefixEnd_692125 105301569775765864134661 := by
  unfold tailWord_692125
  simp only [CollatzResearch.WordTrace]
  refine ⟨25243872617556805384285829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16829248411704536922857219 25243872617556805384285829)
  ·
    refine ⟨4733226115791901009553593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25243872617556805384285829 4733226115791901009553593)
    ·
      refine ⟨3549919586843925757165195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4733226115791901009553593 3549919586843925757165195)
      ·
        refine ⟨5324879380265888635747793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549919586843925757165195 5324879380265888635747793)
        ·
          refine ⟨3993659535199416476810845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5324879380265888635747793 3993659535199416476810845)
          ·
            refine ⟨1497622325699781178804067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3993659535199416476810845 1497622325699781178804067)
            ·
              refine ⟨2246433488549671768206101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497622325699781178804067 2246433488549671768206101)
              ·
                refine ⟨105301569775765864134661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2246433488549671768206101 105301569775765864134661)
                ·
                  rfl

theorem cell20_692125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_692125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692125 prefixEnd_692125 := by exact prefixLift 692125
  have htrace : WordTrace (prefixWord ++ tailWord_692125) baseStart_692125 baseEnd_692125 := by
    simpa [prefixWord, tailWord_692125, baseEnd_692125] using wordTrace_append hprefix tailTrace_692125
  have hstable : (prefixWord ++ tailWord_692125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692125).length < 2 ^ (prefixWord ++ tailWord_692125).sum := by decide
  have hdescent : baseEnd_692125 < baseStart_692125 := by decide
  rcases family_descends (prefixWord ++ tailWord_692125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692132 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_692132 : Nat := 118140960795 + 692132 * 2 ^ 59
def prefixEnd_692132 : Nat := 4983230072969 + 3 ^ 40 * 692132 * 2
def baseEnd_692132 : Nat := 315907904318036679170621

theorem tailTrace_692132 : CollatzResearch.WordTrace tailWord_692132 prefixEnd_692132 315907904318036679170621 := by
  unfold tailWord_692132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622063964265722789895325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16829418619020963719860433 12622063964265722789895325)
  ·
    refine ⟨4733273986599646046210747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12622063964265722789895325 4733273986599646046210747)
    ·
      refine ⟨7099910979899469069316121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4733273986599646046210747 7099910979899469069316121)
      ·
        refine ⟨5324933234924601801987091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7099910979899469069316121 5324933234924601801987091)
        ·
          refine ⟨7987399852386902702980637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324933234924601801987091 7987399852386902702980637)
          ·
            refine ⟨2995274944645088513617739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7987399852386902702980637 2995274944645088513617739)
            ·
              refine ⟨4492912416967632770426609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995274944645088513617739 4492912416967632770426609)
              ·
                refine ⟨3369684312725724577819957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4492912416967632770426609 3369684312725724577819957)
                ·
                  refine ⟨315907904318036679170621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3369684312725724577819957 315907904318036679170621)
                  ·
                    rfl

theorem cell20_692132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_692132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692132 prefixEnd_692132 := by exact prefixLift 692132
  have htrace : WordTrace (prefixWord ++ tailWord_692132) baseStart_692132 baseEnd_692132 := by
    simpa [prefixWord, tailWord_692132, baseEnd_692132] using wordTrace_append hprefix tailTrace_692132
  have hstable : (prefixWord ++ tailWord_692132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692132).length < 2 ^ (prefixWord ++ tailWord_692132).sum := by decide
  have hdescent : baseEnd_692132 < baseStart_692132 := by decide
  rcases family_descends (prefixWord ++ tailWord_692132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692148 : List Nat := [2, 5, 2, 1, 2, 1, 3, 2, 2]
def baseStart_692148 : Nat := 118140960795 + 692148 * 2 ^ 59
def prefixEnd_692148 : Nat := 4983230072969 + 3 ^ 40 * 692148 * 2
def baseEnd_692148 : Nat := 315915207154011734637223

theorem tailTrace_692148 : CollatzResearch.WordTrace tailWord_692148 prefixEnd_692148 315915207154011734637223 := by
  unfold tailWord_692148
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622355748236740156186549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16829807664315653541582065 12622355748236740156186549)
  ·
    refine ⟨1183345851397194389642489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12622355748236740156186549 1183345851397194389642489)
    ·
      refine ⟨887509388547895792231867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1183345851397194389642489 887509388547895792231867)
      ·
        refine ⟨1331264082821843688347801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887509388547895792231867 1331264082821843688347801)
        ·
          refine ⟨998448062116382766260851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1331264082821843688347801 998448062116382766260851)
          ·
            refine ⟨1497672093174574149391277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998448062116382766260851 1497672093174574149391277)
            ·
              refine ⟨561627034940465306021729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1497672093174574149391277 561627034940465306021729)
              ·
                refine ⟨421220276205348979516297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561627034940465306021729 421220276205348979516297)
                ·
                  refine ⟨315915207154011734637223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421220276205348979516297 315915207154011734637223)
                  ·
                    rfl

theorem cell20_692148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_692148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692148 prefixEnd_692148 := by exact prefixLift 692148
  have htrace : WordTrace (prefixWord ++ tailWord_692148) baseStart_692148 baseEnd_692148 := by
    simpa [prefixWord, tailWord_692148, baseEnd_692148] using wordTrace_append hprefix tailTrace_692148
  have hstable : (prefixWord ++ tailWord_692148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692148).length < 2 ^ (prefixWord ++ tailWord_692148).sum := by decide
  have hdescent : baseEnd_692148 < baseStart_692148 := by decide
  rcases family_descends (prefixWord ++ tailWord_692148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692184 : List Nat := [2, 1, 2, 2, 2, 2, 1, 8]
def baseStart_692184 : Nat := 118140960795 + 692184 * 2 ^ 59
def prefixEnd_692184 : Nat := 4983230072969 + 3 ^ 40 * 692184 * 2
def baseEnd_692184 : Nat := 105310546178318536479025

theorem tailTrace_692184 : CollatzResearch.WordTrace tailWord_692184 prefixEnd_692184 105310546178318536479025 := by
  unfold tailWord_692184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623012262171529230341803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16830683016228705640455737 12623012262171529230341803)
  ·
    refine ⟨18934518393257293845512705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12623012262171529230341803 18934518393257293845512705)
    ·
      refine ⟨14200888794942970384134529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18934518393257293845512705 14200888794942970384134529)
      ·
        refine ⟨10650666596207227788100897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14200888794942970384134529 10650666596207227788100897)
        ·
          refine ⟨7987999947155420841075673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10650666596207227788100897 7987999947155420841075673)
          ·
            refine ⟨5990999960366565630806755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7987999947155420841075673 5990999960366565630806755)
            ·
              refine ⟨8986499940549848446210133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990999960366565630806755 8986499940549848446210133)
              ·
                refine ⟨105310546178318536479025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8986499940549848446210133 105310546178318536479025)
                ·
                  rfl

theorem cell20_692184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_692184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692184 prefixEnd_692184 := by exact prefixLift 692184
  have htrace : WordTrace (prefixWord ++ tailWord_692184) baseStart_692184 baseEnd_692184 := by
    simpa [prefixWord, tailWord_692184, baseEnd_692184] using wordTrace_append hprefix tailTrace_692184
  have hstable : (prefixWord ++ tailWord_692184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692184).length < 2 ^ (prefixWord ++ tailWord_692184).sum := by decide
  have hdescent : baseEnd_692184 < baseStart_692184 := by decide
  rcases family_descends (prefixWord ++ tailWord_692184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692208 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_692208 : Nat := 118140960795 + 692208 * 2 ^ 59
def prefixEnd_692208 : Nat := 4983230072969 + 3 ^ 40 * 692208 * 2
def baseEnd_692208 : Nat := 315942592788918192636977

theorem tailTrace_692208 : CollatzResearch.WordTrace tailWord_692208 prefixEnd_692208 315942592788918192636977 := by
  unfold tailWord_692208
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623449938128055279778639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16831266584170740373038185 12623449938128055279778639)
  ·
    refine ⟨18935174907192082919667959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12623449938128055279778639 18935174907192082919667959)
    ·
      refine ⟨28402762360788124379501939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18935174907192082919667959 28402762360788124379501939)
      ·
        refine ⟨42604143541182186569252909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28402762360788124379501939 42604143541182186569252909)
        ·
          refine ⟨15976553827943319963469841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42604143541182186569252909 15976553827943319963469841)
          ·
            refine ⟨11982415370957489972602381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15976553827943319963469841 11982415370957489972602381)
            ·
              refine ⟨4493405764109058739725893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11982415370957489972602381 4493405764109058739725893)
              ·
                refine ⟨842513580770448513698605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4493405764109058739725893 842513580770448513698605)
                ·
                  refine ⟨315942592788918192636977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842513580770448513698605 315942592788918192636977)
                  ·
                    rfl

theorem cell20_692208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_692208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692208 prefixEnd_692208 := by exact prefixLift 692208
  have htrace : WordTrace (prefixWord ++ tailWord_692208) baseStart_692208 baseEnd_692208 := by
    simpa [prefixWord, tailWord_692208, baseEnd_692208] using wordTrace_append hprefix tailTrace_692208
  have hstable : (prefixWord ++ tailWord_692208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692208).length < 2 ^ (prefixWord ++ tailWord_692208).sum := by decide
  have hdescent : baseEnd_692208 < baseStart_692208 := by decide
  rcases family_descends (prefixWord ++ tailWord_692208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692270 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_692270 : Nat := 118140960795 + 692270 * 2 ^ 59
def prefixEnd_692270 : Nat := 4983230072969 + 3 ^ 40 * 692270 * 2
def baseEnd_692270 : Nat := 315970891278321532570057

theorem tailTrace_692270 : CollatzResearch.WordTrace tailWord_692270 prefixEnd_692270 315970891278321532570057 := by
  unfold tailWord_692270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156145150253936893539283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16832774134687663432209509 3156145150253936893539283)
  ·
    refine ⟨4734217725380905340308925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3156145150253936893539283 4734217725380905340308925)
    ·
      refine ⟨1775331647017839502615847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4734217725380905340308925 1775331647017839502615847)
      ·
        refine ⟨2662997470526759253923771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775331647017839502615847 2662997470526759253923771)
        ·
          refine ⟨3994496205790138880885657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2662997470526759253923771 3994496205790138880885657)
          ·
            refine ⟨2995872154342604160664243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3994496205790138880885657 2995872154342604160664243)
            ·
              refine ⟨4493808231513906240996365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995872154342604160664243 4493808231513906240996365)
              ·
                refine ⟨1685178086817714840373637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4493808231513906240996365 1685178086817714840373637)
                ·
                  refine ⟨315970891278321532570057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1685178086817714840373637 315970891278321532570057)
                  ·
                    rfl

theorem cell20_692270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_692270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692270 prefixEnd_692270 := by exact prefixLift 692270
  have htrace : WordTrace (prefixWord ++ tailWord_692270) baseStart_692270 baseEnd_692270 := by
    simpa [prefixWord, tailWord_692270, baseEnd_692270] using wordTrace_append hprefix tailTrace_692270
  have hstable : (prefixWord ++ tailWord_692270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692270).length < 2 ^ (prefixWord ++ tailWord_692270).sum := by decide
  have hdescent : baseEnd_692270 < baseStart_692270 := by decide
  rcases family_descends (prefixWord ++ tailWord_692270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692280 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_692280 : Nat := 118140960795 + 692280 * 2 ^ 59
def prefixEnd_692280 : Nat := 4983230072969 + 3 ^ 40 * 692280 * 2
def baseEnd_692280 : Nat := 315975455550805942236683

theorem tailTrace_692280 : CollatzResearch.WordTrace tailWord_692280 prefixEnd_692280 315975455550805942236683 := by
  unfold tailWord_692280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624762965997633428089147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16833017287996844570785529 12624762965997633428089147)
  ·
    refine ⟨18937144448996450142133721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12624762965997633428089147 18937144448996450142133721)
    ·
      refine ⟨14202858336747337606600291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18937144448996450142133721 14202858336747337606600291)
      ·
        refine ⟨21304287505121006409900437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14202858336747337606600291 21304287505121006409900437)
        ·
          refine ⟨998638476802547175464083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21304287505121006409900437 998638476802547175464083)
          ·
            refine ⟨1497957715203820763196125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998638476802547175464083 1497957715203820763196125)
            ·
              refine ⟨561734143201432786198547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1497957715203820763196125 561734143201432786198547)
              ·
                refine ⟨842601214802149179297821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561734143201432786198547 842601214802149179297821)
                ·
                  refine ⟨315975455550805942236683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842601214802149179297821 315975455550805942236683)
                  ·
                    rfl

theorem cell20_692280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_692280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692280 prefixEnd_692280 := by exact prefixLift 692280
  have htrace : WordTrace (prefixWord ++ tailWord_692280) baseStart_692280 baseEnd_692280 := by
    simpa [prefixWord, tailWord_692280, baseEnd_692280] using wordTrace_append hprefix tailTrace_692280
  have hstable : (prefixWord ++ tailWord_692280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692280).length < 2 ^ (prefixWord ++ tailWord_692280).sum := by decide
  have hdescent : baseEnd_692280 < baseStart_692280 := by decide
  rcases family_descends (prefixWord ++ tailWord_692280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692294 : List Nat := [6, 1, 1, 1, 1, 1, 3, 6]
def baseStart_692294 : Nat := 118140960795 + 692294 * 2 ^ 59
def prefixEnd_692294 : Nat := 4983230072969 + 3 ^ 40 * 692294 * 2
def baseEnd_692294 : Nat := 105327281844094705256653

theorem tailTrace_692294 : CollatzResearch.WordTrace tailWord_692294 prefixEnd_692294 105327281844094705256653 := by
  unfold tailWord_692294
  simp only [CollatzResearch.WordTrace]
  refine ⟨789063642310767101474623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16833357702629698164791957 789063642310767101474623)
  ·
    refine ⟨1183595463466150652211935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 789063642310767101474623 1183595463466150652211935)
    ·
      refine ⟨1775393195199225978317903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183595463466150652211935 1775393195199225978317903)
      ·
        refine ⟨2663089792798838967476855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775393195199225978317903 2663089792798838967476855)
        ·
          refine ⟨3994634689198258451215283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2663089792798838967476855 3994634689198258451215283)
          ·
            refine ⟨5991952033797387676822925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994634689198258451215283 5991952033797387676822925)
            ·
              refine ⟨2246982012674020378808597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5991952033797387676822925 2246982012674020378808597)
              ·
                refine ⟨105327281844094705256653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2246982012674020378808597 105327281844094705256653)
                ·
                  rfl

theorem cell20_692294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_692294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692294 prefixEnd_692294 := by exact prefixLift 692294
  have htrace : WordTrace (prefixWord ++ tailWord_692294) baseStart_692294 baseEnd_692294 := by
    simpa [prefixWord, tailWord_692294, baseEnd_692294] using wordTrace_append hprefix tailTrace_692294
  have hstable : (prefixWord ++ tailWord_692294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692294).length < 2 ^ (prefixWord ++ tailWord_692294).sum := by decide
  have hdescent : baseEnd_692294 < baseStart_692294 := by decide
  rcases family_descends (prefixWord ++ tailWord_692294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692336 : List Nat := [2, 1, 1, 1, 5, 2, 1, 7]
def baseStart_692336 : Nat := 118140960795 + 692336 * 2 ^ 59
def prefixEnd_692336 : Nat := 4983230072969 + 3 ^ 40 * 692336 * 2
def baseEnd_692336 : Nat := 105333671825572878789929

theorem tailTrace_692336 : CollatzResearch.WordTrace tailWord_692336 prefixEnd_692336 105333671825572878789929 := by
  unfold tailWord_692336
  simp only [CollatzResearch.WordTrace]
  refine ⟨12625784209896194210108431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16834378946528258946811241 12625784209896194210108431)
  ·
    refine ⟨18938676314844291315162647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12625784209896194210108431 18938676314844291315162647)
    ·
      refine ⟨28408014472266436972743971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18938676314844291315162647 28408014472266436972743971)
      ·
        refine ⟨42612021708399655459115957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28408014472266436972743971 42612021708399655459115957)
        ·
          refine ⟨3994877035162467699292121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42612021708399655459115957 3994877035162467699292121)
          ·
            refine ⟨2996157776371850774469091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3994877035162467699292121 2996157776371850774469091)
            ·
              refine ⟨4494236664557776161703637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996157776371850774469091 4494236664557776161703637)
              ·
                refine ⟨105333671825572878789929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4494236664557776161703637 105333671825572878789929)
                ·
                  rfl

theorem cell20_692336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_692336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692336 prefixEnd_692336 := by exact prefixLift 692336
  have htrace : WordTrace (prefixWord ++ tailWord_692336) baseStart_692336 baseEnd_692336 := by
    simpa [prefixWord, tailWord_692336, baseEnd_692336] using wordTrace_append hprefix tailTrace_692336
  have hstable : (prefixWord ++ tailWord_692336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692336).length < 2 ^ (prefixWord ++ tailWord_692336).sum := by decide
  have hdescent : baseEnd_692336 < baseStart_692336 := by decide
  rcases family_descends (prefixWord ++ tailWord_692336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692484 : List Nat := [2, 3, 2, 2, 4, 1, 6]
def baseStart_692484 : Nat := 118140960795 + 692484 * 2 ^ 59
def prefixEnd_692484 : Nat := 4983230072969 + 3 ^ 40 * 692484 * 2
def baseEnd_692484 : Nat := 35118729634387544381761

theorem tailTrace_692484 : CollatzResearch.WordTrace tailWord_692484 prefixEnd_692484 35118729634387544381761 := by
  unfold tailWord_692484
  simp only [CollatzResearch.WordTrace]
  refine ⟨12628483211628104848302253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16837977615504139797736337 12628483211628104848302253)
  ·
    refine ⟨4735681204360539318113345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12628483211628104848302253 4735681204360539318113345)
    ·
      refine ⟨3551760903270404488585009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4735681204360539318113345 3551760903270404488585009)
      ·
        refine ⟨2663820677452803366438757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3551760903270404488585009 2663820677452803366438757)
        ·
          refine ⟨499466377022400631207267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2663820677452803366438757 499466377022400631207267)
          ·
            refine ⟨749199565533600946810901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499466377022400631207267 749199565533600946810901)
            ·
              refine ⟨35118729634387544381761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 749199565533600946810901 35118729634387544381761)
              ·
                rfl

theorem cell20_692484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 6].length) (baseStart_692484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692484 prefixEnd_692484 := by exact prefixLift 692484
  have htrace : WordTrace (prefixWord ++ tailWord_692484) baseStart_692484 baseEnd_692484 := by
    simpa [prefixWord, tailWord_692484, baseEnd_692484] using wordTrace_append hprefix tailTrace_692484
  have hstable : (prefixWord ++ tailWord_692484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692484).length < 2 ^ (prefixWord ++ tailWord_692484).sum := by decide
  have hdescent : baseEnd_692484 < baseStart_692484 := by decide
  rcases family_descends (prefixWord ++ tailWord_692484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692488 : List Nat := [2, 1, 3, 2, 3, 1, 8]
def baseStart_692488 : Nat := 118140960795 + 692488 * 2 ^ 59
def prefixEnd_692488 : Nat := 4983230072969 + 3 ^ 40 * 692488 * 2
def baseEnd_692488 : Nat := 35118932490942407033611

theorem tailTrace_692488 : CollatzResearch.WordTrace tailWord_692488 prefixEnd_692488 35118932490942407033611 := by
  unfold tailWord_692488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12628556157620859189875059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16838074876827812253166745 12628556157620859189875059)
  ·
    refine ⟨18942834236431288784812589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12628556157620859189875059 18942834236431288784812589)
    ·
      refine ⟨7103562838661733294304721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18942834236431288784812589 7103562838661733294304721)
      ·
        refine ⟨5327672128996299970728541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7103562838661733294304721 5327672128996299970728541)
        ·
          refine ⟨1997877048373612489023203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5327672128996299970728541 1997877048373612489023203)
          ·
            refine ⟨2996815572560418733534805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997877048373612489023203 2996815572560418733534805)
            ·
              refine ⟨35118932490942407033611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2996815572560418733534805 35118932490942407033611)
              ·
                rfl

theorem cell20_692488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 8].length) (baseStart_692488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692488 prefixEnd_692488 := by exact prefixLift 692488
  have htrace : WordTrace (prefixWord ++ tailWord_692488) baseStart_692488 baseEnd_692488 := by
    simpa [prefixWord, tailWord_692488, baseEnd_692488] using wordTrace_append hprefix tailTrace_692488
  have hstable : (prefixWord ++ tailWord_692488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692488).length < 2 ^ (prefixWord ++ tailWord_692488).sum := by decide
  have hdescent : baseEnd_692488 < baseStart_692488 := by decide
  rcases family_descends (prefixWord ++ tailWord_692488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692581 : List Nat := [1, 3, 1, 3, 1, 4, 3, 4]
def baseStart_692581 : Nat := 118140960795 + 692581 * 2 ^ 59
def prefixEnd_692581 : Nat := 4983230072969 + 3 ^ 40 * 692581 * 2
def baseEnd_692581 : Nat := 105370946717528891067373

theorem tailTrace_692581 : CollatzResearch.WordTrace tailWord_692581 prefixEnd_692581 105370946717528891067373 := by
  unfold tailWord_692581
  simp only [CollatzResearch.WordTrace]
  refine ⟨25260504303904795262885597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16840336202603196841923731 25260504303904795262885597)
  ·
    refine ⟨9472689113964298223582099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25260504303904795262885597 9472689113964298223582099)
    ·
      refine ⟨14209033670946447335373149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9472689113964298223582099 14209033670946447335373149)
      ·
        refine ⟨5328387626604917750764931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14209033670946447335373149 5328387626604917750764931)
        ·
          refine ⟨7992581439907376626147397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328387626604917750764931 7992581439907376626147397)
          ·
            refine ⟨1498609019982633117402637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7992581439907376626147397 1498609019982633117402637)
            ·
              refine ⟨561978382493487419025989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1498609019982633117402637 561978382493487419025989)
              ·
                refine ⟨105370946717528891067373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561978382493487419025989 105370946717528891067373)
                ·
                  rfl

theorem cell20_692581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_692581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692581 prefixEnd_692581 := by exact prefixLift 692581
  have htrace : WordTrace (prefixWord ++ tailWord_692581) baseStart_692581 baseEnd_692581 := by
    simpa [prefixWord, tailWord_692581, baseEnd_692581] using wordTrace_append hprefix tailTrace_692581
  have hstable : (prefixWord ++ tailWord_692581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692581).length < 2 ^ (prefixWord ++ tailWord_692581).sum := by decide
  have hdescent : baseEnd_692581 < baseStart_692581 := by decide
  rcases family_descends (prefixWord ++ tailWord_692581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692598 : List Nat := [5, 1, 1, 4, 1, 1, 7]
def baseStart_692598 : Nat := 118140960795 + 692598 * 2 ^ 59
def prefixEnd_692598 : Nat := 4983230072969 + 3 ^ 40 * 692598 * 2
def baseEnd_692598 : Nat := 35124511046201129959487

theorem tailTrace_692598 : CollatzResearch.WordTrace tailWord_692598 prefixEnd_692598 35124511046201129959487 := by
  unfold tailWord_692598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578820271552700447890903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16840749563228804777502965 1578820271552700447890903)
  ·
    refine ⟨2368230407329050671836355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1578820271552700447890903 2368230407329050671836355)
    ·
      refine ⟨3552345610993576007754533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368230407329050671836355 3552345610993576007754533)
      ·
        refine ⟨666064802061295501453975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3552345610993576007754533 666064802061295501453975)
        ·
          refine ⟨999097203091943252180963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666064802061295501453975 999097203091943252180963)
          ·
            refine ⟨1498645804637914878271445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999097203091943252180963 1498645804637914878271445)
            ·
              refine ⟨35124511046201129959487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1498645804637914878271445 35124511046201129959487)
              ·
                rfl

theorem cell20_692598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 7].length) (baseStart_692598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692598 prefixEnd_692598 := by exact prefixLift 692598
  have htrace : WordTrace (prefixWord ++ tailWord_692598) baseStart_692598 baseEnd_692598 := by
    simpa [prefixWord, tailWord_692598, baseEnd_692598] using wordTrace_append hprefix tailTrace_692598
  have hstable : (prefixWord ++ tailWord_692598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692598).length < 2 ^ (prefixWord ++ tailWord_692598).sum := by decide
  have hdescent : baseEnd_692598 < baseStart_692598 := by decide
  rcases family_descends (prefixWord ++ tailWord_692598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692605 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 3]
def baseStart_692605 : Nat := 118140960795 + 692605 * 2 ^ 59
def prefixEnd_692605 : Nat := 4983230072969 + 3 ^ 40 * 692605 * 2
def baseEnd_692605 : Nat := 316123794406549256402021

theorem tailTrace_692605 : CollatzResearch.WordTrace tailWord_692605 prefixEnd_692605 316123794406549256402021 := by
  unfold tailWord_692605
  simp only [CollatzResearch.WordTrace]
  refine ⟨25261379655817847361759269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16840919770545231574506179 25261379655817847361759269)
  ·
    refine ⟨4736508685465846380329863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25261379655817847361759269 4736508685465846380329863)
    ·
      refine ⟨7104763028198769570494795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4736508685465846380329863 7104763028198769570494795)
      ·
        refine ⟨10657144542298154355742193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7104763028198769570494795 10657144542298154355742193)
        ·
          refine ⟨7992858406723615766806645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10657144542298154355742193 7992858406723615766806645)
          ·
            refine ⟨749330475630338978138123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7992858406723615766806645 749330475630338978138123)
            ·
              refine ⟨1123995713445508467207185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749330475630338978138123 1123995713445508467207185)
              ·
                refine ⟨842996785084131350405389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123995713445508467207185 842996785084131350405389)
                ·
                  refine ⟨316123794406549256402021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842996785084131350405389 316123794406549256402021)
                  ·
                    rfl

theorem cell20_692605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_692605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692605 prefixEnd_692605 := by exact prefixLift 692605
  have htrace : WordTrace (prefixWord ++ tailWord_692605) baseStart_692605 baseEnd_692605 := by
    simpa [prefixWord, tailWord_692605, baseEnd_692605] using wordTrace_append hprefix tailTrace_692605
  have hstable : (prefixWord ++ tailWord_692605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692605).length < 2 ^ (prefixWord ++ tailWord_692605).sum := by decide
  have hdescent : baseEnd_692605 < baseStart_692605 := by decide
  rcases family_descends (prefixWord ++ tailWord_692605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692612 : List Nat := [2, 3, 2, 1, 1, 2, 1, 6, 2]
def baseStart_692612 : Nat := 118140960795 + 692612 * 2 ^ 59
def prefixEnd_692612 : Nat := 4983230072969 + 3 ^ 40 * 692612 * 2
def baseEnd_692612 : Nat := 316126989397288343168659

theorem tailTrace_692612 : CollatzResearch.WordTrace tailWord_692612 prefixEnd_692612 316126989397288343168659 := by
  unfold tailWord_692612
  simp only [CollatzResearch.WordTrace]
  refine ⟨12630817483396243778632045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16841089977861658371509393 12630817483396243778632045)
  ·
    refine ⟨4736556556273591416987017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12630817483396243778632045 4736556556273591416987017)
    ·
      refine ⟨3552417417205193562740263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4736556556273591416987017 3552417417205193562740263)
      ·
        refine ⟨5328626125807790344110395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552417417205193562740263 5328626125807790344110395)
        ·
          refine ⟨7992939188711685516165593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328626125807790344110395 7992939188711685516165593)
          ·
            refine ⟨5994704391533764137124195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7992939188711685516165593 5994704391533764137124195)
            ·
              refine ⟨8992056587300646205686293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5994704391533764137124195 8992056587300646205686293)
              ·
                refine ⟨421502652529717790891545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8992056587300646205686293 421502652529717790891545)
                ·
                  refine ⟨316126989397288343168659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421502652529717790891545 316126989397288343168659)
                  ·
                    rfl

theorem cell20_692612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_692612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692612 prefixEnd_692612 := by exact prefixLift 692612
  have htrace : WordTrace (prefixWord ++ tailWord_692612) baseStart_692612 baseEnd_692612 := by
    simpa [prefixWord, tailWord_692612, baseEnd_692612] using wordTrace_append hprefix tailTrace_692612
  have hstable : (prefixWord ++ tailWord_692612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692612).length < 2 ^ (prefixWord ++ tailWord_692612).sum := by decide
  have hdescent : baseEnd_692612 < baseStart_692612 := by decide
  rcases family_descends (prefixWord ++ tailWord_692612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692622 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_692622 : Nat := 118140960795 + 692622 * 2 ^ 59
def prefixEnd_692622 : Nat := 4983230072969 + 3 ^ 40 * 692622 * 2
def baseEnd_692622 : Nat := 316131553669772752835285

theorem tailTrace_692622 : CollatzResearch.WordTrace tailWord_692622 prefixEnd_692622 316131553669772752835285 := by
  unfold tailWord_692622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157749962094532408141015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16841333131170839510085413 3157749962094532408141015)
  ·
    refine ⟨4736624943141798612211523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3157749962094532408141015 4736624943141798612211523)
    ·
      refine ⟨7104937414712697918317285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4736624943141798612211523 7104937414712697918317285)
      ·
        refine ⟨1332175765258630859684491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7104937414712697918317285 1332175765258630859684491)
        ·
          refine ⟨1998263647887946289526737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332175765258630859684491 1998263647887946289526737)
          ·
            refine ⟨1498697735915959717145053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998263647887946289526737 1498697735915959717145053)
            ·
              refine ⟨562011650968484893929395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1498697735915959717145053 562011650968484893929395)
              ·
                refine ⟨843017476452727340894093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562011650968484893929395 843017476452727340894093)
                ·
                  refine ⟨316131553669772752835285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843017476452727340894093 316131553669772752835285)
                  ·
                    rfl

theorem cell20_692622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_692622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692622 prefixEnd_692622 := by exact prefixLift 692622
  have htrace : WordTrace (prefixWord ++ tailWord_692622) baseStart_692622 baseEnd_692622 := by
    simpa [prefixWord, tailWord_692622, baseEnd_692622] using wordTrace_append hprefix tailTrace_692622
  have hstable : (prefixWord ++ tailWord_692622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692622).length < 2 ^ (prefixWord ++ tailWord_692622).sum := by decide
  have hdescent : baseEnd_692622 < baseStart_692622 := by decide
  rcases family_descends (prefixWord ++ tailWord_692622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692640 : List Nat := [2, 1, 1, 4, 1, 4, 1, 6]
def baseStart_692640 : Nat := 118140960795 + 692640 * 2 ^ 59
def prefixEnd_692640 : Nat := 4983230072969 + 3 ^ 40 * 692640 * 2
def baseEnd_692640 : Nat := 105379923120081563411737

theorem tailTrace_692640 : CollatzResearch.WordTrace tailWord_692640 prefixEnd_692640 105379923120081563411737 := by
  unfold tailWord_692640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12631328105345524169641687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16841770807127365559522249 12631328105345524169641687)
  ·
    refine ⟨18946992158018286254462531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12631328105345524169641687 18946992158018286254462531)
    ·
      refine ⟨28420488237027429381693797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18946992158018286254462531 28420488237027429381693797)
      ·
        refine ⟨5328841544442643009067587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28420488237027429381693797 5328841544442643009067587)
        ·
          refine ⟨7993262316663964513601381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328841544442643009067587 7993262316663964513601381)
          ·
            refine ⟨1498736684374493346300259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7993262316663964513601381 1498736684374493346300259)
            ·
              refine ⟨2248105026561740019450389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498736684374493346300259 2248105026561740019450389)
              ·
                refine ⟨105379923120081563411737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2248105026561740019450389 105379923120081563411737)
                ·
                  rfl

theorem cell20_692640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_692640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692640 prefixEnd_692640 := by exact prefixLift 692640
  have htrace : WordTrace (prefixWord ++ tailWord_692640) baseStart_692640 baseEnd_692640 := by
    simpa [prefixWord, tailWord_692640, baseEnd_692640] using wordTrace_append hprefix tailTrace_692640
  have hstable : (prefixWord ++ tailWord_692640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692640).length < 2 ^ (prefixWord ++ tailWord_692640).sum := by decide
  have hdescent : baseEnd_692640 < baseStart_692640 := by decide
  rcases family_descends (prefixWord ++ tailWord_692640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692673 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 3]
def baseStart_692673 : Nat := 118140960795 + 692673 * 2 ^ 59
def prefixEnd_692673 : Nat := 4983230072969 + 3 ^ 40 * 692673 * 2
def baseEnd_692673 : Nat := 316154831459443242135077

theorem tailTrace_692673 : CollatzResearch.WordTrace tailWord_692673 prefixEnd_692673 316154831459443242135077 := by
  unfold tailWord_692673
  simp only [CollatzResearch.WordTrace]
  refine ⟨25263859819571494975234673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16842573213047663316823115 25263859819571494975234673)
  ·
    refine ⟨18947894864678621231426005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25263859819571494975234673 18947894864678621231426005)
    ·
      refine ⟨444091285890905185111547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18947894864678621231426005 444091285890905185111547)
      ·
        refine ⟨666136928836357777667321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444091285890905185111547 666136928836357777667321)
        ·
          refine ⟨499602696627268333250491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666136928836357777667321 499602696627268333250491)
          ·
            refine ⟨749404044940902499875737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499602696627268333250491 749404044940902499875737)
            ·
              refine ⟨562053033705676874906803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749404044940902499875737 562053033705676874906803)
              ·
                refine ⟨843079550558515312360205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562053033705676874906803 843079550558515312360205)
                ·
                  refine ⟨316154831459443242135077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843079550558515312360205 316154831459443242135077)
                  ·
                    rfl

theorem cell20_692673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_692673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692673 prefixEnd_692673 := by exact prefixLift 692673
  have htrace : WordTrace (prefixWord ++ tailWord_692673) baseStart_692673 baseEnd_692673 := by
    simpa [prefixWord, tailWord_692673, baseEnd_692673] using wordTrace_append hprefix tailTrace_692673
  have hstable : (prefixWord ++ tailWord_692673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692673).length < 2 ^ (prefixWord ++ tailWord_692673).sum := by decide
  have hdescent : baseEnd_692673 < baseStart_692673 := by decide
  rcases family_descends (prefixWord ++ tailWord_692673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692747 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_692747 : Nat := 118140960795 + 692747 * 2 ^ 59
def prefixEnd_692747 : Nat := 4983230072969 + 3 ^ 40 * 692747 * 2
def baseEnd_692747 : Nat := 316188607075827873668107

theorem tailTrace_692747 : CollatzResearch.WordTrace tailWord_692747 prefixEnd_692747 316188607075827873668107 := by
  unfold tailWord_692747
  simp only [CollatzResearch.WordTrace]
  refine ⟨25266558821303405613428495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16844372547535603742285663 25266558821303405613428495)
  ·
    refine ⟨37899838231955108420142743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25266558821303405613428495 37899838231955108420142743)
    ·
      refine ⟨56849757347932662630214115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37899838231955108420142743 56849757347932662630214115)
      ·
        refine ⟨85274636021898993945321173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56849757347932662630214115 85274636021898993945321173)
        ·
          refine ⟨1998624281763257670593465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85274636021898993945321173 1998624281763257670593465)
          ·
            refine ⟨1498968211322443252945099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998624281763257670593465 1498968211322443252945099)
            ·
              refine ⟨2248452316983664879417649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498968211322443252945099 2248452316983664879417649)
              ·
                refine ⟨1686339237737748659563237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248452316983664879417649 1686339237737748659563237)
                ·
                  refine ⟨316188607075827873668107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686339237737748659563237 316188607075827873668107)
                  ·
                    rfl

theorem cell20_692747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_692747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692747 prefixEnd_692747 := by exact prefixLift 692747
  have htrace : WordTrace (prefixWord ++ tailWord_692747) baseStart_692747 baseEnd_692747 := by
    simpa [prefixWord, tailWord_692747, baseEnd_692747] using wordTrace_append hprefix tailTrace_692747
  have hstable : (prefixWord ++ tailWord_692747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692747).length < 2 ^ (prefixWord ++ tailWord_692747).sum := by decide
  have hdescent : baseEnd_692747 < baseStart_692747 := by decide
  rcases family_descends (prefixWord ++ tailWord_692747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692764 : List Nat := [2, 2, 3, 1, 2, 2, 1, 5, 2]
def baseStart_692764 : Nat := 118140960795 + 692764 * 2 ^ 59
def prefixEnd_692764 : Nat := 4983230072969 + 3 ^ 40 * 692764 * 2
def baseEnd_692764 : Nat := 316196366339051370101371

theorem tailTrace_692764 : CollatzResearch.WordTrace tailWord_692764 prefixEnd_692764 316196366339051370101371 := by
  unfold tailWord_692764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12633589431120908758398673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16844785908161211677864897 12633589431120908758398673)
  ·
    refine ⟨9475192073340681568799005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12633589431120908758398673 9475192073340681568799005)
    ·
      refine ⟨3553197027502755588299627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9475192073340681568799005 3553197027502755588299627)
      ·
        refine ⟨5329795541254133382449441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553197027502755588299627 5329795541254133382449441)
        ·
          refine ⟨3997346655940600036837081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5329795541254133382449441 3997346655940600036837081)
          ·
            refine ⟨2998009991955450027627811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3997346655940600036837081 2998009991955450027627811)
            ·
              refine ⟨4497014987933175041441717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998009991955450027627811 4497014987933175041441717)
              ·
                refine ⟨421595155118735160135161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4497014987933175041441717 421595155118735160135161)
                ·
                  refine ⟨316196366339051370101371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421595155118735160135161 316196366339051370101371)
                  ·
                    rfl

theorem cell20_692764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_692764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692764 prefixEnd_692764 := by exact prefixLift 692764
  have htrace : WordTrace (prefixWord ++ tailWord_692764) baseStart_692764 baseEnd_692764 := by
    simpa [prefixWord, tailWord_692764, baseEnd_692764] using wordTrace_append hprefix tailTrace_692764
  have hstable : (prefixWord ++ tailWord_692764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692764).length < 2 ^ (prefixWord ++ tailWord_692764).sum := by decide
  have hdescent : baseEnd_692764 < baseStart_692764 := by decide
  rcases family_descends (prefixWord ++ tailWord_692764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692778 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_692778 : Nat := 118140960795 + 692778 * 2 ^ 59
def prefixEnd_692778 : Nat := 4983230072969 + 3 ^ 40 * 692778 * 2
def baseEnd_692778 : Nat := 316202756320529543634647

theorem tailTrace_692778 : CollatzResearch.WordTrace tailWord_692778 prefixEnd_692778 316202756320529543634647 := by
  unfold tailWord_692778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316922371047774476951747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16845126322794065271871325 6316922371047774476951747)
  ·
    refine ⟨9475383556571661715427621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6316922371047774476951747 9475383556571661715427621)
    ·
      refine ⟨1776634416857186571642679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9475383556571661715427621 1776634416857186571642679)
      ·
        refine ⟨2664951625285779857464019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776634416857186571642679 2664951625285779857464019)
        ·
          refine ⟨3997427437928669786196029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664951625285779857464019 3997427437928669786196029)
          ·
            refine ⟨1499035289223251169823511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3997427437928669786196029 1499035289223251169823511)
            ·
              refine ⟨2248552933834876754735267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499035289223251169823511 2248552933834876754735267)
              ·
                refine ⟨3372829400752315132102901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248552933834876754735267 3372829400752315132102901)
                ·
                  refine ⟨316202756320529543634647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3372829400752315132102901 316202756320529543634647)
                  ·
                    rfl

theorem cell20_692778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_692778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692778 prefixEnd_692778 := by exact prefixLift 692778
  have htrace : WordTrace (prefixWord ++ tailWord_692778) baseStart_692778 baseEnd_692778 := by
    simpa [prefixWord, tailWord_692778, baseEnd_692778] using wordTrace_append hprefix tailTrace_692778
  have hstable : (prefixWord ++ tailWord_692778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692778).length < 2 ^ (prefixWord ++ tailWord_692778).sum := by decide
  have hdescent : baseEnd_692778 < baseStart_692778 := by decide
  rcases family_descends (prefixWord ++ tailWord_692778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692850 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_692850 : Nat := 118140960795 + 692850 * 2 ^ 59
def prefixEnd_692850 : Nat := 4983230072969 + 3 ^ 40 * 692850 * 2
def baseEnd_692850 : Nat := 316235619082417293234353

theorem tailTrace_692850 : CollatzResearch.WordTrace tailWord_692850 prefixEnd_692850 316235619082417293234353 := by
  unfold tailWord_692850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317578884982563551107001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16846877026620169469618669 6317578884982563551107001)
  ·
    refine ⟨4738184163736922663330251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6317578884982563551107001 4738184163736922663330251)
    ·
      refine ⟨7107276245605383994995377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4738184163736922663330251 7107276245605383994995377)
      ·
        refine ⟨5330457184204037996246533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7107276245605383994995377 5330457184204037996246533)
        ·
          refine ⟨999460722038257124296225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5330457184204037996246533 999460722038257124296225)
          ·
            refine ⟨749595541528692843222169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999460722038257124296225 749595541528692843222169)
            ·
              refine ⟨562196656146519632416627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749595541528692843222169 562196656146519632416627)
              ·
                refine ⟨843294984219779448624941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562196656146519632416627 843294984219779448624941)
                ·
                  refine ⟨316235619082417293234353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843294984219779448624941 316235619082417293234353)
                  ·
                    rfl

theorem cell20_692850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_692850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692850 prefixEnd_692850 := by exact prefixLift 692850
  have htrace : WordTrace (prefixWord ++ tailWord_692850) baseStart_692850 baseEnd_692850 := by
    simpa [prefixWord, tailWord_692850, baseEnd_692850] using wordTrace_append hprefix tailTrace_692850
  have hstable : (prefixWord ++ tailWord_692850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692850).length < 2 ^ (prefixWord ++ tailWord_692850).sum := by decide
  have hdescent : baseEnd_692850 < baseStart_692850 := by decide
  rcases family_descends (prefixWord ++ tailWord_692850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692868 : List Nat := [2, 3, 2, 1, 3, 1, 2, 6]
def baseStart_692868 : Nat := 118140960795 + 692868 * 2 ^ 59
def prefixEnd_692868 : Nat := 4983230072969 + 3 ^ 40 * 692868 * 2
def baseEnd_692868 : Nat := 105414611590963076878093

theorem tailTrace_692868 : CollatzResearch.WordTrace tailWord_692868 prefixEnd_692868 105414611590963076878093 := by
  unfold tailWord_692868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635486026932521639291629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16847314702576695519055505 12635486026932521639291629)
  ·
    refine ⟨4738307260099695614734361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12635486026932521639291629 4738307260099695614734361)
    ·
      refine ⟨3553730445074771711050771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4738307260099695614734361 3553730445074771711050771)
      ·
        refine ⟨5330595667612157566576157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553730445074771711050771 5330595667612157566576157)
        ·
          refine ⟨1998973375354559087466059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5330595667612157566576157 1998973375354559087466059)
          ·
            refine ⟨2998460063031838631199089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998973375354559087466059 2998460063031838631199089)
            ·
              refine ⟨2248845047273878973399317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998460063031838631199089 2248845047273878973399317)
              ·
                refine ⟨105414611590963076878093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2248845047273878973399317 105414611590963076878093)
                ·
                  rfl

theorem cell20_692868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_692868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692868 prefixEnd_692868 := by exact prefixLift 692868
  have htrace : WordTrace (prefixWord ++ tailWord_692868) baseStart_692868 baseEnd_692868 := by
    simpa [prefixWord, tailWord_692868, baseEnd_692868] using wordTrace_append hprefix tailTrace_692868
  have hstable : (prefixWord ++ tailWord_692868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692868).length < 2 ^ (prefixWord ++ tailWord_692868).sum := by decide
  have hdescent : baseEnd_692868 < baseStart_692868 := by decide
  rcases family_descends (prefixWord ++ tailWord_692868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692878 : List Nat := [4, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_692878 : Nat := 118140960795 + 692878 * 2 ^ 59
def prefixEnd_692878 : Nat := 4983230072969 + 3 ^ 40 * 692878 * 2
def baseEnd_692878 : Nat := 316248399045373640300905

theorem tailTrace_692878 : CollatzResearch.WordTrace tailWord_692878 prefixEnd_692878 316248399045373640300905 := by
  unfold tailWord_692878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3158917097978601873305911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16847557855885876657631525 3158917097978601873305911)
  ·
    refine ⟨4738375646967902809958867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3158917097978601873305911 4738375646967902809958867)
    ·
      refine ⟨7107563470451854214938301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4738375646967902809958867 7107563470451854214938301)
      ·
        refine ⟨2665336301419445330601863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7107563470451854214938301 2665336301419445330601863)
        ·
          refine ⟨3998004452129167995902795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665336301419445330601863 3998004452129167995902795)
          ·
            refine ⟨5997006678193751993854193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3998004452129167995902795 5997006678193751993854193)
            ·
              refine ⟨4497755008645313995390645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5997006678193751993854193 4497755008645313995390645)
              ·
                refine ⟨421664532060498187067873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4497755008645313995390645 421664532060498187067873)
                ·
                  refine ⟨316248399045373640300905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421664532060498187067873 316248399045373640300905)
                  ·
                    rfl

theorem cell20_692878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_692878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692878 prefixEnd_692878 := by exact prefixLift 692878
  have htrace : WordTrace (prefixWord ++ tailWord_692878) baseStart_692878 baseEnd_692878 := by
    simpa [prefixWord, tailWord_692878, baseEnd_692878] using wordTrace_append hprefix tailTrace_692878
  have hstable : (prefixWord ++ tailWord_692878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692878).length < 2 ^ (prefixWord ++ tailWord_692878).sum := by decide
  have hdescent : baseEnd_692878 < baseStart_692878 := by decide
  rcases family_descends (prefixWord ++ tailWord_692878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692892 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_692892 : Nat := 118140960795 + 692892 * 2 ^ 59
def prefixEnd_692892 : Nat := 4983230072969 + 3 ^ 40 * 692892 * 2
def baseEnd_692892 : Nat := 316254789026851813834181

theorem tailTrace_692892 : CollatzResearch.WordTrace tailWord_692892 prefixEnd_692892 316254789026851813834181 := by
  unfold tailWord_692892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635923702889047688728465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16847898270518730251637953 12635923702889047688728465)
  ·
    refine ⟨9476942777166785766546349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12635923702889047688728465 9476942777166785766546349)
    ·
      refine ⟨3553853541437544662454881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9476942777166785766546349 3553853541437544662454881)
      ·
        refine ⟨2665390156078158496841161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3553853541437544662454881 2665390156078158496841161)
        ·
          refine ⟨1999042617058618872630871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665390156078158496841161 1999042617058618872630871)
          ·
            refine ⟨2998563925587928308946307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999042617058618872630871 2998563925587928308946307)
            ·
              refine ⟨4497845888381892463419461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998563925587928308946307 4497845888381892463419461)
              ·
                refine ⟨843346104071604836891149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4497845888381892463419461 843346104071604836891149)
                ·
                  refine ⟨316254789026851813834181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843346104071604836891149 316254789026851813834181)
                  ·
                    rfl

theorem cell20_692892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_692892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692892 prefixEnd_692892 := by exact prefixLift 692892
  have htrace : WordTrace (prefixWord ++ tailWord_692892) baseStart_692892 baseEnd_692892 := by
    simpa [prefixWord, tailWord_692892, baseEnd_692892] using wordTrace_append hprefix tailTrace_692892
  have hstable : (prefixWord ++ tailWord_692892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692892).length < 2 ^ (prefixWord ++ tailWord_692892).sum := by decide
  have hdescent : baseEnd_692892 < baseStart_692892 := by decide
  rcases family_descends (prefixWord ++ tailWord_692892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692951 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_692951 : Nat := 118140960795 + 692951 * 2 ^ 59
def prefixEnd_692951 : Nat := 4983230072969 + 3 ^ 40 * 692951 * 2
def baseEnd_692951 : Nat := 316281718234509830867273

theorem tailTrace_692951 : CollatzResearch.WordTrace tailWord_692951 prefixEnd_692951 316281718234509830867273 := by
  unfold tailWord_692951
  simp only [CollatzResearch.WordTrace]
  refine ⟨25273999312564348453854707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16849332875042898969236471 25273999312564348453854707)
  ·
    refine ⟨37910998968846522680782061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25273999312564348453854707 37910998968846522680782061)
    ·
      refine ⟨14216624613317446005293273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37910998968846522680782061 14216624613317446005293273)
      ·
        refine ⟨10662468459988084503969955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14216624613317446005293273 10662468459988084503969955)
        ·
          refine ⟨15993702689982126755954933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10662468459988084503969955 15993702689982126755954933)
          ·
            refine ⟨1499409627185824383370775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15993702689982126755954933 1499409627185824383370775)
            ·
              refine ⟨2249114440778736575056163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499409627185824383370775 2249114440778736575056163)
              ·
                refine ⟨3373671661168104862584245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249114440778736575056163 3373671661168104862584245)
                ·
                  refine ⟨316281718234509830867273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3373671661168104862584245 316281718234509830867273)
                  ·
                    rfl

theorem cell20_692951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_692951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692951 prefixEnd_692951 := by exact prefixLift 692951
  have htrace : WordTrace (prefixWord ++ tailWord_692951) baseStart_692951 baseEnd_692951 := by
    simpa [prefixWord, tailWord_692951, baseEnd_692951] using wordTrace_append hprefix tailTrace_692951
  have hstable : (prefixWord ++ tailWord_692951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692951).length < 2 ^ (prefixWord ++ tailWord_692951).sum := by decide
  have hdescent : baseEnd_692951 < baseStart_692951 := by decide
  rcases family_descends (prefixWord ++ tailWord_692951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692982 : List Nat := [5, 1, 1, 1, 1, 2, 3, 6]
def baseStart_692982 : Nat := 118140960795 + 692982 * 2 ^ 59
def prefixEnd_692982 : Nat := 4983230072969 + 3 ^ 40 * 692982 * 2
def baseEnd_692982 : Nat := 105431955826403833611271

theorem tailTrace_692982 : CollatzResearch.WordTrace tailWord_692982 prefixEnd_692982 105431955826403833611271 := by
  unfold tailWord_692982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579695623465752546764575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16850086650301360498822133 1579695623465752546764575)
  ·
    refine ⟨2369543435198628820146863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1579695623465752546764575 2369543435198628820146863)
    ·
      refine ⟨3554315152797943230220295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2369543435198628820146863 3554315152797943230220295)
      ·
        refine ⟨5331472729196914845330443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554315152797943230220295 5331472729196914845330443)
        ·
          refine ⟨7997209093795372267995665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331472729196914845330443 7997209093795372267995665)
          ·
            refine ⟨5997906820346529200996749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7997209093795372267995665 5997906820346529200996749)
            ·
              refine ⟨2249215057629948450373781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5997906820346529200996749 2249215057629948450373781)
              ·
                refine ⟨105431955826403833611271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2249215057629948450373781 105431955826403833611271)
                ·
                  rfl

theorem cell20_692982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_692982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_692982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_692982 prefixEnd_692982 := by exact prefixLift 692982
  have htrace : WordTrace (prefixWord ++ tailWord_692982) baseStart_692982 baseEnd_692982 := by
    simpa [prefixWord, tailWord_692982, baseEnd_692982] using wordTrace_append hprefix tailTrace_692982
  have hstable : (prefixWord ++ tailWord_692982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692982).length < 2 ^ (prefixWord ++ tailWord_692982).sum := by decide
  have hdescent : baseEnd_692982 < baseStart_692982 := by decide
  rcases family_descends (prefixWord ++ tailWord_692982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693020 : List Nat := [2, 2, 3, 1, 1, 4, 2, 5]
def baseStart_693020 : Nat := 118140960795 + 693020 * 2 ^ 59
def prefixEnd_693020 : Nat := 4983230072969 + 3 ^ 40 * 693020 * 2
def baseEnd_693020 : Nat := 105437737238217419188997

theorem tailTrace_693020 : CollatzResearch.WordTrace tailWord_693020 prefixEnd_693020 105437737238217419188997 := by
  unfold tailWord_693020
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638257974657186619058257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16851010632876248825411009 12638257974657186619058257)
  ·
    refine ⟨9478693480992889964293693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12638257974657186619058257 9478693480992889964293693)
    ·
      refine ⟨3554510055372333736610135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9478693480992889964293693 3554510055372333736610135)
      ·
        refine ⟨5331765083058500604915203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554510055372333736610135 5331765083058500604915203)
        ·
          refine ⟨7997647624587750907372805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331765083058500604915203 7997647624587750907372805)
          ·
            refine ⟨1499558929610203295132401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7997647624587750907372805 1499558929610203295132401)
            ·
              refine ⟨1124669197207652471349301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1499558929610203295132401 1124669197207652471349301)
              ·
                refine ⟨105437737238217419188997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1124669197207652471349301 105437737238217419188997)
                ·
                  rfl

theorem cell20_693020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_693020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693020 prefixEnd_693020 := by exact prefixLift 693020
  have htrace : WordTrace (prefixWord ++ tailWord_693020) baseStart_693020 baseEnd_693020 := by
    simpa [prefixWord, tailWord_693020, baseEnd_693020] using wordTrace_append hprefix tailTrace_693020
  have hstable : (prefixWord ++ tailWord_693020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693020).length < 2 ^ (prefixWord ++ tailWord_693020).sum := by decide
  have hdescent : baseEnd_693020 < baseStart_693020 := by decide
  rcases family_descends (prefixWord ++ tailWord_693020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693023 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 3]
def baseStart_693023 : Nat := 118140960795 + 693023 * 2 ^ 59
def prefixEnd_693023 : Nat := 4983230072969 + 3 ^ 40 * 693023 * 2
def baseEnd_693023 : Nat := 316314580996397580466979

theorem tailTrace_693023 : CollatzResearch.WordTrace tailWord_693023 prefixEnd_693023 316314580996397580466979 := by
  unfold tailWord_693023
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276625368303504750475723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16851083578869003166983815 25276625368303504750475723)
  ·
    refine ⟨37914938052455257125713585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25276625368303504750475723 37914938052455257125713585)
    ·
      refine ⟨28436203539341442844285189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37914938052455257125713585 28436203539341442844285189)
      ·
        refine ⟨5331788163626520533303473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28436203539341442844285189 5331788163626520533303473)
        ·
          refine ⟨3998841122719890399977605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5331788163626520533303473 3998841122719890399977605)
          ·
            refine ⟨749782710509979449995801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3998841122719890399977605 749782710509979449995801)
            ·
              refine ⟨562337032882484587496851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749782710509979449995801 562337032882484587496851)
              ·
                refine ⟨843505549323726881245277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562337032882484587496851 843505549323726881245277)
                ·
                  refine ⟨316314580996397580466979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843505549323726881245277 316314580996397580466979)
                  ·
                    rfl

theorem cell20_693023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 3].length) (baseStart_693023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693023 prefixEnd_693023 := by exact prefixLift 693023
  have htrace : WordTrace (prefixWord ++ tailWord_693023) baseStart_693023 baseEnd_693023 := by
    simpa [prefixWord, tailWord_693023, baseEnd_693023] using wordTrace_append hprefix tailTrace_693023
  have hstable : (prefixWord ++ tailWord_693023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693023).length < 2 ^ (prefixWord ++ tailWord_693023).sum := by decide
  have hdescent : baseEnd_693023 < baseStart_693023 := by decide
  rcases family_descends (prefixWord ++ tailWord_693023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693041 : List Nat := [1, 2, 2, 3, 2, 1, 1, 8]
def baseStart_693041 : Nat := 118140960795 + 693041 * 2 ^ 59
def prefixEnd_693041 : Nat := 4983230072969 + 3 ^ 40 * 693041 * 2
def baseEnd_693041 : Nat := 105440932228956505955635

theorem tailTrace_693041 : CollatzResearch.WordTrace tailWord_693041 prefixEnd_693041 105440932228956505955635 := by
  unfold tailWord_693041
  simp only [CollatzResearch.WordTrace]
  refine ⟨25277281882238293824630977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16851521254825529216420651 25277281882238293824630977)
  ·
    refine ⟨18957961411678720368473233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25277281882238293824630977 18957961411678720368473233)
    ·
      refine ⟨14218471058759040276354925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18957961411678720368473233 14218471058759040276354925)
      ·
        refine ⟨5331926647034640103633097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14218471058759040276354925 5331926647034640103633097)
        ·
          refine ⟨3998944985275980077724823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5331926647034640103633097 3998944985275980077724823)
          ·
            refine ⟨5998417477913970116587235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3998944985275980077724823 5998417477913970116587235)
            ·
              refine ⟨8997626216870955174880853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998417477913970116587235 8997626216870955174880853)
              ·
                refine ⟨105440932228956505955635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8997626216870955174880853 105440932228956505955635)
                ·
                  rfl

theorem cell20_693041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_693041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693041 prefixEnd_693041 := by exact prefixLift 693041
  have htrace : WordTrace (prefixWord ++ tailWord_693041) baseStart_693041 baseEnd_693041 := by
    simpa [prefixWord, tailWord_693041, baseEnd_693041] using wordTrace_append hprefix tailTrace_693041
  have hstable : (prefixWord ++ tailWord_693041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693041).length < 2 ^ (prefixWord ++ tailWord_693041).sum := by decide
  have hdescent : baseEnd_693041 < baseStart_693041 := by decide
  rcases family_descends (prefixWord ++ tailWord_693041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693060 : List Nat := [2, 3, 4, 2, 2, 1, 2, 2, 2]
def baseStart_693060 : Nat := 118140960795 + 693060 * 2 ^ 59
def prefixEnd_693060 : Nat := 4983230072969 + 3 ^ 40 * 693060 * 2
def baseEnd_693060 : Nat := 316331468804589896233495

theorem tailTrace_693060 : CollatzResearch.WordTrace tailWord_693060 prefixEnd_693060 316331468804589896233495 := by
  unfold tailWord_693060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638987434584730034786317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16851983246112973379715089 12638987434584730034786317)
  ·
    refine ⟨4739620287969273763044869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12638987434584730034786317 4739620287969273763044869)
    ·
      refine ⟨888678803994238830570913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4739620287969273763044869 888678803994238830570913)
      ·
        refine ⟨666509102995679122928185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 888678803994238830570913 666509102995679122928185)
        ·
          refine ⟨499881827246759342196139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666509102995679122928185 499881827246759342196139)
          ·
            refine ⟨749822740870139013294209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499881827246759342196139 749822740870139013294209)
            ·
              refine ⟨562367055652604259970657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749822740870139013294209 562367055652604259970657)
              ·
                refine ⟨421775291739453194977993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562367055652604259970657 421775291739453194977993)
                ·
                  refine ⟨316331468804589896233495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421775291739453194977993 316331468804589896233495)
                  ·
                    rfl

theorem cell20_693060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_693060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693060 prefixEnd_693060 := by exact prefixLift 693060
  have htrace : WordTrace (prefixWord ++ tailWord_693060) baseStart_693060 baseEnd_693060 := by
    simpa [prefixWord, tailWord_693060, baseEnd_693060] using wordTrace_append hprefix tailTrace_693060
  have hstable : (prefixWord ++ tailWord_693060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693060).length < 2 ^ (prefixWord ++ tailWord_693060).sum := by decide
  have hdescent : baseEnd_693060 < baseStart_693060 := by decide
  rcases family_descends (prefixWord ++ tailWord_693060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693065 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 3]
def baseStart_693065 : Nat := 118140960795 + 693065 * 2 ^ 59
def prefixEnd_693065 : Nat := 4983230072969 + 3 ^ 40 * 693065 * 2
def baseEnd_693065 : Nat := 316333750940832101066807

theorem tailTrace_693065 : CollatzResearch.WordTrace tailWord_693065 prefixEnd_693065 316333750940832101066807 := by
  unfold tailWord_693065
  simp only [CollatzResearch.WordTrace]
  refine ⟨25278157234151345923504649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16852104822767563949003099 25278157234151345923504649)
  ·
    refine ⟨18958617925613509442628487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25278157234151345923504649 18958617925613509442628487)
    ·
      refine ⟨28437926888420264163942731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18958617925613509442628487 28437926888420264163942731)
      ·
        refine ⟨42656890332630396245914097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28437926888420264163942731 42656890332630396245914097)
        ·
          refine ⟨31992667749472797184435573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42656890332630396245914097 31992667749472797184435573)
          ·
            refine ⟨2999312601513074736040835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31992667749472797184435573 2999312601513074736040835)
            ·
              refine ⟨4498968902269612104061253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999312601513074736040835 4498968902269612104061253)
              ·
                refine ⟨843556669175552269511485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4498968902269612104061253 843556669175552269511485)
                ·
                  refine ⟨316333750940832101066807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843556669175552269511485 316333750940832101066807)
                  ·
                    rfl

theorem cell20_693065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_693065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693065 prefixEnd_693065 := by exact prefixLift 693065
  have htrace : WordTrace (prefixWord ++ tailWord_693065) baseStart_693065 baseEnd_693065 := by
    simpa [prefixWord, tailWord_693065, baseEnd_693065] using wordTrace_append hprefix tailTrace_693065
  have hstable : (prefixWord ++ tailWord_693065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693065).length < 2 ^ (prefixWord ++ tailWord_693065).sum := by decide
  have hdescent : baseEnd_693065 < baseStart_693065 := by decide
  rcases family_descends (prefixWord ++ tailWord_693065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693068 : List Nat := [2, 2, 1, 3, 3, 2, 1, 4, 2]
def baseStart_693068 : Nat := 118140960795 + 693068 * 2 ^ 59
def prefixEnd_693068 : Nat := 4983230072969 + 3 ^ 40 * 693068 * 2
def baseEnd_693068 : Nat := 316335120222577423966795

theorem tailTrace_693068 : CollatzResearch.WordTrace tailWord_693068 prefixEnd_693068 316335120222577423966795 := by
  unfold tailWord_693068
  simp only [CollatzResearch.WordTrace]
  refine ⟨12639133326570238717931929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16852177768760318290575905 12639133326570238717931929)
  ·
    refine ⟨9479349994927679038448947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12639133326570238717931929 9479349994927679038448947)
    ·
      refine ⟨14219024992391518557673421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9479349994927679038448947 14219024992391518557673421)
      ·
        refine ⟨5332134372146819459127533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14219024992391518557673421 5332134372146819459127533)
        ·
          refine ⟨1999550389555057297172825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5332134372146819459127533 1999550389555057297172825)
          ·
            refine ⟨1499662792166292972879619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1999550389555057297172825 1499662792166292972879619)
            ·
              refine ⟨2249494188249439459319429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499662792166292972879619 2249494188249439459319429)
              ·
                refine ⟨421780160296769898622393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2249494188249439459319429 421780160296769898622393)
                ·
                  refine ⟨316335120222577423966795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421780160296769898622393 316335120222577423966795)
                  ·
                    rfl

theorem cell20_693068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_693068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693068 prefixEnd_693068 := by exact prefixLift 693068
  have htrace : WordTrace (prefixWord ++ tailWord_693068) baseStart_693068 baseEnd_693068 := by
    simpa [prefixWord, tailWord_693068, baseEnd_693068] using wordTrace_append hprefix tailTrace_693068
  have hstable : (prefixWord ++ tailWord_693068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693068).length < 2 ^ (prefixWord ++ tailWord_693068).sum := by decide
  have hdescent : baseEnd_693068 < baseStart_693068 := by decide
  rcases family_descends (prefixWord ++ tailWord_693068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693127 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_693127 : Nat := 118140960795 + 693127 * 2 ^ 59
def prefixEnd_693127 : Nat := 4983230072969 + 3 ^ 40 * 693127 * 2
def baseEnd_693127 : Nat := 316362049430235440999887

theorem tailTrace_693127 : CollatzResearch.WordTrace tailWord_693127 prefixEnd_693127 316362049430235440999887 := by
  unfold tailWord_693127
  simp only [CollatzResearch.WordTrace]
  refine ⟨25280418559926730512261635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16853612373284487008174423 25280418559926730512261635)
  ·
    refine ⟨37920627839890095768392453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25280418559926730512261635 37920627839890095768392453)
    ·
      refine ⟨7110117719979392956573585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37920627839890095768392453 7110117719979392956573585)
      ·
        refine ⟨5332588289984544717430189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7110117719979392956573585 5332588289984544717430189)
        ·
          refine ⟨1999720608744204269036321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5332588289984544717430189 1999720608744204269036321)
          ·
            refine ⟨1499790456558153201777241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1999720608744204269036321 1499790456558153201777241)
            ·
              refine ⟨1124842842418614901332931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1499790456558153201777241 1124842842418614901332931)
              ·
                refine ⟨1687264263627922351999397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124842842418614901332931 1687264263627922351999397)
                ·
                  refine ⟨316362049430235440999887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1687264263627922351999397 316362049430235440999887)
                  ·
                    rfl

theorem cell20_693127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_693127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693127 prefixEnd_693127 := by exact prefixLift 693127
  have htrace : WordTrace (prefixWord ++ tailWord_693127) baseStart_693127 baseEnd_693127 := by
    simpa [prefixWord, tailWord_693127, baseEnd_693127] using wordTrace_append hprefix tailTrace_693127
  have hstable : (prefixWord ++ tailWord_693127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693127).length < 2 ^ (prefixWord ++ tailWord_693127).sum := by decide
  have hdescent : baseEnd_693127 < baseStart_693127 := by decide
  rcases family_descends (prefixWord ++ tailWord_693127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693151 : List Nat := [1, 1, 2, 5, 2, 3, 2, 4]
def baseStart_693151 : Nat := 118140960795 + 693151 * 2 ^ 59
def prefixEnd_693151 : Nat := 4983230072969 + 3 ^ 40 * 693151 * 2
def baseEnd_693151 : Nat := 105457667894732674733263

theorem tailTrace_693151 : CollatzResearch.WordTrace tailWord_693151 prefixEnd_693151 105457667894732674733263 := by
  unfold tailWord_693151
  simp only [CollatzResearch.WordTrace]
  refine ⟨25281293911839782611135307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16854195941226521740756871 25281293911839782611135307)
  ·
    refine ⟨37921940867759673916702961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25281293911839782611135307 37921940867759673916702961)
    ·
      refine ⟨28441455650819755437527221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37921940867759673916702961 28441455650819755437527221)
      ·
        refine ⟨2666386467264352072268177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28441455650819755437527221 2666386467264352072268177)
        ·
          refine ⟨1999789850448264054201133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2666386467264352072268177 1999789850448264054201133)
          ·
            refine ⟨749921193918099020325425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1999789850448264054201133 749921193918099020325425)
            ·
              refine ⟨562440895438574265244069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749921193918099020325425 562440895438574265244069)
              ·
                refine ⟨105457667894732674733263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 562440895438574265244069 105457667894732674733263)
                ·
                  rfl

theorem cell20_693151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_693151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693151 prefixEnd_693151 := by exact prefixLift 693151
  have htrace : WordTrace (prefixWord ++ tailWord_693151) baseStart_693151 baseEnd_693151 := by
    simpa [prefixWord, tailWord_693151, baseEnd_693151] using wordTrace_append hprefix tailTrace_693151
  have hstable : (prefixWord ++ tailWord_693151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693151).length < 2 ^ (prefixWord ++ tailWord_693151).sum := by decide
  have hdescent : baseEnd_693151 < baseStart_693151 := by decide
  rcases family_descends (prefixWord ++ tailWord_693151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693174 : List Nat := [5, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_693174 : Nat := 118140960795 + 693174 * 2 ^ 59
def prefixEnd_693174 : Nat := 4983230072969 + 3 ^ 40 * 693174 * 2
def baseEnd_693174 : Nat := 316383501510912166433029

theorem tailTrace_693174 : CollatzResearch.WordTrace tailWord_693174 prefixEnd_693174 316383501510912166433029 := by
  unfold tailWord_693174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580133299422278596201411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16854755193837638359481717 1580133299422278596201411)
  ·
    refine ⟨2370199949133417894302117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1580133299422278596201411 2370199949133417894302117)
    ·
      refine ⟨444412490462515855181647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2370199949133417894302117 444412490462515855181647)
      ·
        refine ⟨666618735693773782772471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444412490462515855181647 666618735693773782772471)
        ·
          refine ⟨999928103540660674158707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666618735693773782772471 999928103540660674158707)
          ·
            refine ⟨1499892155310991011238061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999928103540660674158707 1499892155310991011238061)
            ·
              refine ⟨562459558241621629214273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1499892155310991011238061 562459558241621629214273)
              ·
                refine ⟨421844668681216221910705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562459558241621629214273 421844668681216221910705)
                ·
                  refine ⟨316383501510912166433029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421844668681216221910705 316383501510912166433029)
                  ·
                    rfl

theorem cell20_693174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_693174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693174 prefixEnd_693174 := by exact prefixLift 693174
  have htrace : WordTrace (prefixWord ++ tailWord_693174) baseStart_693174 baseEnd_693174 := by
    simpa [prefixWord, tailWord_693174, baseEnd_693174] using wordTrace_append hprefix tailTrace_693174
  have hstable : (prefixWord ++ tailWord_693174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693174).length < 2 ^ (prefixWord ++ tailWord_693174).sum := by decide
  have hdescent : baseEnd_693174 < baseStart_693174 := by decide
  rcases family_descends (prefixWord ++ tailWord_693174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
