import V185TrunkScan18Incremental

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace H27Shared
theorem certifiedStep (a x y : Nat)
    (h : decide (CollatzResearch.ExactOddStep a x y) = true) :
    CollatzResearch.ExactOddStep a x y :=
  of_decide_eq_true h
end H27Shared

namespace V185TrunkScan19Incremental

def tailWord_4 : List Nat := [2, 3, 2, 4, 2, 1, 5]
def baseStart_4 : Nat := 118140960795 + 4 * 2 ^ 59
def prefixEnd_4 : Nat := 4983230072969 + 3 ^ 40 * 4 * 2
def baseEnd_4 : Nat := 405713130512207405

theorem tailTrace_4 : CollatzResearch.WordTrace tailWord_4 prefixEnd_4 405713130512207405 := by
  unfold tailWord_4
  simp only [CollatzResearch.WordTrace]
  refine ⟨72945996491764127533, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 97261328655685503377 72945996491764127533)
  ·
    refine ⟨27354748684411547825, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 72945996491764127533 27354748684411547825)
    ·
      refine ⟨20516061513308660869, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 27354748684411547825 20516061513308660869)
      ·
        refine ⟨3846761533745373913, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 20516061513308660869 3846761533745373913)
        ·
          refine ⟨2885071150309030435, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 3846761533745373913 2885071150309030435)
          ·
            refine ⟨4327606725463545653, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 2885071150309030435 4327606725463545653)
            ·
              refine ⟨405713130512207405, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 4327606725463545653 405713130512207405)
              ·
                rfl

theorem cell19_4_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_4 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4 prefixEnd_4 := by exact prefixLift 4
  have htrace : WordTrace (prefixWord ++ tailWord_4) baseStart_4 baseEnd_4 := by
    simpa [prefixWord, tailWord_4, baseEnd_4] using wordTrace_append hprefix tailTrace_4
  have hstable : (prefixWord ++ tailWord_4).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4).length < 2 ^ (prefixWord ++ tailWord_4).sum := by decide
  have hdescent : baseEnd_4 < baseStart_4 := by decide
  rcases family_descends (prefixWord ++ tailWord_4) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46 : List Nat := [4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_46 : Nat := 118140960795 + 46 * 2 ^ 59
def prefixEnd_46 : Nat := 4983230072969 + 3 ^ 40 * 46 * 2
def baseEnd_46 : Nat := 13997102347883688767

theorem tailTrace_46 : CollatzResearch.WordTrace tailWord_46 prefixEnd_46 13997102347883688767 := by
  unfold tailWord_46
  simp only [CollatzResearch.WordTrace]
  refine ⟨209719730103087660499, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 1118505227216467522661 209719730103087660499)
  ·
    refine ⟨314579595154631490749, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 209719730103087660499 314579595154631490749)
    ·
      refine ⟨117967348182986809031, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 314579595154631490749 117967348182986809031)
      ·
        refine ⟨176951022274480213547, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 117967348182986809031 176951022274480213547)
        ·
          refine ⟨265426533411720320321, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 176951022274480213547 265426533411720320321)
          ·
            refine ⟨199069900058790240241, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 265426533411720320321 199069900058790240241)
            ·
              refine ⟨149302425044092680181, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 199069900058790240241 149302425044092680181)
              ·
                refine ⟨13997102347883688767, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 149302425044092680181 13997102347883688767)
                ·
                  rfl

theorem cell19_46_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_46 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46 prefixEnd_46 := by exact prefixLift 46
  have htrace : WordTrace (prefixWord ++ tailWord_46) baseStart_46 baseEnd_46 := by
    simpa [prefixWord, tailWord_46, baseEnd_46] using wordTrace_append hprefix tailTrace_46
  have hstable : (prefixWord ++ tailWord_46).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46).length < 2 ^ (prefixWord ++ tailWord_46).sum := by decide
  have hdescent : baseEnd_46 < baseStart_46 := by decide
  rcases family_descends (prefixWord ++ tailWord_46) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48 : List Nat := [2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_48 : Nat := 118140960795 + 48 * 2 ^ 59
def prefixEnd_48 : Nat := 4983230072969 + 3 ^ 40 * 48 * 2
def baseEnd_48 : Nat := 14605672012471644317

theorem tailTrace_48 : CollatzResearch.WordTrace tailWord_48 prefixEnd_48 14605672012471644317 := by
  unfold tailWord_48
  simp only [CollatzResearch.WordTrace]
  refine ⟨875351916789521428399, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 1167135889052695237865 875351916789521428399)
  ·
    refine ⟨1313027875184282142599, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 875351916789521428399 1313027875184282142599)
    ·
      refine ⟨1969541812776423213899, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 1313027875184282142599 1969541812776423213899)
      ·
        refine ⟨2954312719164634820849, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 1969541812776423213899 2954312719164634820849)
        ·
          refine ⟨2215734539373476115637, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 2954312719164634820849 2215734539373476115637)
          ·
            refine ⟨207725113066263385841, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 2215734539373476115637 207725113066263385841)
            ·
              refine ⟨155793834799697539381, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 207725113066263385841 155793834799697539381)
              ·
                refine ⟨14605672012471644317, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 155793834799697539381 14605672012471644317)
                ·
                  rfl

theorem cell19_48_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_48 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48 prefixEnd_48 := by exact prefixLift 48
  have htrace : WordTrace (prefixWord ++ tailWord_48) baseStart_48 baseEnd_48 := by
    simpa [prefixWord, tailWord_48, baseEnd_48] using wordTrace_append hprefix tailTrace_48
  have hstable : (prefixWord ++ tailWord_48).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48).length < 2 ^ (prefixWord ++ tailWord_48).sum := by decide
  have hdescent : baseEnd_48 < baseStart_48 := by decide
  rcases family_descends (prefixWord ++ tailWord_48) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82 : List Nat := [3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_82 : Nat := 118140960795 + 82 * 2 ^ 59
def prefixEnd_82 : Nat := 4983230072969 + 3 ^ 40 * 82 * 2
def baseEnd_82 : Nat := 24951356310466888669

theorem tailTrace_82 : CollatzResearch.WordTrace tailWord_82 prefixEnd_82 24951356310466888669 := by
  unfold tailWord_82
  simp only [CollatzResearch.WordTrace]
  refine ⟨747696427600712398625, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 1993857140268566396333 747696427600712398625)
  ·
    refine ⟨560772320700534298969, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 747696427600712398625 560772320700534298969)
    ·
      refine ⟨420579240525400724227, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 560772320700534298969 420579240525400724227)
      ·
        refine ⟨630868860788101086341, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 420579240525400724227 630868860788101086341)
        ·
          refine ⟨118287911397768953689, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 630868860788101086341 118287911397768953689)
          ·
            refine ⟨88715933548326715267, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 118287911397768953689 88715933548326715267)
            ·
              refine ⟨133073900322490072901, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 88715933548326715267 133073900322490072901)
              ·
                refine ⟨24951356310466888669, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 133073900322490072901 24951356310466888669)
                ·
                  rfl

theorem cell19_82_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_82 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82 prefixEnd_82 := by exact prefixLift 82
  have htrace : WordTrace (prefixWord ++ tailWord_82) baseStart_82 baseEnd_82 := by
    simpa [prefixWord, tailWord_82, baseEnd_82] using wordTrace_append hprefix tailTrace_82
  have hstable : (prefixWord ++ tailWord_82).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82).length < 2 ^ (prefixWord ++ tailWord_82).sum := by decide
  have hdescent : baseEnd_82 < baseStart_82 := by decide
  rcases family_descends (prefixWord ++ tailWord_82) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103 : List Nat := [1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_103 : Nat := 118140960795 + 103 * 2 ^ 59
def prefixEnd_103 : Nat := 4983230072969 + 3 ^ 40 * 103 * 2
def baseEnd_103 : Nat := 31341337788640421945

theorem tailTrace_103 : CollatzResearch.WordTrace tailWord_103 prefixEnd_103 31341337788640421945 := by
  unfold tailWord_103
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756718634323436108963, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 2504479089548957405975 3756718634323436108963)
  ·
    refine ⟨5635077951485154163445, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 3756718634323436108963 5635077951485154163445)
    ·
      refine ⟨528288557951733202823, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 5635077951485154163445 528288557951733202823)
      ·
        refine ⟨792432836927599804235, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 528288557951733202823 792432836927599804235)
        ·
          refine ⟨1188649255391399706353, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 792432836927599804235 1188649255391399706353)
          ·
            refine ⟨891486941543549779765, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 1188649255391399706353 891486941543549779765)
            ·
              refine ⟨83576900769707791853, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 891486941543549779765 83576900769707791853)
              ·
                refine ⟨31341337788640421945, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 83576900769707791853 31341337788640421945)
                ·
                  rfl

theorem cell19_103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103 prefixEnd_103 := by exact prefixLift 103
  have htrace : WordTrace (prefixWord ++ tailWord_103) baseStart_103 baseEnd_103 := by
    simpa [prefixWord, tailWord_103, baseEnd_103] using wordTrace_append hprefix tailTrace_103
  have hstable : (prefixWord ++ tailWord_103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103).length < 2 ^ (prefixWord ++ tailWord_103).sum := by decide
  have hdescent : baseEnd_103 < baseStart_103 := by decide
  rcases family_descends (prefixWord ++ tailWord_103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124 : List Nat := [2, 2, 2, 1, 1, 5, 6]
def baseStart_124 : Nat := 118140960795 + 124 * 2 ^ 59
def prefixEnd_124 : Nat := 4983230072969 + 3 ^ 40 * 124 * 2
def baseEnd_124 : Nat := 12577106422271318407

theorem tailTrace_124 : CollatzResearch.WordTrace tailWord_124 prefixEnd_124 12577106422271318407 := by
  unfold tailWord_124
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261325779122011311713, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 3015101038829348415617 2261325779122011311713)
  ·
    refine ⟨1695994334341508483785, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 2261325779122011311713 1695994334341508483785)
    ·
      refine ⟨1271995750756131362839, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 1695994334341508483785 1271995750756131362839)
      ·
        refine ⟨1907993626134197044259, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 1271995750756131362839 1907993626134197044259)
        ·
          refine ⟨2861990439201295566389, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 1907993626134197044259 2861990439201295566389)
          ·
            refine ⟨268311603675121459349, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 2861990439201295566389 268311603675121459349)
            ·
              refine ⟨12577106422271318407, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 6 268311603675121459349 12577106422271318407)
              ·
                rfl

theorem cell19_124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124 prefixEnd_124 := by exact prefixLift 124
  have htrace : WordTrace (prefixWord ++ tailWord_124) baseStart_124 baseEnd_124 := by
    simpa [prefixWord, tailWord_124, baseEnd_124] using wordTrace_append hprefix tailTrace_124
  have hstable : (prefixWord ++ tailWord_124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124).length < 2 ^ (prefixWord ++ tailWord_124).sum := by decide
  have hdescent : baseEnd_124 < baseStart_124 := by decide
  rcases family_descends (prefixWord ++ tailWord_124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150 : List Nat := [5, 3, 2, 1, 1, 2, 2, 3]
def baseStart_150 : Nat := 118140960795 + 150 * 2 ^ 59
def prefixEnd_150 : Nat := 4983230072969 + 3 ^ 40 * 150 * 2
def baseEnd_150 : Nat := 45642724906457377373

theorem tailTrace_150 : CollatzResearch.WordTrace tailWord_150 prefixEnd_150 45642724906457377373 := by
  unfold tailWord_150
  simp only [CollatzResearch.WordTrace]
  refine ⟨341934341503153941869, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 3647299642700308713269 341934341503153941869)
  ·
    refine ⟨128225378063682728201, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 341934341503153941869 128225378063682728201)
    ·
      refine ⟨96169033547762046151, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 128225378063682728201 96169033547762046151)
      ·
        refine ⟨144253550321643069227, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 96169033547762046151 144253550321643069227)
        ·
          refine ⟨216380325482464603841, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 144253550321643069227 216380325482464603841)
          ·
            refine ⟨162285244111848452881, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 216380325482464603841 162285244111848452881)
            ·
              refine ⟨121713933083886339661, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 162285244111848452881 121713933083886339661)
              ·
                refine ⟨45642724906457377373, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 121713933083886339661 45642724906457377373)
                ·
                  rfl

theorem cell19_150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150 prefixEnd_150 := by exact prefixLift 150
  have htrace : WordTrace (prefixWord ++ tailWord_150) baseStart_150 baseEnd_150 := by
    simpa [prefixWord, tailWord_150, baseEnd_150] using wordTrace_append hprefix tailTrace_150
  have hstable : (prefixWord ++ tailWord_150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150).length < 2 ^ (prefixWord ++ tailWord_150).sum := by decide
  have hdescent : baseEnd_150 < baseStart_150 := by decide
  rcases family_descends (prefixWord ++ tailWord_150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158 : List Nat := [4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_158 : Nat := 118140960795 + 158 * 2 ^ 59
def prefixEnd_158 : Nat := 4983230072969 + 3 ^ 40 * 158 * 2
def baseEnd_158 : Nat := 48077003564809199573

theorem tailTrace_158 : CollatzResearch.WordTrace tailWord_158 prefixEnd_158 48077003564809199573 := by
  unfold tailWord_158
  simp only [CollatzResearch.WordTrace]
  refine ⟨720341679383478670141, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 3841822290045219574085 720341679383478670141)
  ·
    refine ⟨270128129768804501303, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 720341679383478670141 270128129768804501303)
    ·
      refine ⟨405192194653206751955, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 270128129768804501303 405192194653206751955)
      ·
        refine ⟨607788291979810127933, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 405192194653206751955 607788291979810127933)
        ·
          refine ⟨227920609492428797975, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 607788291979810127933 227920609492428797975)
          ·
            refine ⟨341880914238643196963, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 227920609492428797975 341880914238643196963)
            ·
              refine ⟨512821371357964795445, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 341880914238643196963 512821371357964795445)
              ·
                refine ⟨48077003564809199573, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 512821371357964795445 48077003564809199573)
                ·
                  rfl

theorem cell19_158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158 prefixEnd_158 := by exact prefixLift 158
  have htrace : WordTrace (prefixWord ++ tailWord_158) baseStart_158 baseEnd_158 := by
    simpa [prefixWord, tailWord_158, baseEnd_158] using wordTrace_append hprefix tailTrace_158
  have hstable : (prefixWord ++ tailWord_158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158).length < 2 ^ (prefixWord ++ tailWord_158).sum := by decide
  have hdescent : baseEnd_158 < baseStart_158 := by decide
  rcases family_descends (prefixWord ++ tailWord_158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160 : List Nat := [2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_160 : Nat := 118140960795 + 160 * 2 ^ 59
def prefixEnd_160 : Nat := 4983230072969 + 3 ^ 40 * 160 * 2
def baseEnd_160 : Nat := 48685573229397155123

theorem tailTrace_160 : CollatzResearch.WordTrace tailWord_160 prefixEnd_160 48685573229397155123 := by
  unfold tailWord_160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917839713911085466967, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 3890452951881447289289 2917839713911085466967)
  ·
    refine ⟨4376759570866628200451, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 2917839713911085466967 4376759570866628200451)
    ·
      refine ⟨6565139356299942300677, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 4376759570866628200451 6565139356299942300677)
      ·
        refine ⟨1230963629306239181377, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 6565139356299942300677 1230963629306239181377)
        ·
          refine ⟨923222721979679386033, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 1230963629306239181377 923222721979679386033)
          ·
            refine ⟨692417041484759539525, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 923222721979679386033 692417041484759539525)
            ·
              refine ⟨129828195278392413661, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 692417041484759539525 129828195278392413661)
              ·
                refine ⟨48685573229397155123, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 129828195278392413661 48685573229397155123)
                ·
                  rfl

theorem cell19_160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160 prefixEnd_160 := by exact prefixLift 160
  have htrace : WordTrace (prefixWord ++ tailWord_160) baseStart_160 baseEnd_160 := by
    simpa [prefixWord, tailWord_160, baseEnd_160] using wordTrace_append hprefix tailTrace_160
  have hstable : (prefixWord ++ tailWord_160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160).length < 2 ^ (prefixWord ++ tailWord_160).sum := by decide
  have hdescent : baseEnd_160 < baseStart_160 := by decide
  rcases family_descends (prefixWord ++ tailWord_160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177 : List Nat := [1, 2, 2, 5, 3, 1, 5]
def baseStart_177 : Nat := 118140960795 + 177 * 2 ^ 59
def prefixEnd_177 : Nat := 4983230072969 + 3 ^ 40 * 177 * 2
def baseEnd_177 : Nat := 17952805126131592433

theorem tailTrace_177 : CollatzResearch.WordTrace tailWord_177 prefixEnd_177 17952805126131592433 := by
  unfold tailWord_177
  simp only [CollatzResearch.WordTrace]
  refine ⟨6455720366234074302785, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 4303813577489382868523 6455720366234074302785)
  ·
    refine ⟨4841790274675555727089, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 6455720366234074302785 4841790274675555727089)
    ·
      refine ⟨3631342706006666795317, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 4841790274675555727089 3631342706006666795317)
      ·
        refine ⟨340438378688125012061, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 3631342706006666795317 340438378688125012061)
        ·
          refine ⟨127664392008046879523, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 340438378688125012061 127664392008046879523)
          ·
            refine ⟨191496588012070319285, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 127664392008046879523 191496588012070319285)
            ·
              refine ⟨17952805126131592433, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 191496588012070319285 17952805126131592433)
              ·
                rfl

theorem cell19_177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177 prefixEnd_177 := by exact prefixLift 177
  have htrace : WordTrace (prefixWord ++ tailWord_177) baseStart_177 baseEnd_177 := by
    simpa [prefixWord, tailWord_177, baseEnd_177] using wordTrace_append hprefix tailTrace_177
  have hstable : (prefixWord ++ tailWord_177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177).length < 2 ^ (prefixWord ++ tailWord_177).sum := by decide
  have hdescent : baseEnd_177 < baseStart_177 := by decide
  rcases family_descends (prefixWord ++ tailWord_177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194 : List Nat := [3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_194 : Nat := 118140960795 + 194 * 2 ^ 59
def prefixEnd_194 : Nat := 4983230072969 + 3 ^ 40 * 194 * 2
def baseEnd_194 : Nat := 59031257527392399475

theorem tailTrace_194 : CollatzResearch.WordTrace tailWord_194 prefixEnd_194 59031257527392399475 := by
  unfold tailWord_194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768940326161494417909, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 4717174203097318447757 1768940326161494417909)
  ·
    refine ⟨165838155577640101679, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 1768940326161494417909 165838155577640101679)
    ·
      refine ⟨248757233366460152519, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 165838155577640101679 248757233366460152519)
      ·
        refine ⟨373135850049690228779, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 248757233366460152519 373135850049690228779)
        ·
          refine ⟨559703775074535343169, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 373135850049690228779 559703775074535343169)
          ·
            refine ⟨419777831305901507377, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 559703775074535343169 419777831305901507377)
            ·
              refine ⟨314833373479426130533, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 419777831305901507377 314833373479426130533)
              ·
                refine ⟨59031257527392399475, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 314833373479426130533 59031257527392399475)
                ·
                  rfl

theorem cell19_194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194 prefixEnd_194 := by exact prefixLift 194
  have htrace : WordTrace (prefixWord ++ tailWord_194) baseStart_194 baseEnd_194 := by
    simpa [prefixWord, tailWord_194, baseEnd_194] using wordTrace_append hprefix tailTrace_194
  have hstable : (prefixWord ++ tailWord_194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194).length < 2 ^ (prefixWord ++ tailWord_194).sum := by decide
  have hdescent : baseEnd_194 < baseStart_194 := by decide
  rcases family_descends (prefixWord ++ tailWord_194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348 : List Nat := [2, 2, 4, 3, 1, 2, 5]
def baseStart_348 : Nat := 118140960795 + 348 * 2 ^ 59
def prefixEnd_348 : Nat := 4983230072969 + 3 ^ 40 * 348 * 2
def baseEnd_348 : Nat := 35297040566888325611

theorem tailTrace_348 : CollatzResearch.WordTrace tailWord_348 prefixEnd_348 35297040566888325611 := by
  unfold tailWord_348
  simp only [CollatzResearch.WordTrace]
  refine ⟨6346301373365139388849, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 8461735164486852518465 6346301373365139388849)
  ·
    refine ⟨4759726030023854541637, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 6346301373365139388849 4759726030023854541637)
    ·
      refine ⟨892448630629472726557, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 4759726030023854541637 892448630629472726557)
      ·
        refine ⟨334668236486052272459, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 892448630629472726557 334668236486052272459)
        ·
          refine ⟨502002354729078408689, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 334668236486052272459 502002354729078408689)
          ·
            refine ⟨376501766046808806517, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 502002354729078408689 376501766046808806517)
            ·
              refine ⟨35297040566888325611, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 376501766046808806517 35297040566888325611)
              ·
                rfl

theorem cell19_348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348 prefixEnd_348 := by exact prefixLift 348
  have htrace : WordTrace (prefixWord ++ tailWord_348) baseStart_348 baseEnd_348 := by
    simpa [prefixWord, tailWord_348, baseEnd_348] using wordTrace_append hprefix tailTrace_348
  have hstable : (prefixWord ++ tailWord_348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348).length < 2 ^ (prefixWord ++ tailWord_348).sum := by decide
  have hdescent : baseEnd_348 < baseStart_348 := by decide
  rcases family_descends (prefixWord ++ tailWord_348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424 : List Nat := [2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_424 : Nat := 118140960795 + 424 * 2 ^ 59
def prefixEnd_424 : Nat := 4983230072969 + 3 ^ 40 * 424 * 2
def baseEnd_424 : Nat := 129016768955007287737

theorem tailTrace_424 : CollatzResearch.WordTrace tailWord_424 prefixEnd_424 129016768955007287737 := by
  unfold tailWord_424
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732275235697629272163, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 10309700314263505696217 7732275235697629272163)
  ·
    refine ⟨11598412853546443908245, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 7732275235697629272163 11598412853546443908245)
    ·
      refine ⟨543675602509989558199, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 6 11598412853546443908245 543675602509989558199)
      ·
        refine ⟨815513403764984337299, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 543675602509989558199 815513403764984337299)
        ·
          refine ⟨1223270105647476505949, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 815513403764984337299 1223270105647476505949)
          ·
            refine ⟨458726289617803689731, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 1223270105647476505949 458726289617803689731)
            ·
              refine ⟨688089434426705534597, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 458726289617803689731 688089434426705534597)
              ·
                refine ⟨129016768955007287737, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 688089434426705534597 129016768955007287737)
                ·
                  rfl

theorem cell19_424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424 prefixEnd_424 := by exact prefixLift 424
  have htrace : WordTrace (prefixWord ++ tailWord_424) baseStart_424 baseEnd_424 := by
    simpa [prefixWord, tailWord_424, baseEnd_424] using wordTrace_append hprefix tailTrace_424
  have hstable : (prefixWord ++ tailWord_424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424).length < 2 ^ (prefixWord ++ tailWord_424).sum := by decide
  have hdescent : baseEnd_424 < baseStart_424 := by decide
  rcases family_descends (prefixWord ++ tailWord_424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445 : List Nat := [1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_445 : Nat := 118140960795 + 445 * 2 ^ 59
def prefixEnd_445 : Nat := 4983230072969 + 3 ^ 40 * 445 * 2
def baseEnd_445 : Nat := 135406750433180821013

theorem tailTrace_445 : CollatzResearch.WordTrace tailWord_445 prefixEnd_445 135406750433180821013 := by
  unfold tailWord_445
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230483395315845058789, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 10820322263543896705859 16230483395315845058789)
  ·
    refine ⟨3043215636621720948523, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 16230483395315845058789 3043215636621720948523)
    ·
      refine ⟨4564823454932581422785, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 3043215636621720948523 4564823454932581422785)
      ·
        refine ⟨3423617591199436067089, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 4564823454932581422785 3423617591199436067089)
        ·
          refine ⟨2567713193399577050317, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 3423617591199436067089 2567713193399577050317)
          ·
            refine ⟨962892447524841393869, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 2567713193399577050317 962892447524841393869)
            ·
              refine ⟨361084667821815522701, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 962892447524841393869 361084667821815522701)
              ·
                refine ⟨135406750433180821013, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 361084667821815522701 135406750433180821013)
                ·
                  rfl

theorem cell19_445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445 prefixEnd_445 := by exact prefixLift 445
  have htrace : WordTrace (prefixWord ++ tailWord_445) baseStart_445 baseEnd_445 := by
    simpa [prefixWord, tailWord_445, baseEnd_445] using wordTrace_append hprefix tailTrace_445
  have hstable : (prefixWord ++ tailWord_445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445).length < 2 ^ (prefixWord ++ tailWord_445).sum := by decide
  have hdescent : baseEnd_445 < baseStart_445 := by decide
  rcases family_descends (prefixWord ++ tailWord_445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498 : List Nat := [3, 2, 1, 4, 3, 1, 2, 3]
def baseStart_498 : Nat := 118140960795 + 498 * 2 ^ 59
def prefixEnd_498 : Nat := 4983230072969 + 3 ^ 40 * 498 * 2
def baseEnd_498 : Nat := 151533846544761643091

theorem tailTrace_498 : CollatzResearch.WordTrace tailWord_498 prefixEnd_498 151533846544761643091 := by
  unfold tailWord_498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540888050826474184537, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 12109034802203931158765 4540888050826474184537)
  ·
    refine ⟨3405666038119855638403, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 4540888050826474184537 3405666038119855638403)
    ·
      refine ⟨5108499057179783457605, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 3405666038119855638403 5108499057179783457605)
      ·
        refine ⟨957843573221209398301, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 4 5108499057179783457605 957843573221209398301)
        ·
          refine ⟨359191339957953524363, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 957843573221209398301 359191339957953524363)
          ·
            refine ⟨538787009936930286545, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 359191339957953524363 538787009936930286545)
            ·
              refine ⟨404090257452697714909, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 2 538787009936930286545 404090257452697714909)
              ·
                refine ⟨151533846544761643091, ?_, ?_⟩
                · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 404090257452697714909 151533846544761643091)
                ·
                  rfl

theorem cell19_498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498 prefixEnd_498 := by exact prefixLift 498
  have htrace : WordTrace (prefixWord ++ tailWord_498) baseStart_498 baseEnd_498 := by
    simpa [prefixWord, tailWord_498, baseEnd_498] using wordTrace_append hprefix tailTrace_498
  have hstable : (prefixWord ++ tailWord_498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498).length < 2 ^ (prefixWord ++ tailWord_498).sum := by decide
  have hdescent : baseEnd_498 < baseStart_498 := by decide
  rcases family_descends (prefixWord ++ tailWord_498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523 : List Nat := [1, 1, 1, 1, 7, 3, 5]
def baseStart_523 : Nat := 118140960795 + 523 * 2 ^ 59
def prefixEnd_523 : Nat := 4983230072969 + 3 ^ 40 * 523 * 2
def baseEnd_523 : Nat := 53046989117370362489

theorem tailTrace_523 : CollatzResearch.WordTrace tailWord_523 prefixEnd_523 53046989117370362489 := by
  unfold tailWord_523
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075377112735166398223, ?_, ?_⟩
  · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 12716918075156777598815 19075377112735166398223)
  ·
    refine ⟨28613065669102749597335, ?_, ?_⟩
    · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 19075377112735166398223 28613065669102749597335)
    ·
      refine ⟨42919598503654124396003, ?_, ?_⟩
      · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 28613065669102749597335 42919598503654124396003)
      ·
        refine ⟨64379397755481186594005, ?_, ?_⟩
        · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 1 42919598503654124396003 64379397755481186594005)
        ·
          refine ⟨1508892134894090310797, ?_, ?_⟩
          · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 7 64379397755481186594005 1508892134894090310797)
          ·
            refine ⟨565834550585283866549, ?_, ?_⟩
            · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 3 1508892134894090310797 565834550585283866549)
            ·
              refine ⟨53046989117370362489, ?_, ?_⟩
              · exact (H27Shared.certifiedStep _ _ _ rfl : CollatzResearch.ExactOddStep 5 565834550585283866549 53046989117370362489)
              ·
                rfl

theorem cell19_523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_523 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523 prefixEnd_523 := by exact prefixLift 523
  have htrace : WordTrace (prefixWord ++ tailWord_523) baseStart_523 baseEnd_523 := by
    simpa [prefixWord, tailWord_523, baseEnd_523] using wordTrace_append hprefix tailTrace_523
  have hstable : (prefixWord ++ tailWord_523).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523).length < 2 ^ (prefixWord ++ tailWord_523).sum := by decide
  have hdescent : baseEnd_523 < baseStart_523 := by decide
  rcases family_descends (prefixWord ++ tailWord_523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩


end V185TrunkScan19Incremental
